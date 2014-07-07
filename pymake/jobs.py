from __future__ import print_function

import os, sys, site, traceback, multiprocessing
# XXXkhuey Work around http://bugs.python.org/issue1731717
import subprocess
subprocess._cleanup = lambda: None
from collections import deque

from pymake.builtins import PythonException


class Job(object):
    """
    A single job to be executed on the process pool.
    """
    done = False # set to true when the job completes

    def __init__(self):
        self.exitcode = -127

    def notify(self, condition, result):
        condition.acquire()
        self.done = True
        self.exitcode = result
        condition.notify()
        condition.release()

    def get_callback(self, condition):
        return lambda result: self.notify(condition, result)

class PopenJob(Job):
    """
    A job that executes a command using subprocess.Popen.
    """
    def __init__(self, argv, executable, shell, env, cwd):
        Job.__init__(self)
        self.argv = argv
        self.executable = executable
        self.shell = shell
        self.env = env
        self.cwd = cwd
        self.parentpid = os.getpid()

    def run(self):
        assert os.getpid() != self.parentpid
        # subprocess.Popen doesn't use the PATH set in the env argument for
        # finding the executable on some platforms (but strangely it does on
        # others!), so set os.environ['PATH'] explicitly. This is parallel-
        # safe because pymake uses separate processes for parallelism, and
        # each process is serial. See http://bugs.python.org/issue8557 for a
        # general overview of "subprocess PATH semantics and portability".
        oldpath = os.environ['PATH']
        try:
            if self.env is not None and self.env.has_key('PATH'):
                os.environ['PATH'] = self.env['PATH']
            p = subprocess.Popen(self.argv, executable=self.executable, shell=self.shell, env=self.env, cwd=self.cwd)
            return p.wait()
        except OSError as e:
            print(e, file=sys.stderr)
            return -127
        finally:
            os.environ['PATH'] = oldpath


class PythonJob(Job):
    """
    A job that calls a Python method.
    """
    def __init__(self, module, method, argv, env, cwd, pycommandpath=None):
        self.module = module
        self.method = method
        self.argv = argv
        self.env = env
        self.cwd = cwd
        self.pycommandpath = pycommandpath or []
        self.parentpid = os.getpid()

    def run(self):
        assert os.getpid() != self.parentpid
        # os.environ is a magic dictionary. Setting it to something else
        # doesn't affect the environment of subprocesses, so use clear/update
        oldenv = dict(os.environ)

        # sys.path is adjusted for the entire lifetime of the command
        # execution. This ensures any delayed imports will still work.
        oldsyspath = list(sys.path)
        try:
            os.chdir(self.cwd)
            os.environ.clear()
            os.environ.update(self.env)

            sys.path = []
            for p in sys.path + self.pycommandpath:
                site.addsitedir(p)
            sys.path.extend(oldsyspath)

            if self.module not in sys.modules:
                try:
                    __import__(self.module)
                except Exception as e:
                    print('Error importing %s: %s' % (
                        self.module, e), file=sys.stderr)
                    return -127

            m = sys.modules[self.module]
            if self.method not in m.__dict__:
                print("No method named '%s' in module %s" % (self.method, self.module), file=sys.stderr)
                return -127
            rv = m.__dict__[self.method](self.argv)
            if rv != 0 and rv is not None:
                print((
                    "Native command '%s %s' returned value '%s'" %
                    (self.module, self.method, rv)), file=sys.stderr)
                return (rv if isinstance(rv, int) else 1)

        except PythonException as e:
            print(e, file=sys.stderr)
            return e.exitcode
        except:
            e = sys.exc_info()[1]
            if isinstance(e, SystemExit) and (e.code == 0 or e.code is None):
                pass # sys.exit(0) is not a failure
            else:
                print(e, file=sys.stderr)
                traceback.print_exc()
                return -127
        finally:
            os.environ.clear()
            os.environ.update(oldenv)
            sys.path = oldsyspath
            # multiprocessing exits via os._exit, make sure that all output
            # from command gets written out before that happens.
            sys.stdout.flush()
            sys.stderr.flush()

        return 0

def job_runner(job):
    """
    Run a job. Called in a Process pool.
    """
    return job.run()

class ParallelContext(object):
    """
    Manages the parallel execution of processes.
    """

    _allcontexts = set()
    _condition = multiprocessing.Condition()

    def __init__(self, jcount):
        self.jcount = jcount
        self.exit = False

        self.processpool = multiprocessing.Pool(processes=jcount)
        self.pending = deque() # deque of (cb, args, kwargs)
        self.running = [] # list of (subprocess, cb)

        self._allcontexts.add(self)

    def finish(self):
        assert len(self.pending) == 0 and len(self.running) == 0, "pending: %i running: %i" % (len(self.pending), len(self.running))
        self.processpool.close()
        self.processpool.join()
        self._allcontexts.remove(self)

    def run(self):
        while len(self.pending) and len(self.running) < self.jcount:
            cb, args, kwargs = self.pending.popleft()
            cb(*args, **kwargs)

    def defer(self, cb, *args, **kwargs):
        assert self.jcount > 1 or not len(self.pending), "Serial execution error defering %r %r %r: currently pending %r" % (cb, args, kwargs, self.pending)
        self.pending.append((cb, args, kwargs))

    def _docall_generic(self, pool, job, cb, echo, justprint):
        if echo is not None:
            print(echo)
        processcb = job.get_callback(ParallelContext._condition)
        if justprint:
            processcb(0)
        else:
            pool.apply_async(job_runner, args=(job,), callback=processcb)
        self.running.append((job, cb))

    def call(self, argv, shell, env, cwd, cb, echo, justprint=False, executable=None):
        """
        Asynchronously call the process
        """

        job = PopenJob(argv, executable=executable, shell=shell, env=env, cwd=cwd)
        self.defer(self._docall_generic, self.processpool, job, cb, echo, justprint)

    def call_native(self, module, method, argv, env, cwd, cb,
                    echo, justprint=False, pycommandpath=None):
        """
        Asynchronously call the native function
        """

        job = PythonJob(module, method, argv, env, cwd, pycommandpath)
        self.defer(self._docall_generic, self.processpool, job, cb, echo, justprint)

    @staticmethod
    def _waitany(condition):
        def _checkdone():
            jobs = []
            for c in ParallelContext._allcontexts:
                for i in range(0, len(c.running)):
                    if c.running[i][0].done:
                        jobs.append(c.running[i])
                for j in jobs:
                    if j in c.running:
                        c.running.remove(j)
            return jobs

        # We must acquire the lock, and then check to see if any jobs have
        # finished.  If we don't check after acquiring the lock it's possible
        # that all outstanding jobs will have completed before we wait and we'll
        # wait for notifications that have already occurred.
        condition.acquire()
        jobs = _checkdone()

        if jobs == []:
            condition.wait()
            jobs = _checkdone()

        condition.release()

        return jobs
        
    @staticmethod
    def spin():
        """
        Spin the 'event loop', and never return.
        """

        while True:
            clist = list(ParallelContext._allcontexts)
            for c in clist:
                c.run()

            dowait = any((len(c.running) for c in ParallelContext._allcontexts))
            if dowait:
                # Wait on local jobs first for perf
                for job, cb in ParallelContext._waitany(ParallelContext._condition):
                    cb(job.exitcode)
            else:
                assert any(len(c.pending) for c in ParallelContext._allcontexts)

def makedeferrable(usercb, **userkwargs):
    def cb(*args, **kwargs):
        kwargs.update(userkwargs)
        return usercb(*args, **kwargs)

    return cb

_serialContext = None
_parallelContext = None

def getcontext(jcount):
    global _serialContext, _parallelContext
    if jcount == 1:
        if _serialContext is None:
            _serialContext = ParallelContext(1)
        return _serialContext
    else:
        if _parallelContext is None:
            _parallelContext = ParallelContext(jcount)
        return _parallelContext

