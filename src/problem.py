from model import *

from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

class Problem:
    def __init__(self, file):
        n = int(file.readline().strip())
        self.tasks = [Task.from_line(i, file.readline()) for i in range(1, n+1)]
        self.task_map = dict()
        id = 1
        for t in self.tasks:
            t.add_deps(file.readline())
            self.task_map[t.id] = list(range(id, id + len(t.frags)))
            id += len(t.frags)

        #self._transitive_task_closure()

        self.frags = {
            f.id: f for f in sum(
                (t.generate_frags(
                    self.task_map) for t in self.tasks),
                list())}

        #self._transitive_dep_closure()

        self.begin_time = min(map(lambda x: x.start_time, self.tasks))
        self.end_time = max(map(lambda x: x.deadline, self.tasks))

        self.min_starts = len(self.frags) + 1 + (self.end_time - self.begin_time)
        self.max_starts = len(self.frags) + 1 + max(self.frags.keys()) * (self.end_time - self.begin_time) + (self.end_time - 1 - self.begin_time)
        self.solver = RC2(WCNF(), exhaust=True)

    def __repr__(self):
        return '\n'.join(repr(f) for f in self.frags.values())

    def _transitive_task_closure(self):
        # private method
        # finds the transitive closure of dependencies
        # ie: if T1 depends on T2 and T2 depends on T3, add a dependency from T1 to T3
        #
        deps = dict()
        def find_deps(t):
            if t in deps: return deps[t]
            ideps = sum(map(lambda x: find_deps(self.tasks[x - 1]), t.deps), t.deps)
            deps[t] = ideps
            return deps[t]

        for t in self.tasks:
            t.deps = find_deps(t)

    def _transitive_dep_closure(self):
        # private method
        # finds the transitive closure of dependencies
        # ie: if F1 depends on F2 and F2 depends on F3, add a dependency from F1 to F3
        #
        deps = dict()
        def find_deps(i):
            if i in deps: return deps[i]
            ideps = sum(map(lambda x: find_deps(x), self.frags[i].deps), self.frags[i].deps)
            deps[i] = ideps
            return deps[i]

        for i, f in self.frags.items():
            f.deps = find_deps(i)

    def time_range(self):
        return range(self.begin_time, self.end_time)

    def start(self, i, t):
        # relationship: fragment starts running at some time
        # i is the frag number
        # t is the time
        #
        # variable SAT variable slots
        # [1, len(frags)]: whether fragment ID runs
        # [len(frags)+1, len(frags)+1 + max_time * len(frags)]
        assert i in self.frags
        assert t in self.frags[i].start_range()
        base = self.end_time - self.begin_time
        return len(self.frags) + 1 + i * base + (t - self.begin_time)

    def encode(self):
        def encode_atomicity(self):
            # if a frag of the task runs, then all the frags in tasks run
            # we encode this as a circular dependency
            # if frag 1 runs then frag 2 runs
            # ...
            # if frag N fruns then frag 1

            for task in self.task_map.values():
                for f1, f2 in zip([task[-1]] + task[:-1], task):
                    self.solver.add_clause([-f1, f2])

        def encode_start(self):
            for i, frag in self.frags.items():
                # if a frag runs, it starts at some (valid) point
                self.solver.add_clause([-i] + [self.start(i, t) for t in frag.start_range()])

                for t in frag.start_range():
                    # if a frag starts, it runs
                    self.solver.add_clause([-self.start(i, t), i])

                    for p in range(frag.proc_time):
                        for i2 in filter(lambda k: k != i, self.frags):
                            if t + p in self.frags[i2].start_range():
                                self.solver.add_clause([-self.start(i, t), -self.start(i2, t + p)])

        def encode_dependencies(self):
            for i, frag in self.frags.items():
                for dep in map(lambda i: self.frags[i], frag.deps):
                    for t in frag.start_range():
                        self.solver.add_clause([-self.start(i, t)] + [self.start(dep.id, tdep) for tdep in dep.start_range() if tdep < t])
                        #self.solver.add_clause([-self.start(i, t)] + [self.start(dep.id, tdep) for tdep in dep.start_range() if tdep + dep.proc_time <= t])
                    #for tdep in dep.start_range():
                     #   self.solver.add_clause([-self.start(dep.id, tdep), -i] + [self.start(i, t) for t in frag.start_range() if tdep + dep.proc_time <= t])


        def encode_soft_clauses(self):
            # the soft clauses are based on the first fragment of each task
            # if that fragment runs then the task itself runs

            for t, frag_list in self.task_map.items():
                self.solver.add_clause([frag_list[0]], weight=1)

        # atomicity of tasks
        encode_atomicity(self)

        # start relationship
        encode_start(self)

        # fragment dependencies
        encode_dependencies(self)

        # soft clauses: try to maximize the number of tasks
        encode_soft_clauses(self)

    def compute(self):
        # get a model
        assert self.solver.compute(), 'UNSAT'
        return self.solver.model, self.solver.cost

    def disallow_current_model(self):
        self.solver.add_clause([-v for v in filter(lambda x: x in self.frags or -x in self.frags, self.solver.model)])

    def interpret(self):
        def reverse_starts(v):
            norm = v - len(self.frags) - 1
            base = self.end_time - self.begin_time
            return norm // base, norm % base + self.begin_time

        task_running = { t: [False for _ in self.task_map] for t in range(self.begin_time, self.end_time)}
        frag_running = { t: [False for _ in self.frags] for t in range(self.begin_time, self.end_time)}
        for frag, time in map(reverse_starts, filter(lambda x: x in range(self.min_starts, self.max_starts + 1), self.solver.model)):
            for t in range(time, time+self.frags[frag].proc_time):
                frag_running[t][frag - 1] = True
                task_running[t][self.frags[frag].task_id - 1] = True

        print('Tasks completed: {}'.format(len(self.tasks) - self.solver.cost))
        print('{:>10s}\t{}'.format('Fragment', '\t'.join('{:^4d}'.format(f) for f in self.frags)))
        for t in range(self.begin_time, self.end_time):
            print('{:>10d}\t{}'.format(t, '\t'.join('{:^4s}'.format('x' if frag_running[t][frag-1] in self.solver.model else '') for frag in self.frags)))

        print()
        print('{:>10s}\t{}'.format('Task', '\t'.join('{:^4d}'.format(t) for t in self.task_map)))
        for t in range(self.begin_time, self.end_time):
            print('{:>10d}\t{}'.format(t, '\t'.join('{:^4s}'.format('x' if task_running[t][task-1] in self.solver.model else '') for task in self.task_map)))

    def solve(self):
        def reverse_starts(v):
            norm = v - len(self.frags) - 1
            base = self.end_time - self.begin_time
            return norm // base, norm % base + self.begin_time

        self.compute()
        starts_map = {frag: time for frag, time in map(reverse_starts, filter(lambda x: x in range(self.min_starts, self.max_starts + 1), self.solver.model))}
        print(len(self.tasks) - self.solver.cost)
        for task, frags in self.task_map.items():
            start_times = [starts_map[f] for f in frags if f in starts_map]
            if len(start_times) > 0:
                print('{} {}'.format(task, ' '.join(str(i) for i in start_times)))

if __name__ == '__main__':
    s = Problem(open('../tests/test1.sms'))
    print(s)
    s.encode()
    s.compute()
    #s.interpret()
    s.solve()
