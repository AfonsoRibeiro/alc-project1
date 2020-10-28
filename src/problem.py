from model import *

from pysat.examples.rc2 import RC2
from pysat.formula import WCNF


class Problem:
    def __init__(self, file):
        n = int(file.readline().strip())
        self.tasks = [Task.from_line(i, file.readline()) for i in range(n)]
        self.task_map = dict()
        id = 1
        for t in self.tasks:
            t.add_deps(file.readline())
            self.task_map[t.id] = list(range(id, id + len(t.frags)))
            id += len(t.frags)

        self.frags = {
            f.id: f for f in sum(
                (t.generate_frags(
                    self.task_map) for t in self.tasks),
                list())}
        self.time_allotment = max(map(
            lambda x: x.deadline, self.tasks)) - min(map(lambda x: x.start_time, self.tasks))
        self.solver = RC2(WCNF())

    def __repr__(self):
        return '\n'.join(repr(f) for f in self.frags.values())

    def encode(self):
        def encode_atomicity(self):
            # if a frag of the task runs, then all the frags in tasks run
            # we encode this as a circular dependency
            # if frag 1 runs then frag 2 runs
            # ...
            # if frag N fruns then frag 1

            first_frag_in_task = None
            for task in self.task_map.values():
                for f1, f2 in zip([task[-1]] + task[:-1], task):
                    self.solver([-self.frags[f1].var(), self.frags[f2].var()])
