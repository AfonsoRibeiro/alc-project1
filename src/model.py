#!/usr/bin/env python3

class Fragment:
    def __init__(self, tid, id, start, proc, deadline, deps):
        self.id = id
        self.task_id = tid
        self.start_time = start
        self.proc_time = proc
        self.deadline = deadline
        self.deps = deps

    def var(self):
        return self.id

    def start_range(self):
        return range(self.start_time, 1 + self.deadline - self.proc_time)

    def __repr__(self):
        return 'Fragment {} {{ task: {}, start: {}, proc_time: {}, deadline: {}, deps: {} }}'.format(
            self.id, self.task_id, self.start_time, self.proc_time, self.deadline, self.deps)


class Task:
    @classmethod
    def from_line(cls, lineno, line):
        line = line.strip().split()
        assert len(line) >= 5, 'Task line needs at least 5 elements (had {})\nFormat: <ri> <pi> <di> <nfrags> <frag>\nLine given: '.format(
            len(line), line)
        return cls(lineno, int(line[0]), int(line[1]), int(
            line[2]), [int(t) for t in line[4:]])

    def __init__(self, id, r, p, d, frags, deps=None):
        self.id = id
        self.start_time = r
        self.proc_time = p
        self.deadline = d

        self.frags = frags
        self.deps = deps

    def __repr__(self):
        return 'Task {} {{ start: {}, proc_time: {}, deadline: {}, fragments: {}, deps: {} }}'.format(
            self.id, self.start_time, self.proc_time, self.deadline, self.frags, self.deps)

    def add_deps(self, deps):
        if isinstance(deps, str):
            deps = [int(a) for a in deps.strip().split()]
            assert deps[0] == len(
                deps) - 1, 'Dependency format: <len> <list>\nFound: {}'.format(deps)
            deps = deps[1:]

        self.deps = deps

    def generate_frags(self, task_map):
        frags = list()
        for idx, f in enumerate(self.frags):
            start_time = self.start_time + sum(self.frags[:idx])
            proc_time = f
            deadline = self.deadline - sum(self.frags[idx + 1:])

            if idx == 0:
                deps = [task_map[d_id][-1] for d_id in self.deps]
            else:
                deps = [task_map[self.id][idx - 1]]

            frags.append(Fragment(self.id,
                                  task_map[self.id][idx],
                                  start_time,
                                  proc_time,
                                  deadline,
                                  deps))

        return frags
