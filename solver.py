#!/usr/bin/python3

def parse_input():
    def parse_task_line(rawline): # release time (ri), processing time (pi), deadline time (di), the number of fragments (ki), ki integers denoting the processing time of each fragment.
        line = rawline.split(' ')

        r = int(line[0])
        p = int(line[1])
        d = int(line[2])
        k = int(line[3])
        kp = list( map(lambda t: int(t), line[4:]) )

        print("r {} p {} d {} k {}  kp {}".format(r,p,d,k,kp))
        return 1

    def parse_dependecies_line(rawline): # e number of dependencies (mi), mi dependencies
        line = rawline.split(' ')

        m = int(line[0])
        dep = list( map(lambda t: int(t), line[1:]) )

        print("m {} dep {}".format(m, dep))
        return 1


    n = int(input())
    print(n)

    tasks = [ parse_task_line(input()) for i in range(n) ]

    task_dep = [ parse_dependecies_line(input()) for i in range(n) ]


    return 1

def solve(todo):
    return 1

if __name__ == '__main__':
    solve(parse_input())