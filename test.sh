#!/usr/bin/env zsh

for input in $(ls tests/*.sms)
do
    tmpfile=.$(basename $input).out.tmp
    echo "Testing $input"
    src/solver.py < $input > $tmpfile
    echo "Produced output"
    ./proj1-checker/proj1-checker $input $tmpfile | grep 'OK!'
    echo "$input: SUCCESS"
    if [ $? -ne 0 ]
    then
        echo "Failed on test $input"
        exit -1
    fi

    diff -q <(head -n 1 $tmpfile) <(head -n 1 ${input%.sms}.out) >/dev/null
    if [ $? -ne 0 ]
    then
        echo "Failed on test $input: failed to maximize"
        exit -1
    fi

    rm $tmpfile
done
