#!/usr/bin/env zsh

for input in $(ls tests/*.sms)
do
    grep $input $1 | awk '{ sum += $2; n++; } END { if (n > 0) print "'$input'\t", sum/n }'
done
