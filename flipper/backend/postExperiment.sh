#!/bin/bash

if [ -f experiments/september2018/$2/query.log ]; then
	echo "that experiment already exists"
	exit 0
fi

cp int-output/query.log experiments/september2018/workingArea/query.log
cp int-output/response.log experiments/september2018/workingArea/response.log
cp int-output/grammar.log.json experiments/september2018/workingArea/grammar.log.json
cd experiments
python3 collectQueryLogsClean.py --query_log_file=september2018/workingArea/query.log --query_response_file=september2018/workingArea/response.log --cleaned_output_file=september2018/workingArea/output.txt  --statistics_file=september2018/workingArea/statistics.csv --group=$1

mkdir september2018/$2

mv september2018/workingArea/* september2018/$2



