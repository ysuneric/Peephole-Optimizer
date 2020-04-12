#!/usr/bin/env bash

#!/bin/bash

echo -e "\033[93m"
echo "  Building Compiler"
echo "====================================="
echo -e -n "\033[0m"

make -C JOOSA-src
if [ $? != 0 ]
then
	echo -e "\x1B[41m\033[1mError:\033[0m\x1B[41m Unable to compile patterns file\x1B[0m"
	exit
fi

rm -f PeepholeBenchmarks/bench*/*.*dump

COUNT=0
COUNT_COMPILED=0

for BENCH_DIR in PeepholeBenchmarks/*/
do
	((COUNT++))

	BENCH=$(basename $BENCH_DIR)
	echo -e "\033[93m"
	echo "  Generating Bytecode for '$BENCH'"
	echo "====================================="
	echo -e -n "\033[0m"

	echo -e -n "\033[92m"
	echo "  Normal"
	echo "----------------"
	echo -e -n "\033[0m"

	PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR clean

	PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR

	if [ $? != 0 ]
	then
		echo
		echo -e "\x1B[41m\033[1mError:\033[0m\x1B[41m Unable to compile benchmark '$BENCH'\x1B[0m"
		exit
	fi

	echo -e "\033[92m"
	echo "  Optimized"
	echo "----------------"
	echo -e -n "\033[0m"

	PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR opt

	if [ $? != 0 ]
	then
		echo
		echo -e "\x1B[41m\033[1mError:\033[0m\x1B[41m Unable to optimize benchmark '$BENCH'\x1B[0m"
		exit
	fi

	echo -e "\033[92m"
	echo "  Execution"
	echo "----------------"
	echo -e -n "\033[0m"

	RESULT=$(PEEPDIR=`pwd` make -s --no-print-directory -C $BENCH_DIR run)
	EXPECTED=$(cat $BENCH_DIR/out1)

	if [[ "$RESULT" == "$EXPECTED" ]]
	then
		echo -e "\x1B[42mExecution Successful\x1B[0m"
	else
		echo $EXPECTED
		echo
		echo $RESULT
		echo -e "\x1B[41mExecution Failed\x1B[0m"
		continue
	fi

	echo -e "\033[92m"
	echo "  Bytecode Size"
	echo "----------------"
	echo -e -n "\033[0m"

	NORMAL=$(grep -a code_length $BENCH_DIR*.dump | awk '{sum += $3} END {print sum}')
	OPT=$(grep -a code_length $BENCH_DIR*.optdump | awk '{sum += $3} END {print sum}')

	if [[ -z "$NORMAL" || -z "$OPT" ]]
	then
		echo -e "\x1B[41m\033[1mError:\033[0m\x1B[41m Unable to load bytecode statistics\x1B[0m"
		continue
	fi

	((COUNT_COMPILED++))

	echo -e "\x1B[42m\033[1mNormal:\033[0m\x1B[42m $NORMAL\x1B[49m"
	echo -e "\x1B[42m\033[1mOptimized:\033[0m\x1B[42m $OPT\x1B[49m"
done

echo -e "\033[93m"
echo "  Overall Bytecode Size"
echo "====================================="
echo -e -n "\033[0m"

if [ $COUNT == $COUNT_COMPILED ]
then
	echo -e "\x1B[42mSuccessfully compiled all benchmarks\x1B[49m"
else
	echo -e "\x1B[41mError: Compiled $COUNT_COMPILED/$COUNT benchmarks\x1B[49m"
	exit 1
fi
echo

NORMAL=$(grep -a code_length PeepholeBenchmarks/bench*/*.dump | awk '{sum += $3} END {print sum}')
OPT=$(grep -a code_length PeepholeBenchmarks/bench*/*.optdump | awk '{sum += $3} END {print sum}')

if [[ -z "$NORMAL" || -z "$OPT" ]]
then
	echo -e "\x1B[41m\033[1mError:\033[0m\x1B[41m Unable to load bytecode statistics\x1B[0m"
	exit
fi

echo -e "\x1B[42m\033[1mNormal:\033[0m\x1B[42m $NORMAL\x1B[49m"
echo -e "\x1B[42m\033[1mOptimized:\033[0m\x1B[42m $OPT\x1B[49m"
