#!/bin/bash
#Note that this script relies on Petr4 repository being cloned in the HOL4P4 root directory.

if [ $# -eq 0 ]; then
    NTHREADS=1
else
	NTHREADS=$1
fi

#1. Check if validation_tests directory exists, if not, check if ../../petr4/examples/checker_tests/good exists
#2. Copy over all .stf files and all .p4 files with a corresponding .stf file from the petr4 subdirectory to validation_tests if needed

#3. Check if p4include exists, if not, check if ../../petr4/ci-test/p4include exists
#4. Copy over all files from the petr4 subdirectory to p4include if needed

#if [ $# -eq 3 ]; then
#	#Path to pairs of .p4 and .stf files
#    TESTS_DIR=$2
#    #Path to common P4 includes (core.p4, v1model.p4, ...)
#    INCLUDES_DIR=$3
#    #Path to skeleton files (arith-inline-skeleton.p4 and arith-skeleton.p4)
#    SKELETONS_DIR=$4
#else
#	#TODO: Use other subdirectories of expectation also? Use tests from 0.1.2 instead?
#    TESTS_DIR=../../petr4/ci-test/stf-test/expectation/passes/
#    INCLUDES_DIR=../../petr4/ci-test/p4include/
#    SKELETONS_DIR=../../petr4/ci-test/testdata/p4_16_samples/
#fi

#if ! [ -d ./validation_tests ]; then
#	if [ -d ${TESTS_DIR} ]; then
#		echo "TODO: Copy over tests from petr4."
#		cp -r ${TESTS_DIR}. ./validation_tests
#	else
#		echo "Error: petr4 installation not detected in HOL4P4 root directory. Clone the Petr4 repository in the HOL4P4 for this script to work properly."
#		exit 3
#	fi
#fi

#if ! [ -d ./p4include ]; then
#	if [ -d ${INCLUDES_DIR} ] && [ -d ${SKELETONS_DIR} ]; then
#		echo "TODO: Copy over includes from petr4."
#		cp -r ${INCLUDES_DIR}. ./p4include
#		cp ${SKELETONS_DIR}arith-inline-skeleton.p4 ./p4include
#		cp ${SKELETONS_DIR}arith-skeleton.p4 ./p4include
#	else
#		echo "Error: petr4 installation not detected in HOL4P4 root directory. Clone the Petr4 repository in the HOL4P4 for this script to work properly."
#		exit 3
#	fi
#fi

./petr4_json_export.sh validation_tests/ p4include/

./petr4_to_hol4p4_dir.sh validation_tests/ ${NTHREADS}

cd validation_tests

Holmake

cd ..
