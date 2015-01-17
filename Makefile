CC=g++
TBB_LIB=/path/to/tbb/release
TBB_INCLUDE=/path/to/tbb/include

export DYLD_LIBRARY_PATH=${TBB_LIB}

test:
	${CC} -g -std=c++11 -L${TBB_LIB} -I${TBB_INCLUDE} -ltbb lt.cc -o lt-test
	./lt-test
