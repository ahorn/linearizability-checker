CC=g++
CCFLAGS=-g -std=c++11

EMBB_INCLUDE=/path/to/embb/include
EMBB_BUILD=/path/to/build

TBB_INCLUDE=/path/to/tbb/include
TBB_LIB=/path/to/tbb/lib

export DYLD_LIBRARY_PATH=${EMBB_LIB}:${TBB_LIB}
export LD_LIBRARY_PATH=${EMBB_LIB}:${TBB_LIB}

tbb-test:
	${CC} ${CCFLAGS} -D_ENABLE_TBB_ -L${TBB_LIB} -I${TBB_INCLUDE} -lpthread -ltbb lt.cc -o lt-tbb-test
	./lt-tbb-test

embb-test:
	${CC} ${CCFLAGS} -D_ENABLE_EMBB_ -I${EMBB_INCLUDE} -lpthread -lrt lt.cc -o lt-embb-test ${EMBB_BUILD}/base_cpp/libembb_base_cpp.a ${EMBB_BUILD}/base_c/libembb_base_c.a ${EMBB_BUILD}/containers_cpp/libembb_containers_cpp.a
	./lt-embb-test

