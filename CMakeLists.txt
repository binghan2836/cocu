
CMAKE_MINIMUM_REQUIRED(VERSION 2.8)


PROJECT(COCU)

IF (CMAKE_SYSTEM_NAME MATCHES "Linux")
    MESSAGE(STATUS "current platform: Linux ")
    #ADD_DEFINITIONS(${CMAKE_CXX_FLAGS} "$ENV{CXXFLAGS} -Wall -pthread -DGTEST_HAS_PTHREAD=1 -std=c++11")
    SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -pthread -DGTEST_HAS_PTHREAD=1 -std=c++11")
ELSE ()
    MESSAGE(STATUS "other platform: ${CMAKE_SYSTEM_NAME}")
ENDIF (CMAKE_SYSTEM_NAME MATCHES "Linux")

SET (LIBRARY_OUTPUT_PATH ${PROJECT_SOURCE_DIR}/out/lib/)
SET (EXECUTABLE_OUTPUT_PATH ${PROJECT_SOURCE_DIR}/out/bin/)


configure_file (
  "${PROJECT_SOURCE_DIR}/includes/config.h.in"
  "${CMAKE_CURRENT_BINARY_DIR}/includes/config.h"
  )
option(OUTPUT2CONSOLE "write log to console" ON)

INCLUDE_DIRECTORIES(
	./third_parts/googletest/googletest/include/
	./third_parts/googletest/googlemock/include/
  ./third_parts/libevent/include/
  ${CMAKE_BINARY_DIR}/third_parts/libevent/include/
  ${CMAKE_CURRENT_BINARY_DIR}/includes/
	./includes/
)

ADD_SUBDIRECTORY(third_parts/googletest/)
ADD_SUBDIRECTORY(third_parts/libevent/)
#ADD_SUBDIRECTORY(src)
ADD_SUBDIRECTORY(tests)
