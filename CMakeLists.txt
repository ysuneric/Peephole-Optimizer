cmake_minimum_required(VERSION 3.5)
project(joos)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_FLAGS "-Wall -ansi -pedantic -g")

file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/src)

include_directories(${PROJECT_SOURCE_DIR}/JOOSA-src)
include_directories(${CMAKE_CURRENT_BINARY_DIR}/src)

find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

BISON_TARGET(
        Parser ${PROJECT_SOURCE_DIR}/JOOSA-src/joos.y
        ${CMAKE_CURRENT_BINARY_DIR}/src/y.tab.h
        COMPILE_FLAGS "-y -d"
        DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/JOOSA-src/y.tab.c
)
FLEX_TARGET(
        Scanner ${PROJECT_SOURCE_DIR}/JOOSA-src/joos.l
        ${CMAKE_CURRENT_BINARY_DIR}/src/lex.yy.c
)
ADD_FLEX_BISON_DEPENDENCY(Scanner Parser)

set(EXECUTABLE_OUTPUT_PATH ${PROJECT_SOURCE_DIR}/JOOSA-src)

add_executable(
        ${PROJECT_NAME}
        JOOSA-src/main.c
        JOOSA-src/code.c
        JOOSA-src/weed.c
        JOOSA-src/defasn.c
        JOOSA-src/emit.c
        JOOSA-src/error.c
        JOOSA-src/memory.c
        JOOSA-src/optimize.c
        JOOSA-src/resource.c
        JOOSA-src/patterns.h
        JOOSA-src/type.c
        JOOSA-src/tree.c
        ${BISON_Parser_OUTPUTS}
        ${FLEX_Scanner_OUTPUTS}
)
target_link_libraries( ${PROJECT_NAME} ${FLEX_LIBRARIES})
