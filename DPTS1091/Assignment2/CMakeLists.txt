cmake_minimum_required(VERSION 3.21)
project(DPTS1091 C)

set(CMAKE_C_STANDARD 11)

include_directories(.)

add_executable(DPTS1091
        main.c
        pizzeria.c
        pizzeria.h save_string.c save_string.h)
