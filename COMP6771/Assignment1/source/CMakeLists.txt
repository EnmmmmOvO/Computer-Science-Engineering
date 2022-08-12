cxx_library(TARGET word_ladder
        FILENAME word_ladder.cpp
        LINK ladder)

cxx_library(TARGET lexicon FILENAME lexicon.cpp)

cxx_library(TARGET ladder FILENAME ladder.cpp)

cxx_executable(TARGET debugging_main FILENAME debugging_main.cpp LINK word_ladder lexicon)
