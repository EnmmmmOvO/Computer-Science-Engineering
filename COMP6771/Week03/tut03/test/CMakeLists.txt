cxx_library(
   TARGET test_main
   FILENAME test_main.cpp
)
target_include_directories(test_main PUBLIC .)

cxx_test(
   TARGET lambda_string
   FILENAME "lambda_string.cpp"
)
