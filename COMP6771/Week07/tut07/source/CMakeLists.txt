cxx_executable(
   TARGET instant
   FILENAME "instant.cpp"
)

cxx_library(
   TARGET stack
   FILENAME "stack.cpp"
)

cxx_executable(
   TARGET stack_use
   FILENAME "stack_use.cpp"
   LINK stack
)

cxx_executable(
   TARGET constexpr
   FILENAME "constexpr.cpp"
)
