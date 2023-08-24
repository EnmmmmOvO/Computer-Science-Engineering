proctype P() {
  printf("Hello world, I am process %d!", _pid);
}

init { run P(); run P() }
