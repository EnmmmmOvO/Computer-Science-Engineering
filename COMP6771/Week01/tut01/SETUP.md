# Setting up the environment

## Setup

### Standard Setup

To complete tutorials in this course we recommend that you use UNSW's Vlab (VNC connection to CSE machines). If you aren't familiar with Vlab then you can see some instructions to connect [here](https://cgi.cse.unsw.edu.au/~cs1511/21T1/home_computing/vlab.html).

### Local Setup

If you wish to install this environment and toolchain locally, you are welcome to do so. We have fine-tuned the process to make it easy as possible, however, you may run into platform-specific bugs that are simply not possible for us to debug. Full instructions to allow for broad (but not complete) are in SETUP_HOME.md. Install locally at your own risk, knowing that we cannot guarantee support for your installation.

## Downloading the tutorial repository

1. Connect to the CSE machine via Vlab (you can skip this step if doing this locally).
2. If you haven't already, add your ssh to gitlab (instructions in GIT.md)
3. Run `git clone gitlab@gitlab.cse.unsw.edu.au:COMP6771/22T2/students/z5555555/tut01.git` in a directory you have write and execution access to (note replace "z5555555" with your z-number).

## Installing & Configuring

These steps only needs to be completed once.

1. In your terminal, navigate to directory you have cloned the repository to.
2. Run `bash config/tools/install-vscode.sh`. This will install Visual Studio Code if it isn't already installed, and will also install all of the necessary plugins we require. Please wait for the terminal to complete it's work. Close VSCode when it's finished if it opened for you.
3. In the terminal, run `code .` (note the dot) in the tutorial directory. This opens Visual Studio (VS) Code.
4. Press _Ctrl+Shift+P_, type `CMake: Select a Kit`, and press Enter.
5. The contents of the drop-down window should be replaced with a different drop-down window.
   One of the options should say `COMP6771`. Select that one.
6. Press _Ctrl+Shift+P_, type `CMake: Configure`, and press Enter.
7. An output window should appear, detailing the configuration process.
8. Now that you've configured the project, we need to restart our editor to have our extensions pick up the new directory. Press _Ctrl+Shift+P_, type `Reload Window`, and press Enter.

## Building & Running a simple binary

### Building

1. Press _Ctrl+Shift+P_, type `CMake: Build Target`, and press Enter.
2. You should see a blank textbox. Type `hello_ex` and press Enter. This will build `source/hello.cpp`. The instruction that allows this to be built is in `source/CMakeLists.txt`.
3. An output window should appear, detailing the process.
4. You can proceed once the output window says `[build] Build finished with exit code 0`.

### Running the program

1. Your code is now compiled. In the terminal, execute `build/source/hello_ex` to run the program.

## Building & Running a simple test
### Building

1. Press _Ctrl+Shift+P_, type `CMake: Build Target`, and press Enter.
2. You should see a blank textbox. Type `hello` and press Enter. This will build `test/hello.cpp`. The instruction that allows this to be built is in `source/CMakeLists.txt`.
3. An output window should appear, detailing the process.
4. You can proceed once the output window says `[build] Build finished with exit code 0`.

### Running the program

1. Press _Ctrl+Shift+P_, type `CMake: Set Debug Target`, and press Enter.
2. A blank textbox should appear. Type `hello` again, and press Enter.
3. Press _Shift+F5_ to run the program.
4. A terminal should appear, presenting the following output.

```shell
===============================================================================
All tests passed (1 assertion in 1 test case)

```

5. Congratualtions! You've just built and run your first C++ program.

### Debugging the program

The previous section looked at running the `hello` program we'd built, but it didn't do very much at
all. We're now going to debug the program.

1. Open the file `test/hello.cpp`. You can either do this by using the side
   pane or by pressing _Ctrl+Shift+P_, typing `File: Open file`, and pressing Enter.
2. Place your mouse over line number `11` (put it right over the number 11). A red dot should appear. Move your mouse over the red dot
   and press it. This will set a breakpoint on line 11.
3. Press the play symbol with a little bug on the left-hand side of VS Code, to open the debugger
   pane.
4. Press the green play symbol. Line 11 should be highlighted, and a shape should encompass the red
   dot. This means we've started running the program and paused it at the breakpoint.
5. The debugger pane should show some new elements. The key element is the local object named
   `hello`. You should see its value, `"Hello, C++!"` next to its name.
6. That's it for now. You can either press _F5_ to continue and let the program exit normally, or
   you can press _Shift+F5_ to forcefully stop the program.

### Running the tests

We've only built, run, and debugged one program so far. The project contains functionality to
automatically run all the test cases we write, so let's get that happening.

1. Press _Ctrl+Shift+P_, type `CMake: Run Tests`, and press Enter. The output pane will show that
   any targets that we haven't already built are now being built. Once all the targets have been
   built, CMake will automatically run all of the tests for us. You should see
   `[ctest] 100% tests passed, 0 tests failed out of 2` appear toward the bottom.
2. Go to `test/hello.cpp` and change the `==` on line 11 to `!=`.
3. Rebuild your test file.
4. Press _Ctrl+Shift+P_, type `CMake: Run Tests`, and press Enter again. `hello` will be rebuilt,
   and then all the tests will be re-run. You should now see
   `50% tests passed, 1 tests failed out of 2`.
5. The output of a failed test case is always printed. Scroll up to read the failed test case's
   output. The failed test case should be also highlighted in your editor, which will come in handy
   later on.
6. Change the `!=` back to `==`, and re-run the tests. You'll notice that the only output is the
   test suite's summary, because all of the tests have passed.
