# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.10

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/mku/share/tool_source/z3_TRAU

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/mku/tools/z3_TRAU

# Include any dependencies generated for this target.
include src/sat/tactic/CMakeFiles/sat_tactic.dir/depend.make

# Include the progress variables for this target.
include src/sat/tactic/CMakeFiles/sat_tactic.dir/progress.make

# Include the compile flags for this target's objects.
include src/sat/tactic/CMakeFiles/sat_tactic.dir/flags.make

src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o: src/sat/tactic/CMakeFiles/sat_tactic.dir/flags.make
src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o: /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/atom2bool_var.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3_TRAU/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o -c /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/atom2bool_var.cpp

src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.i"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/atom2bool_var.cpp > CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.i

src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.s"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/atom2bool_var.cpp -o CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.s

src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.requires:

.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.requires

src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.provides: src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.requires
	$(MAKE) -f src/sat/tactic/CMakeFiles/sat_tactic.dir/build.make src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.provides.build
.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.provides

src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.provides.build: src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o


src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o: src/sat/tactic/CMakeFiles/sat_tactic.dir/flags.make
src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o: /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/goal2sat.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3_TRAU/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/sat_tactic.dir/goal2sat.cpp.o -c /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/goal2sat.cpp

src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/sat_tactic.dir/goal2sat.cpp.i"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/goal2sat.cpp > CMakeFiles/sat_tactic.dir/goal2sat.cpp.i

src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/sat_tactic.dir/goal2sat.cpp.s"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/goal2sat.cpp -o CMakeFiles/sat_tactic.dir/goal2sat.cpp.s

src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.requires:

.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.requires

src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.provides: src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.requires
	$(MAKE) -f src/sat/tactic/CMakeFiles/sat_tactic.dir/build.make src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.provides.build
.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.provides

src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.provides.build: src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o


src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o: src/sat/tactic/CMakeFiles/sat_tactic.dir/flags.make
src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o: /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/sat_tactic.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3_TRAU/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o -c /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/sat_tactic.cpp

src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/sat_tactic.dir/sat_tactic.cpp.i"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/sat_tactic.cpp > CMakeFiles/sat_tactic.dir/sat_tactic.cpp.i

src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/sat_tactic.dir/sat_tactic.cpp.s"
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_TRAU/src/sat/tactic/sat_tactic.cpp -o CMakeFiles/sat_tactic.dir/sat_tactic.cpp.s

src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.requires:

.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.requires

src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.provides: src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.requires
	$(MAKE) -f src/sat/tactic/CMakeFiles/sat_tactic.dir/build.make src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.provides.build
.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.provides

src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.provides.build: src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o


sat_tactic: src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o
sat_tactic: src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o
sat_tactic: src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o
sat_tactic: src/sat/tactic/CMakeFiles/sat_tactic.dir/build.make

.PHONY : sat_tactic

# Rule to build all files generated by this target.
src/sat/tactic/CMakeFiles/sat_tactic.dir/build: sat_tactic

.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/build

src/sat/tactic/CMakeFiles/sat_tactic.dir/requires: src/sat/tactic/CMakeFiles/sat_tactic.dir/atom2bool_var.cpp.o.requires
src/sat/tactic/CMakeFiles/sat_tactic.dir/requires: src/sat/tactic/CMakeFiles/sat_tactic.dir/goal2sat.cpp.o.requires
src/sat/tactic/CMakeFiles/sat_tactic.dir/requires: src/sat/tactic/CMakeFiles/sat_tactic.dir/sat_tactic.cpp.o.requires

.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/requires

src/sat/tactic/CMakeFiles/sat_tactic.dir/clean:
	cd /home/mku/tools/z3_TRAU/src/sat/tactic && $(CMAKE_COMMAND) -P CMakeFiles/sat_tactic.dir/cmake_clean.cmake
.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/clean

src/sat/tactic/CMakeFiles/sat_tactic.dir/depend:
	cd /home/mku/tools/z3_TRAU && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/mku/share/tool_source/z3_TRAU /home/mku/share/tool_source/z3_TRAU/src/sat/tactic /home/mku/tools/z3_TRAU /home/mku/tools/z3_TRAU/src/sat/tactic /home/mku/tools/z3_TRAU/src/sat/tactic/CMakeFiles/sat_tactic.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/sat/tactic/CMakeFiles/sat_tactic.dir/depend

