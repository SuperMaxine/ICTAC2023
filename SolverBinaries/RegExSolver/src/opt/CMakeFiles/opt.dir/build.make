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
CMAKE_SOURCE_DIR = /home/mku/share/tool_source/z3_mur

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/mku/tools/z3str4

# Include any dependencies generated for this target.
include src/opt/CMakeFiles/opt.dir/depend.make

# Include the progress variables for this target.
include src/opt/CMakeFiles/opt.dir/progress.make

# Include the compile flags for this target's objects.
include src/opt/CMakeFiles/opt.dir/flags.make

src/opt/opt_params.hpp: /home/mku/share/tool_source/z3_mur/scripts/pyg2hpp.py
src/opt/opt_params.hpp: /home/mku/share/tool_source/z3_mur/scripts/mk_genfile_common.py
src/opt/opt_params.hpp: /home/mku/share/tool_source/z3_mur/src/opt/opt_params.pyg
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Generating \"/home/mku/tools/z3str4/src/opt/opt_params.hpp\" from \"opt_params.pyg\""
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/python /home/mku/share/tool_source/z3_mur/scripts/pyg2hpp.py /home/mku/share/tool_source/z3_mur/src/opt/opt_params.pyg /home/mku/tools/z3str4/src/opt

src/opt/CMakeFiles/opt.dir/maxlex.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/maxlex.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/maxlex.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object src/opt/CMakeFiles/opt.dir/maxlex.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/maxlex.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/maxlex.cpp

src/opt/CMakeFiles/opt.dir/maxlex.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/maxlex.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/maxlex.cpp > CMakeFiles/opt.dir/maxlex.cpp.i

src/opt/CMakeFiles/opt.dir/maxlex.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/maxlex.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/maxlex.cpp -o CMakeFiles/opt.dir/maxlex.cpp.s

src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.requires

src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.provides: src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.provides

src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/maxlex.cpp.o


src/opt/CMakeFiles/opt.dir/maxres.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/maxres.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/maxres.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object src/opt/CMakeFiles/opt.dir/maxres.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/maxres.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/maxres.cpp

src/opt/CMakeFiles/opt.dir/maxres.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/maxres.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/maxres.cpp > CMakeFiles/opt.dir/maxres.cpp.i

src/opt/CMakeFiles/opt.dir/maxres.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/maxres.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/maxres.cpp -o CMakeFiles/opt.dir/maxres.cpp.s

src/opt/CMakeFiles/opt.dir/maxres.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/maxres.cpp.o.requires

src/opt/CMakeFiles/opt.dir/maxres.cpp.o.provides: src/opt/CMakeFiles/opt.dir/maxres.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/maxres.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/maxres.cpp.o.provides

src/opt/CMakeFiles/opt.dir/maxres.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/maxres.cpp.o


src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/maxsmt.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/maxsmt.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/maxsmt.cpp

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/maxsmt.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/maxsmt.cpp > CMakeFiles/opt.dir/maxsmt.cpp.i

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/maxsmt.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/maxsmt.cpp -o CMakeFiles/opt.dir/maxsmt.cpp.s

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.requires

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.provides: src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.provides

src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o


src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/opt_cmds.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_cmds.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/opt_cmds.cpp

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_cmds.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/opt_cmds.cpp > CMakeFiles/opt.dir/opt_cmds.cpp.i

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_cmds.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/opt_cmds.cpp -o CMakeFiles/opt.dir/opt_cmds.cpp.s

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.requires

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.provides: src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.provides

src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o


src/opt/CMakeFiles/opt.dir/opt_context.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_context.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/opt_context.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_context.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_context.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/opt_context.cpp

src/opt/CMakeFiles/opt.dir/opt_context.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_context.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/opt_context.cpp > CMakeFiles/opt.dir/opt_context.cpp.i

src/opt/CMakeFiles/opt.dir/opt_context.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_context.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/opt_context.cpp -o CMakeFiles/opt.dir/opt_context.cpp.s

src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.requires

src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.provides: src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.provides

src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/opt_context.cpp.o


src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/opt_pareto.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_pareto.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/opt_pareto.cpp

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_pareto.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/opt_pareto.cpp > CMakeFiles/opt.dir/opt_pareto.cpp.i

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_pareto.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/opt_pareto.cpp -o CMakeFiles/opt.dir/opt_pareto.cpp.s

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.requires

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.provides: src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.provides

src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o


src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/opt_parse.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_parse.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/opt_parse.cpp

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_parse.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/opt_parse.cpp > CMakeFiles/opt.dir/opt_parse.cpp.i

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_parse.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/opt_parse.cpp -o CMakeFiles/opt.dir/opt_parse.cpp.s

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.requires

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.provides: src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.provides

src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o


src/opt/CMakeFiles/opt.dir/optsmt.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/optsmt.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/optsmt.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_9) "Building CXX object src/opt/CMakeFiles/opt.dir/optsmt.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/optsmt.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/optsmt.cpp

src/opt/CMakeFiles/opt.dir/optsmt.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/optsmt.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/optsmt.cpp > CMakeFiles/opt.dir/optsmt.cpp.i

src/opt/CMakeFiles/opt.dir/optsmt.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/optsmt.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/optsmt.cpp -o CMakeFiles/opt.dir/optsmt.cpp.s

src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.requires

src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.provides: src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.provides

src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/optsmt.cpp.o


src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/opt_solver.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_10) "Building CXX object src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/opt_solver.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/opt_solver.cpp

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/opt_solver.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/opt_solver.cpp > CMakeFiles/opt.dir/opt_solver.cpp.i

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/opt_solver.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/opt_solver.cpp -o CMakeFiles/opt.dir/opt_solver.cpp.s

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.requires

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.provides: src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.provides

src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o


src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/pb_sls.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_11) "Building CXX object src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/pb_sls.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/pb_sls.cpp

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/pb_sls.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/pb_sls.cpp > CMakeFiles/opt.dir/pb_sls.cpp.i

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/pb_sls.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/pb_sls.cpp -o CMakeFiles/opt.dir/pb_sls.cpp.s

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.requires

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.provides: src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.provides

src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o


src/opt/CMakeFiles/opt.dir/sortmax.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/sortmax.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/sortmax.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_12) "Building CXX object src/opt/CMakeFiles/opt.dir/sortmax.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/sortmax.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/sortmax.cpp

src/opt/CMakeFiles/opt.dir/sortmax.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/sortmax.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/sortmax.cpp > CMakeFiles/opt.dir/sortmax.cpp.i

src/opt/CMakeFiles/opt.dir/sortmax.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/sortmax.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/sortmax.cpp -o CMakeFiles/opt.dir/sortmax.cpp.s

src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.requires

src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.provides: src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.provides

src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/sortmax.cpp.o


src/opt/CMakeFiles/opt.dir/wmax.cpp.o: src/opt/CMakeFiles/opt.dir/flags.make
src/opt/CMakeFiles/opt.dir/wmax.cpp.o: /home/mku/share/tool_source/z3_mur/src/opt/wmax.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mku/tools/z3str4/CMakeFiles --progress-num=$(CMAKE_PROGRESS_13) "Building CXX object src/opt/CMakeFiles/opt.dir/wmax.cpp.o"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/opt.dir/wmax.cpp.o -c /home/mku/share/tool_source/z3_mur/src/opt/wmax.cpp

src/opt/CMakeFiles/opt.dir/wmax.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/opt.dir/wmax.cpp.i"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mku/share/tool_source/z3_mur/src/opt/wmax.cpp > CMakeFiles/opt.dir/wmax.cpp.i

src/opt/CMakeFiles/opt.dir/wmax.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/opt.dir/wmax.cpp.s"
	cd /home/mku/tools/z3str4/src/opt && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mku/share/tool_source/z3_mur/src/opt/wmax.cpp -o CMakeFiles/opt.dir/wmax.cpp.s

src/opt/CMakeFiles/opt.dir/wmax.cpp.o.requires:

.PHONY : src/opt/CMakeFiles/opt.dir/wmax.cpp.o.requires

src/opt/CMakeFiles/opt.dir/wmax.cpp.o.provides: src/opt/CMakeFiles/opt.dir/wmax.cpp.o.requires
	$(MAKE) -f src/opt/CMakeFiles/opt.dir/build.make src/opt/CMakeFiles/opt.dir/wmax.cpp.o.provides.build
.PHONY : src/opt/CMakeFiles/opt.dir/wmax.cpp.o.provides

src/opt/CMakeFiles/opt.dir/wmax.cpp.o.provides.build: src/opt/CMakeFiles/opt.dir/wmax.cpp.o


opt: src/opt/CMakeFiles/opt.dir/maxlex.cpp.o
opt: src/opt/CMakeFiles/opt.dir/maxres.cpp.o
opt: src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_context.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o
opt: src/opt/CMakeFiles/opt.dir/optsmt.cpp.o
opt: src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o
opt: src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o
opt: src/opt/CMakeFiles/opt.dir/sortmax.cpp.o
opt: src/opt/CMakeFiles/opt.dir/wmax.cpp.o
opt: src/opt/CMakeFiles/opt.dir/build.make

.PHONY : opt

# Rule to build all files generated by this target.
src/opt/CMakeFiles/opt.dir/build: opt

.PHONY : src/opt/CMakeFiles/opt.dir/build

src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/maxlex.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/maxres.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/maxsmt.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/opt_cmds.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/opt_context.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/opt_pareto.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/opt_parse.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/optsmt.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/opt_solver.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/pb_sls.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/sortmax.cpp.o.requires
src/opt/CMakeFiles/opt.dir/requires: src/opt/CMakeFiles/opt.dir/wmax.cpp.o.requires

.PHONY : src/opt/CMakeFiles/opt.dir/requires

src/opt/CMakeFiles/opt.dir/clean:
	cd /home/mku/tools/z3str4/src/opt && $(CMAKE_COMMAND) -P CMakeFiles/opt.dir/cmake_clean.cmake
.PHONY : src/opt/CMakeFiles/opt.dir/clean

src/opt/CMakeFiles/opt.dir/depend: src/opt/opt_params.hpp
	cd /home/mku/tools/z3str4 && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/mku/share/tool_source/z3_mur /home/mku/share/tool_source/z3_mur/src/opt /home/mku/tools/z3str4 /home/mku/tools/z3str4/src/opt /home/mku/tools/z3str4/src/opt/CMakeFiles/opt.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/opt/CMakeFiles/opt.dir/depend

