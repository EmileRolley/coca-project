# Assignment for the Complexité and Calculabilité course of the M1 informatique from University of Bordeaux.

> Author: Vincent Penelle (vincent.penelle@u-bordeaux.fr)

## Utilisation

To build: `make`

Alternatively, if the `make` command does not work (it might be your system is
different than mine or the one of CREMI), try the following:
- `mkdir toto`
- `cd toto`
- `cmake ..`
- `make`
This will build the project in the directory `toto` (you might change this
name). The following command will then work, except the command `make doc`,
which I do not manage to configure. `make doc` should work in the root, though.

To build the documentation: `make doc`

To launch the program: `./graphProblemSolver`

A working executable is given. It was compiled at CREMI, so it is wiser to use
it only there. To use it: `./working-graphProblemSolver`. The usage is given by
the program. You might use it to compare with your own solution (its behaviour
is only restricted to not display the generated formula by the reduction).

Two example files are given, one to manipulate the graph structure, one to
manipulate Z3, they are in the examples folder. You may play with them at your
leisure.
To build the Z3 example: `make Z3Example`
To build the graph example: `make graphParser`
(note, the make generated by cmake can also build these programs).

## Instruction

You have to implement the files EdgeConResolution.c and EdgeConReduction.c
whose prototypes are defined in EdgeConResolution.h and EdgeConReduction.h. You
should add more functions than the ones given in the latter (and document them
as in the .h -- but if you don!t need them in other files, just put the
documentation in the .c file it belongs to).

You are not allowed to modify any files outside of the EdgeConProblem folder.
If you need functions which are not present in EdgeConGraph.c, you can define
them there and add a .h file in the folder EdgeConProblem (you will only give
back this folder). But don't modify any existing function in EdgeConGraph.c.
Your program should compile at every step. If you don!t finish to code one of
the functions expected, let it return a dummy value that won!t prevent the
program to compile (and make it print that it is not done).

Some helper function to manipulate instances of the problem, and print results
are given in EdgeConGraph.h. The printing function will warn you if you print
an incorrect solution.

You will only send the EdgeConProblem folder as your solution (hence the
obligation to only modify files there).

Make your code as clean and readable as possible. To this end, you must add
auxiliary functions, and thrive to keep them short and doing a single thing.
You will be penalised if the functions BruteForceEdgeCon and/or
EdgeConReduction are not divided in smaller functions.