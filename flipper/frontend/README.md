# Flipper 

Flipper is a natural language interface for describing high level
task specifications for robots that are compiled into robot actions. It
starts with a formal core language for task planning that allows expressing
temporal specifications and uses a semantic parser to provide a natural
language interface. Flipper provides immediate visual feedback by executing an
automatically constructed plan of the task in a graphical user interface. This
allows the user to resolve potentially ambiguous interpretations. Flipper
extends itself via naturalization: users of Flipper can define new commands,
which are generalized and added as new rules to the core language, gradually
growing a more and more natural task specification language. A rule inferred from the definition of one user is available to all future users. This means that 
eventually a newcomer to Flipper won't need to know the core language at all.  


# Technical details
 - you can try out Flipper [here](http://flipper.mpi-sws.org/#/about) and check out [the paper](https://arxiv.org/abs/1803.02238)
 - the setup of the system is described [here](/voxelurn).
 - the fork of semantic parser used with flipper is available [here](https://github.com/mpi-sws-rse/sempre-interactive-flipper)
 - the system is inspired by the [Voxelurn system](https://github.com/sidaw/shrdlurn/blob/master/Voxelurn.md), that performs the same naturalization process for building in a simple world of Voxels.

