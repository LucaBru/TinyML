# TinyML

This is the project of the course *Functional Languages*

The goal was to implement a simple version of ML language, including features like type inference and evaluator.

The type inference implemented grant the polymorphism (it was a mandatory requirement) and the basic binary operators support all the base types. Concretely the math operator *+* can be used with types *int*, *float*, *char* and *string*.

File *Typing.fs* contains all the auxillary procedures that the type inference algorithm requires and the algorithm itself.