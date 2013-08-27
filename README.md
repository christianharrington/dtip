DTIP
====
Dependently Typed Idris Programming language

Problem statement
-----------------
The goal of this project is to gain hands-on experience with programming with dependent types, specifically through learning the Idris programming language. This will be accomplished by implementing a simple programming language in Idris. 

Dependent types can be parameterized by values, and not just other types. This allows types to be more specific, which can statically guarantee certain invariants, and reduce the number of possible errors at runtime. They can also be used in formal proofs of correctness, although formal verification is not a goal of this project.

Through this project, we aim to identify some of the challenges programmers face, when inexperienced with dependent types. Hopefully, this will lead to potential solutions, and areas for further research. We expect this project will produce generally applicable data structures that can be used when working with dependent types in Idris.

Method
------
- We will start by familiarizing ourselves with Idris, through the official Idris tutorials and documentation, and other relevant materials.
- We will implement a simple programming language in Idris, along with an interpreter, based on Edwin Brady's "Well-typed Interpreter".
- We will implement a optimization function, using dependent types to check the correctness of the optimizations.
- We will build on this simple programming language, using the general progression described in Types and Programming Languages (2002) by Benjamin Pierce. These extensions could include:
    - The Unit type
    - Ascription
    - Let bindings
    - Recursion
- We may, time permitting, implement a simple compiler and stack machine, using dependent types where applicable to reduce possible runtime errors, such as stack underflow. 

Deliverables
------------
- The source code written for this project, along with accompanying documentation.
- A report describing the process, and reflecting on the challenges we encountered.
