# PL-2017-HW4

## Goal
The goal is to implement a static type system for the language with recursive procedures.
Read "hw4.pdf" carefully.

## Specification
- Implement the ***gen_equations*** and ***solve*** functions in the "m.ml".
- Do not modify anything in the "m.ml" except for the those two functions. (You can add additional helper functions as necessary)
- During type checking, raise the exception *TypeError* whenever type checking should fail.
  - You should use the pre-defined exception that we provided in "m.ml".
  - You can raise the exception by ```raise TypeError```.

## Compilation and Execution
Compile and execute the type checker as follows:
```
  make                   (* for compilation *)
  ./run test/example1.m  (* running the type checker *)
```

If everything is successful, you will obtain the following output:

```
= Program =
proc (f) proc (x) ((f 3) - (f x))

= Equations =
t1 = (t2 -> t3)
t3 = (t4 -> t5)
t5 = int
(t7 -> int) = t2
t7 = int
(t6 -> int) = t2
t6 = t4

= Substitution =
t4 |-> int
t6 |-> int
t7 |-> int
t2 |-> (int -> int)
t5 |-> int
t3 |-> (int -> int)
t1 |-> ((int -> int) -> (int -> int))

Type of the given program: ((int -> int) -> (int -> int))
```

## How to Submit
Submit the single file "m.ml" via Blackboard. Submissions that are not compiled properly will get zero points.
