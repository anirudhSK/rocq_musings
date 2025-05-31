Interpreter style:

Pros:
Defining things in terms of an interpreter is very concrete and executable.
Can run Compute.

Cons:
By default every Rocq program has to terminate.
What if the programming language allows you to diverge?
And is Turing complete?
You can bound it using a number N.

Inductive relations style:

Dual of the interpreter style

Pros:
Very easy to specify as a state transition something that doesn't necessarily terminate.
You just define one step.
If e evals to v, then c(e) evals to c(v).
You can do induction on the case by case stepping of e to v.

Cons:
Can't execute this, can't run Compute.
The inductive relations style is much more straightforward for pen and paper proofs.

