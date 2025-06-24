-- - Basics: Functional Programming in LEAN

-- - Introduction 

/-
    The functional style of programming is founded on simple, everyday
    mathematical intuitions: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions as _first-class_ values --
    i.e., values that can be passed as arguments to other functions,
    returned as results, included in data structures, etc.  The
    recognition that functions can be treated as data gives rise to a
    host of useful and powerful programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and _polymorphic
    type systems_ supporting abstraction and code reuse. LEAN offers
    all of these features.

    LEAN has been made to be performant both as a programming language
    and as a theorem prover. The first half of this chapter introduces
    the most essential functional programming primitives. The second
    half introduces some basic _tactics_ that can be used to prove
    properties of the programs that you write within LEAN.
-/


-- - Data and Functions

-- -- Enumerated Types

/- 
    One notable thing about LEAN is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), LEAN offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the LEAN distribution comes with an extensive standard
    library providing definitions of booleans, numbers, and many
    common data structures like lists and hash tables.  But there is
    nothing magic or primitive about these library definitions.  To
    illustrate this, in this course we will explicitly recapitulate
    (almost) all the definitions we need, rather than getting them
    from the standard library.
-/

-- -- Days of the Week


/-
    To see how this definition mechanism works, let's start with
    a very simple example.  The following declaration tells LEAN that
    we are defining a set of data values -- a _type_.
-/


inductive day : Type
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

/- 
    The new type is called [day], and its members are [monday],
    [tuesday], etc.

    Having defined [day], we can write functions that operate on
    days. 
-/

def next_working_day (d:day) : day :=
  match d with
  | day.monday    => day.tuesday
  | day.tuesday   => day.wednesday
  | day.wednesday => day.thursday
  | day.thursday  => day.friday
  | day.friday    => day.monday
  | day.saturday  => day.monday
  | day.sunday    => day.monday


/- 
    Note that the argument and return types of this function are
    explicitly declared here.  Like most functional programming
    languages, LEAN can often figure out these types for itself when
    they are not given explicitly -- i.e., it can do _type inference_
    -- but we'll generally include them to make reading easier. 
-/

/- 
    Having defined a function, we can check that it works on
    some examples.  There are actually three different ways to do
    examples in LEAN.  First, we can use the command [#eval] to
    evaluate a compound expression involving [next_working_day]. 
-/

#eval next_working_day day.friday 
-- ==> day.monday : day
#eval next_working_day (next_working_day day.saturday)
-- ==> tuesday : day


/- 
    Second, we can record what we _expect_ the result to be in the
    form of a LEAN example: 
-/

example : (next_working_day (next_working_day day.saturday)) = day.tuesday :=

/- 
    This declaration does two things: it makes an assertion
    (that the second working day after [saturday] is [tuesday]), and it
    gives the assertion a name that can be used to refer to it later.
    Having made the assertion, we can also ask LEAN to verify it like
    this: 
-/

  by rfl

/- 
    The details are not important just now, but essentially this
    little script can be read as "The assertion we've just made can be
    proved by observing that both sides of the equality evaluate to
    the same thing." 
-/


-- TODO: There's a bit about "Extraction" here, which doesn't make sense in the context of LEAN

-------------------------------------------------------------------

-- -- Booleans



namespace Bool

/- 
    Following the pattern of the days of the week above, we can
    define the standard type [Bool] of booleans, with members [true]
    and [false]. 
-/

inductive Bool : Type 
| true
| false

/- 
    Functions over booleans can be defined in the same way as
    above: 
-/

def Bool.not (b: Bool) : Bool :=
  match b with
  | Bool.true => Bool.false
  | Bool.false => Bool.true
  
def Bool.and (b₁: Bool) (b₂: Bool) : Bool :=
  match b₁ with
  | Bool.true => b₂
  | Bool.false => Bool.false

def Bool.or (b₁: Bool) (b₂: Bool) : Bool :=
  match b₁ with
  | Bool.true => Bool.true
  | Bool.false => b₂


/- 
    (Although we are rolling our own booleans here for the sake
    of building up everything from scratch, LEAN does, of course,
    provide a default implementation of the booleans, together with a
    multitude of useful functions and lemmas.  Whereever possible,
    we've named our own definitions and theorems to match the ones in
    the standard library.) 
-/

/- 
    The last two of these illustrate LEAN's syntax for
    multi-argument function definitions.  The corresponding
    multi-argument _application_ syntax is illustrated by the
    following "unit tests," which constitute a complete specification
    -- a truth table -- for the [Bool.or] function: 
-/

example :  (Bool.or Bool.true  Bool.false) = Bool.true :=
  by rfl
example :  (Bool.or Bool.false Bool.false) = Bool.false :=
  by rfl
example :  (Bool.or Bool.false Bool.true)  = Bool.true :=
  by rfl
example :  (Bool.or Bool.true  Bool.true)  = Bool.true :=
  by rfl
end Bool
