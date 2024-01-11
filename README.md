# Hooo
Propositional logic with exponentials

To install Hooo, type:

```text
cargo install --example hooo hooo
```

Then, to check a file with Hooo, type:

```text
hooo <file.hooo>
```

### Example: Absurd

```text
fn absurd : false -> a {
    x : false;
    let r = match x : a;
    return r;
}
```

### Working with projects

To check a whole project, type:

```text
hooo <project directory>
```

Hooo will generate a "Hooo.config" file, which you can modify to use other libraries:

```text
dependencies {
    path("../my_library");
}
```

By default, Hooo adds a "std" library which you can use in the following way:

```text
use std::not_double;
```

This will add a term `not_double : a -> !!a`.

Hooo generates a file "hooo-meta_cache.bin" that stores data to make repeated checks faster.
This will usually just take a few MB of storage.
If you want a clean check, then delete this file.

## Introduction to Hooo

Intuitionistic Propositional Logic (IPL) is the most important mathematical language
in the world, because it is the foundation for constructive logic and many type systems.

Usually, IPL is thought of as a "simple language" that is generalized in various ways.
For example, by adding predicates, one gets First Order Logic.

Previously, IPL was thought of as "complete" in the sense that it can derive every
formula that is true about propositions.
To reason about IPL at meta-level, mathematicians relied on some meta-language (e.g. Sequent Calculus)
or some modal logic.

For example, in Provability Logic, `□(a => b)` is introduced by proving `⊢ a => b` in Sequent Calculus.

Recently, I discovered that, while logical implication (`=>`) in IPL corresponds to lambda/closures,
there is no possible way to express the analogue of function pointers (`->`).
People thought previously that, since logical implication is a kind of exponential object,
that IPL covered exponentials in the sense of Category Theory.
However, there can be more than one kind of exponential!
The extension of IPL to include function pointers is called "exponential propositions".

Exponential propositions allows a unification of the meta-language of IPL with its object-language.
This means that IPL in its previous form is "incomplete", in the sense that there are no ways
to express exponential propositions.

Hooo finalizes intuitionistic logic by introducing exponential propositions (HOOO EP).
This solves the previous problems of using a separate meta-language.
Inference rules in Hooo are first-class citizens.

There is no separation between the language and meta-language in Hooo.
All types, including rules, are constructive propositions.

### Relation to Provability Logic

HOOO EP might sound like Provability Logic, but it is not the same thing.
Provability Logic is incompatible with HOOO EP, since Löb's axiom is absurd.
For proof, see `lob_absurd` in "source/std/modal.hooo".

You can model Provability Logic in HOOO EP,
by using explicit symbols for modality operators.

# HOOO EP

"HOOO EP" stands for "Higher Order Operator Overloading Exponential Propositions".

HOOO EP was first developed in the [Prop](https://github.com/advancedresearch/prop) library,
which exploited function pointers in Rust's type system.

The basic idea of HOOO EP is that
function pointers have the types of proofs.
By calculating with these types, one obtains new proofs. Now, in order to do this,
you need some special function pointers with types that proves
which types of function pointers one can prove.
These special function pointers are the axioms.
With other words: Type Theory Magic!

There are 3 axioms in HOOO EP:

```text
pow_lift : a^b -> (a^b)^c
tauto_hooo_imply : (a => b)^c -> (a^c => b^c)^true
tauto_hooo_or : (a | b)^c -> (a^c | b^c)^true
```

The philosophy of HOOO EP is that the axioms are intuitive.
This is how people can know that the axioms can be trusted.

From these axioms, there are infinitely complex logical consequences.
It is important to keep the axioms few and simple to not cause trouble later on.

However, some statements many people find "obviously true" can be difficult to prove.
This is why a library is needed to show how to prove such statements.

For example, in Hooo, one can prove that function composition is possible:

```text
fn pow_transitivity : b^a & c^b -> c^a {
    use hooo_imply;
    use pow_and_lift;

    x : b^a;
    y : c^b;

    fn f : a -> ((b^a & c^b) => c) {
        x : a;

        lam g : (b^a & c^b) => c {
            y : b^a;
            z : c^b;

            let x2 = y(x) : b;
            let x3 = z(x2) : c;
            return x3;
        }
        return g;
    }

    let x2 = hooo_imply(f) : (b^a & c^b)^a => c^a;
    let x3 = pow_and_lift(x, y) : (b^a & c^b)^a;
    let r = x2(x3) : c^a;
    return r;
}
```

Notice how complex this proof is compared to proving lambda/closure composition:

```text
fn imply_transitivity : (a => b) & (b => c) -> (a => c) {
    x : a => b;
    y : b => c;
    lam f : (a => c) {
        arg : a;
        let x2 = x(arg) : b;
        let x3 = y(x2) : c;
        return x3;
    }
    return f;
}
```

Intuitively, function composition is possible, so most people just take it for granted.
Previously, mathematicians needed a meta-language to prove such properties.
Now, people can prove these properties directly using Hooo-like languages.

Hooo is designed for meta-theorem proving in constructive/intuitionistic logic.
This means that Hooo can reason about its own rules.
From existing rules, you can generate new rules, by leveraging the full
power of meta-theorem proving in constructive logic.

An exponential proposition is a function pointer, or an inference rule.
You can write the type of function pointers as `a -> b` or `b^a`.

## Syntax

```text
true       True (unit type)
false      False (empty type)
a -> b     Exponential/function pointer/inference rule
b^a        Exponential/function pointer/inference rule
a => b     Imply (lambda/closure)
a & b      And (struct type)
a | b      Or (enum type)
!a         Not (sugar for `a => false`)
a == b     Equal (sugar for `(a => b) & (b => a)`)
a =^= b    Pow equal (sugar for `b^a & a^b`)
excm(a)    Excluded middle (sugar for `a | !a`)
sd(a, b)   Symbolic distinction (see section [Symbolic distinction])
~a         Path semantical qubit (see section [Path Semantics])
a ~~ b     Path semantical quality (see section [Path Semantics])
(a, b)     Ordered pair (see section [Avatar Logic])
(a : b)    Type judgement (see section [Type judgement])
(f . g)    Function composition
all(a)     Lifts `a` to matching all types
□a         Necessary `a` (modal logic)
◇a         Possibly `a` (modal logic)
foo'       Symbol `foo` (see section [Symbols])
foo'(a)    Apply symbol `foo` to `a`
sym(f, f') Symbolic block (see section [Symbolic blocks])
sym a      Locally declared symbol `a` (see section [Symbolic blocks])

x : a      Premise/argument
let y      Theorem/variable

return x                    Make a conclusion (safe)
unsafe return x             Override safety (unsafe)

sym foo;                    Declare a symbol `foo'`.
axiom foo : a               Introduce axiom `foo` of type `a`
() : a                      Prove `a`, e.g. `() : true`
f(x)                        Apply one argument `x` to `f`
f(x, y, ...)                Apply multiple arguments
match x : a                 If `x : false`
match x (l, r) : c          If `x : (a | b)`, `l : a => c` and `r : b => c`
use <tactic>                Imports tactic
fn <name> : a -> b { ... }  Function
lam <name> : a => b { ... } Lambda/closure
```

The `^` operator has high precedence, while `->` has low precedence.

E.g. `b^a => b` is parsed as `(b^a) => b`.
`b -> a => b` is parsed as `b -> (a => b)`.

### Terms and types design

In Hooo, the design is based on a principle of
making terms simple, while making types complex.
This is because terms are mostly used as tactics,
while types are statements one wants to prove.

The philosophy of this principle is that the user
wants to focus on what to prove, not how to prove it.
Therefore, how to prove it should be easy to keep in mind while having a clear overview over the progress.

The types are always listed on the right side,
to make it easy to read the proof:

```text
let <name> = <term> : <type>;
```

Hooo's design is optimized for three use cases:

1. Type checking performance
2. Proof readability
3. Source code maintenance

This leads to some design decisions that might seem
a bit strange from the perspective of normal programming.

The user is forced by the syntax of Hooo to perform
each step explicitly:

```text
let y = foo(x) : a;         // Allowed
let y = foo(bar(z)) : a;    // Disallowed
```

This is because, otherwise,
users are tempted to compress proofs into unreadable form.
Writing proofs in Hooo is an investment into the
future.
People who complain about the length of proofs
are usually using the wrong approach when evaluating proof systems.

The cost of unreadable proofs over long periods of time outweighs the short term benefits of compressible code.
However, Hooo does not prevent people from working on making proofs shorter.
Since Hooo supports meta-theorem proving,
it is encouraging users to reuse generic theorems.
This is the proper way of producing formal proofs.

### Type judgement

Most modern theorem prover assistants are based
on dependent types.
A common design in dependent typed languages,
is to build a higher level language on top of
a lower level one.
This ensures the correctness of the more complex
higher level language as long the transformation
to the lower level language is sound.

Technically, Hooo is not dependent typed.
Hooo is actually simply typed,
because in HOOO EP every type is a proposition.
However, since HOOO EP introduces exponential
propositions, the power of Hooo is comparable to
dependent type systems.

One can think about this as Hooo without a standard library resembles a
lower level language used to build a higher level
language.

For example, instead of:

```text
z' : nat'
```

Hooo requires an extra term to express type judgement:

```text
x : (z' : nat')
```

The intuition is that Hooo bootstraps from
lower to higher language through its types.
Terms at the lowest level are very simple and restricted.
Once you have developed a library for your needs,
Hooo approaches a higher level language.

The advantage of this design is that Hooo can
bootstrap over and over into higher levels.
New rules can be generated from existing rules,
while keeping a simple set of basic terms.

### Safety heuristics

Safety heuristics are used to cover two cases:

1. when proving something can lead to unsoundness
2. when the user might have intended to prove something else

Safety heuristics kick in when trying
to prove `all(..)` or `sym(..)(..)`.
This is unusual and discouraged under normal theorem proving. For example, if the user is designing axioms
of this form, it is best to be extra careful,
since it easily can lead to unintentional absurdity.

The `unsafe return` syntax is used when the safety heuristics
of the solver are too strong. This is a way for the
user to communicate that this part should be payed some attention.

One application of unsafe return is when needing to reason about unsound reasoning.
Since Hooo is used to check other mathematical languages,
it is sometimes useful to not only be able to reason
about cases that are done right, but also cases
which go wrong. When used properly, this can be done safely in Hooo by guarding the unsound reasoning behind well designed axioms.

### Symbols

The current version of Hooo uses simple symbols.
This means that instead of declaring data structures,
one can just use e.g. `foo'(a, b)`.
A symbol must be declared once before use:

```text
sym foo;
```

In other places, one must use the symbol:

```text
use foo;
```

Symbols are global, so `foo'` is `foo'` everywhere.

### Symbolic blocks

Since Hooo uses implicit quantification by lifting all
variables in `all(..)` expressions, it needs a way to
"freeze" variables to express some statements.

For example, `all(a & b -> a)` lifts `a & b -> a` to all types `a` and `b`.
This is OK for statements that are provable,
but it is not safe when one has an assumption `a -> b`.
An assumption `all(a -> b)` is absurd.

```text
fn sym_all_pow_absurd : all(a -> b) -> false {
    x : all(a -> b);
    let x2 = x() : a -> b;
    let x3 = x() : (a -> b) -> false;
    let r = x3(x2) : false;
    return r;
}
```

Hooo automatically lifts `fn` statements.
This means `all(..)` is not needed in most places.

However, sometimes we need to reason using hypothetical axioms.
The problem is that since `all(..)` lifts all variables,
there is no way to prevent some parts from being lifted.
This is why we need symbolic blocks.

```text
fn sym_absurd : a & sym(a, all(a' -> b))(a) -> false {
    x : a;
    y : sym(a, all(a' -> b))(a);
    let y2 = y() : a -> false;
    let r = y2(x) : false;
    return r;
}
```

In the `sym_absurd` example, one needs `a` and a symbolic block
`sym(a, all(a' -> b))` applied to `a` to prove `false`.
The applied symbolic block alone is not strong enough.

Hooo understands how to convert to and from sym-blocks automatically.
For example, `a` is the same as `sym(b, b')(a)`.

In some cases, you need to prove properties of sym-blocks.
To make this easier, there is an axiom `sym_transport`:

```text
sym_transport : sym(a, b) & (b == c)^(sym a) -> sym(a, c)
```

This allows you to transport the body expression of a sym-block.
The type `sym a` has no term, but you can just declare a symbol locally:

```text
fn sym_eq_refl : sym a  ->  a' == a' {
    sym a;
    use eq_refl;
    use triv;
    let r = triv(eq_refl) : a' == a';
    return r;
}
```

### Congruence

An operator `f` is normal congruent when:

```text
a == b  ->  f(a) == f(b)
```

An operator `f` is tautological congruent when:

```text
(a == b)^true -> f(a) == f(b)
```

Most operators are normal congruent.
Some theories treat all operators within the theory
as normal congruent, e.g. predicates in First Order Logic.

However, in [Path Semantics](https://github.com/advancedresearch/path_semantics/tree/master) there
are some operators which are tautological congruent.

For example, path semantical quality and symbolic distinction are tautological congruent.

In traditional mathematics,
definitional equality was introduced for convenience,
which might be interpreted as
a subjective notion of equality that is stronger
than tautological equality.

The problems with using definitional equality:

- no distinction between tautological and normal equality
- no known examples where tautological equality is not sufficient
- normal equality is preferred, when possible

Since Hooo can not assume congruence for all operators, it must be axiomized per operator.
To learn more, see "source/std/cong.hooo".

The upside is that Hooo is more logical precise.
The downside is that normal congruence must be proved for sym-blocks, for example:

```text
fn cong_sym_id : true -> cong'(sym(a, a')) {
    use cong_from;
    use refl;

    x : true;

    let x2 = refl() : all(a == b -> a == b);
    let x3 = x2() : all(a == b -> sym(a, a')(a) == sym(a, a')(b));
    let x4 = x3() : sym(f, all(a == b -> f'(a) == f'(b)))(sym(a, a'));
    let r = cong_from(x4) : cong'(sym(a, a'));
    return r;
}
```

Notice how this proof uses Hooo's internal knowledge
about sym-blocks. The above proof is considered to be a
very deep insight, because it shows that normal congruence is a natural property of mathematics.

### Symbolic distinction

Paper: [Symbolic distinction](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/symbolic-distinction.pdf).

In normal logic, there is no way to distingish propositions from each other
without adding explicit assumptions.
With other words, logic is not allowed to know internally
the accurate representation of data.
This is because logic is used to reason hypothetically.

For example, you know that the symbol `x'` is identical to `x'`.
Yet, logic can not know this internally, because it would lead to unsoundness.
If one has two indistinct symbols which are non-equal, then this would be unsound in logic.

You must always be allowed to treat propositions as equal,
although they are strictly symbolic distinct:

- `a == b` (normal equality)
- `(a == b)^true` (tautological equality)

There should be no stronger notion of equality in logic than tautological equality.
Most operators are congruent by normal equality,
but a few operators are only congruent by tautological equality.

However, there are no problems in logic by using symbolic distinction.

- `sd(a, b)` (`a` and `b` are symbolic distinct)

For example, in Hooo, one can distinguish two symbols `foo'` and `bar'`:

`let x = () : sd(foo', bar');`

This is useful when you are working with theories that need
some form of uniqueness.

For example, in Type Theory, a member of a type is
only allowed to have a unique type.
When we work with Type Theory in logic,
we are allowed to assume that two types are equal,
but the theory decides whether this is permitted.
The theory can not prevent us from making assumptions,
but it can control the consequences.
Without symbolic distinction, there is no way to tell
in logic that two types are not permitted to be equal.

Symbolic distinction allows you to add axioms for such cases
and still be able to reason hypothetically.

### Path Semantics

[Path Semantics](https://github.com/advancedresearch/path_semantics)
is an expressive language for mathematical programming.

Mathematical programming usually deals with higher dimensions compared to normal programming.
In normal programming, you have just one dimension of evaluation.
In higher dimensional programming, you can have multiple dimensions of evaluation.
It is not as simple as parallelism, because you can evaluate functions as boundaries of a "function surface".
Such surfaces, called "normal paths", must be treated as mathematical objects on their own,
which requires a foundation of higher dimensional programming.

For example:

```text
len(concat(a, b)) <=> add(len(a), len(b))
```

To write this as a normal path:

```text
concat[len] <=> add
```

In Category Theory, `concat[len]` is an "open box" which is closed by `add`.

Now, since `add[even] <=> eqb`, one can prove:

```text
concat[len][even] <=> add[even]
concat[len][even] <=> eqb
concat[even . len] <=> eqb
```

The idea is that normal paths compose in an "orthogonal dimension" to normal computation.
One uses this notation because it does not require variables,
hence being a style of "point-free" theorem proving.

The foundation of higher dimensional programming is notoriously hard,
so you should not feel bad if you do not understand the entire theory.
There is a lot to take in, so take your time.

Path Semantics is just one approach to higher dimensional programming.
Another approach is Cubical Type Theory.

#### Changing perspective of type hierarchies

Since higher dimensions often explode in combinatorial complexity,
there is no way we can explore the entire space of possibilities.
Therefore, we have to be satisfied with proving some properties
across multiple dimensions.

Naturally, we are used to think of types as a way of organizing data. However, if you have a powerful logic
such as HOOO EP, then it also makes sense to reason
about type hierarchies as "moments in time".
Each moment in time is a local space for reasoning in IPL.

Path Semantics at its fundamental level is the mechanism that allows propositions to transition
from one moment in time to another moment.

This is expressed in the core axiom of Path Semantics:

```text
ps_core : (a ~~ b) & (a : c) & (b : d) -> (c ~~ d)
```

The operator `~~` is path semantical quality,
which is a partial equivalence that lifts bi-conditions using symbolic distinction:

```text
q_lift : sd(a, b) & (a == b) -> a ~~ b
```

This means, that when one assumes equality in some
moment of time between two propositions that can be
proved to be symbolic distinct, one is allowed to
introduce quality and hence get a way to propagate
new quality propositions in future moments.

The reason for this mechanism is that in any moment of time,
the information is relative to its internal state.
So, there must be at least two separate physical states
to store information from the past.
Path semantical quality is a logical model of this phenomena.

If you find this hard to think about, then you can just
use the thumb rule "if two symbols are qual `a ~~ b`, then their meanings `(a : c) & (b : d)` are qual `c ~~ d`". This is a proper way of handling semantics of symbols in logic. Notice that you should not use "equal" because reflexivity and logical implication makes this unsound.

Path semantical quality `~~` is a way to express an
intentional equivalence relation in logic.
Like, solutions or some existence of unification.
The operator is sometimes thought of as a path, so the meaning of symbols using paths was why this field became "Path Semantics".

In philosophy, path semantical quality is closely
related to Hegel's philosophy of Being.
Hegel's philosophy was rejected by Russell,
who founded analytic philosophy.
This turned out to be a mistake, likely because
Russell was influenced by the language bias of First Order Logic, where all predicates are normal congruent.
By using tautological congruence, one can reason about
Hegel's philosophy just fine.
However, this requires HOOO EP.

Self quality `a ~~ a` is equivalent to `~a`,
which is called a "qubit".
The name "qubit" comes from the model in classical logic, where one generates a random truth table of `~a` using `a` as the seed to the random generator.
This makes `~a` behave as if it is in super-position of all propositions, hence similar to qubit in a classical approximation of a quantum circuit.
One can also think about it as introducing a new proposition.

Path semantical quality and qubit are tautological congruent.

### Uniqueness, solutions and the imaginary

Path semantical quality `~~`, or qubit `~`, are often used as
"flags" for other theories to express uniqueness or solutions.

- `!~a` is an expression that `a` is unique
- `~a` is an expression that `a` has some solution

By default, you are not able to prove `~a` or `!~a`,
which means that you have a choice.
You can design your theory leaning toward `~a`,
or you can go in the opposite direction and lean toward `!~a`.
The direction a theory is designed is called "language bias".
Notice that they both are expressions of the underlying idea "there exists a solution".
The way they differ is in plurality,
where `!~a` means "one" and `~a` means "many".

Theories that lean toward `!~a` are called "Seshatic"
from [Seshatism](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatism.pdf).
On the other hand, theories that lean toward `~a` are called "Platonic" from Platonism.
Seshatism is the dual of Platonism.
They differ from each other in the way existence is
biased by language, either toward "one-ness" (concrete)
or "many-ness" (abstract).

Intuitively, an abstract object can be copied,
so it has a kind of "many-ness" built into it.
A concrete object can not be copied,
because this would destroy its uniqueness.

When mathematics works in absence of solutions
we call it "imaginary" that has some kind of "zero-ness" to it,
e.g. the imaginary unit `i` in complex numbers.
In logic, this is simply theorems that do not need
`!~a` or `~a`.

### Avatar Logic

Avatar Logic is an alternative to First Order Logic
which is more suitable for higher dimensional mathematics.
The reason is that it gets rid of predicates and replaces
them with binary relations, avatars and roles.
This design generalizes better over
multiple dimensions of evaluation.

You can experiment with Avatar Logic using [Avalog](https://github.com/advancedresearch/avalog), which is a Prolog-like language.

There are two basic axioms in Avatar Logic:

```text
ava_univ : !~b & (a, b) & (b : c)  ->  c(a) == b
ava_ava : (a, b(c)) & (b(c) : d)  ->  d(a) => b(c)
```

The first axiom `ava_univ` says that if `b` is unique, (expressed as `!~b`) and `b` has the role `c` (expressed as `b : c`) then it is sufficient to say `(a, b)` (an ordered pair) to determine `c(a) == b`.

In some sense, `ava_univ` says what it means to "compute" `b`. Another way to think of it is as a property `c` of `a`. When `b` is unique,
it is forced to behave that way for all other objects.
Every other object needs to use `b` the same way.
This is why `b` is thought of as a unique universal binary relation.

However, unique universal binary relations are too restrictive in many cases. This is why we need an "avatar". An avatar is a symbol which wraps another expression, e.g. `ava'(a)` where `ava'` is the avatar and `a` is the expression wrapped by `ava'`.

The second axiom `ava_ava` tells that when `b(c) : d`
it is sufficient to say `(a, b(c))` to determine
`d(a) => b(c)`. Notice that this is a weaker conclusion.

For example, if `(carl', parent'(alice'))` and
`parent'(alice') : mom'` then `mom'(carl') => parent'(alice')`. In this case, Carl is allowed to
have more than one mom.

If `!~parent'(alice')`, then Carl has only one mom Alice, because `mom'(carl') == parent'(alice')`.

Avatar Logic is well suited to handle complex relations
between objects that are often found in the natural world, such as family relations. In some sense,
Avatar Logic handles "exceptions to the rule" very well.

There is one more axiom that handles collision between avatars:

```text
ava_collide :
  (b, q1(a1)) & (b, q2(a2)) &
  (q1(a1) : p) & (q2(a2) : p) -> !sd(q1, q2)
```

For example, if you try to use `foo'` and `bar'` as avatars in the same place,
one can prove that they will collide:

```text
sym foo;
sym bar;
sym p;

fn test :
    (b, foo'(a1)) & (b, bar'(a2)) &
    (foo'(a1) : p') & (bar'(a2) : p')
-> false {
    arg : (b, foo'(a1)) & (b, bar'(a2)) &
          (foo'(a1) : p') & (bar'(a2) : p');
    use std::ava_collide;
    let x = ava_collide(arg) : !sd(foo', bar');
    let y = () : sd(foo', bar');
    let r = x(y) : false;
    return r;
}
```

If you want to treat a role `p` as unique for all its members,
then you can use the following theorem:

```text
ava_lower_univ : !~p & (b, a) & (a : p) -> p(b) == a
```

### Homotopy Type Theory

Homotopy Type Theory is a branch of mathematics
that uses type theory for formalizing homotopy theory.
Homotopy theory is a sub-field of topology which
treats two topological spaces equivalent if the two
spaces can be contracted into each other.
It turns out that Homotopy Type Theory also is useful
as a foundation for mathematics, since proofs are
mathematical objects that correspond to paths in
topological spaces equivalent up to homotopy.

Hooo uses a version of Cubical Type Theory
for Homotopy Type Theory.
This version uses path semantical quality `a ~~ b` instead of lambda expressions for canonical paths, such that one can use `iq_left` or `iq_right` to calculate the end-points of a path:

```text
iq_left : true -> (a ~~ b)(i0') == a
iq_right : true -> (a ~~ b)(i1') == b
```

Type formation of a path:

```text
iq_ty : (a : c) & (b : c) -> ((a ~~ b) : I' => c)
```

It follows that path semantical qubit `~a` gets the properties of a constant path:

```text
iqu_left : true -> (~a)(i0') == a
iqu_right : true -> (~a)(i1') == a
iqu_ty : (a : c) -> (~a : I' => c)
```

Terminology:

```text
a ~~ b    Canonical path between two points `a` and `b`
~a        Constant path from point `a` to itself
I'        Interval type
i0'       Start of interval
i1'       End of interval
Id'       Identity type
idt_r'    Reflexivity of identity type
idt_s'    Symmetry of identity type
idt_t'    Transitivity of identity type
idt_i'    Identity type constructed from path
```
