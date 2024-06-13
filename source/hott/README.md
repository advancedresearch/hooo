# Homotopy Type Theory

Homotopy Type Theory (HoTT) is a branch of mathematics
that uses type theory for formalizing homotopy theory.
Homotopy theory is a sub-field of topology which
treats two topological spaces equivalent if the two
spaces can be contracted into each other.
It turns out that Homotopy Type Theory also is useful
as a foundation for mathematics, since proofs are
mathematical objects that correspond to paths in
topological spaces equivalent up to homotopy.

For more information, see [Homotopy Type Theory](https://homotopytypetheory.org/book/).

### Path Semantical Quality in HoTT

Hooo uses a version of Cubical Type Theory
for Homotopy Type Theory.
This version uses path semantical quality `a ~~ b` instead of lambda expressions for path types, such that one can use `iq_left` or `iq_right` to calculate the end-points of a path:

```text
iq_left : true -> (a ~~ b)(i0') == a
iq_right : true -> (a ~~ b)(i1') == b
```

One can think about `a ~~ b` as a simple set of
two elements, because the order can be swapped to `b ~~ a` using `q_symmetry`:

```text
q_symmetry : a ~~ b  ->  b ~~ a
```

Therefore, whether you use `i0'` or `i1'`,
it does not really matter, because it is just a way
to obtain the end-points of a path.
However, this is just for path semantical quality.
You can create your own operators when the order matters and use them with HoTT.

### Homotopy Levels

A space can contain multiple homotopy levels at once.

A homotopy level is like a key that opens up a door
to access some part of a space (e.g. a room in a house). The homotopy level contains paths between objects of the homotopy level below.

For example, in one room you have paths between points,
in another room you have paths between lines,
in a third room you have paths between surfaces,
in a fourth room you have paths between cubes etc.

To access the entire space, you need all the keys
to all the rooms. You can not get access to one room for free by accessing some other room (unless there are explicit assumptions added to do so).

It is important to remember the following:

*A line is not the same as a path.*

So, when I say "points, lines, rectangles, cubes" etc.
I do *not* mean paths. A path between two points means in some sense there is a "truth" between them.
You have the points when you have the path.

On the contrary, a line is a proof of some path,
but does not mean that you have the points of that path.

This might seem confusing at first, but you will get used to it. I will explain what it means later.

### Points

A point in a space is simply a proof of some type:

```text
a : x
```

Notice that in Hooo, this is written:

```text
let a_ty = ... : (a : x);
```

Hooo is for propositional logic, so all advanced
Type Theory happens as propositional types.
Every type in Hooo is propositional.

In HoTT, only types in h-level 1 are propositional.
So, to not mix homotopy propositions with Hooo
propositions, HoTT uses `hprop_` or `hlev_` prefix in theorems.

Hooo is very powerful and used for other things besides
HoTT, so one should think of it as HoTT being implemented or formalized in Hooo.

H-level 1 that contains h-propositions will be explained later.

### Paths

A path between `a` and `b` is the following:

```text
(a ~~ b) : I' => x
```

It follows that path semantical qubit `~a`
is a path loop from `a` to `a`:

```text
~a : I' => x
```

You can obtain the points from a path using `i_points`:

```text
i_points : ((a ~~ b) : I' => x) -> (a : x) & (b : x)
```

### Lines

A line is a proof of a path:

```text
p : ((a ~~ b) : I' => x)
```

Notice that a line is *not* the same as a path.
You can not obtain the points of the path from a line.
To do that you need the path.

When you have a line, it is like saying there is path between two points,
but this statement can be true even the space
contains no points at all!
This is kind of like lying, but it is technically true.
In logic, we say that such statements are absurd.

In HoTT, you have to be more specific when using
language than in natural language.
So, you have to get used to this terminology,
because natural language is too ambiguous to handle it.

A line in HoTT is not the same as a line in geometry.
In geometry, there are always points on a line.
You can not draw a line without points!

In geometry, there are also coordinates for points.
However, in HoTT, which a synthetic theory,
not analytic like geometry, there are no coordinates associated with points. Coordinates are intuitive for people to think about. It is kind of sad that there is a line, but there is no way to picture how it is drawn. However, that's life!

### Topology

Btw, points in HoTT also do not have any coordinates.
Neither points nor lines can be pictured as being
drawn in a specific way.

When reasoning about spaces with the property that
there are no concrete coordinates, mathematicians
call it "topology".

Topology is a huge field of mathematics that people
spend their entire careers studying.
Traditionally, topology was thought of as a subset
of Set Theory.
When mathematicians explained what topology was,
they used Set Theory to define it.

However, I can not explain to you what topology
actually is, because there is no Set Theory underneith
it in HoTT. Instead, you have to embrace the philosophy
you get through Path Semantics to understand it. A path is something vague that comes in many forms.
Path Semanticists just accepts that the foundation
of Path Semantics is so existential horrible that no
philosopher in existential philosophy has managed to
produce anything close to as existentially horrible.
Yet it works, every time.

In HoTT, topology is the language one can use to
develop an intuition for how it works.
It does not mean that HoTT *is* topology.
In Path Semantics, we say that there is a normal path
from topology to HoTT, which is more abstract than
what we mean by ordinary topology.
People working in HoTT say that it is a synthetic theory of topology, which is saying the same in a more vague way.

### Rectangles

While lines in HoTT can be difficult to wrap your head around, at least it refers to two points:

```text
p : ((a ~~ b) : I' => x)
```

What is even more counter-intuitive is that when I say a "rectangle" it does not mean that it has 4 corners. Instead, a "rectangle" is actually more like an eye-shape where there are 2 corners:

```text
r : ((p ~~ q) : I' => ((a ~~ b) : I' => x))
```

It is called a "rectangle" because `I'` occurs twice.
Naturally, if you use `i0'` or `i1'` there would be 4 combinations:

```text
i0' i0'
i0' i1'
i1' i0'
i1' i1'
```

However, you can not actually access these corners from a rectangle. If you have a path between two lines then you can access the lines. However, a rectangle is a proof of a path between lines. This does not mean that you have the lines when you have the rectangle.

### Understanding Homotopy Levels

Now you have a basic understanding of the language of HoTT, I can show you how to think about homotopy levels in more detail.

A homotopy level gives you a list of stuff to do before you get some concrete path at the end.

In h-level 0, the todo list is empty:

```text
HLev'(z', x) -> x
```

You can use `hlev_z`:

```text
hlev_z : true -> HLev'(z', x) == x
```

In higher h-levels, you always start with two points,
followed by two lines, two rectangles, two cubes, etc.
You get the path after `n` steps:

```text
HLev'(n, x) ->
points =>
lines =>
rectangles =>
cubes =>
...
path
```

The path at the end gets more and more higher dimensional when you climb up homotopy levels.

### For every two points, for every two lines, ...

This part is really a brain-wrecker.
If you do not understand this, just skip it and come back to it later.

When you have access to some h-level,
you can progress toward the path using any element
available in the space. It does not matter e.g.
which points you use, but remember that the next steps
depend on what you chose previously.

So, a homotopy level is actually a broad way to talk
about the things in the space, as some kind of symmetry that holds for every combination of two objects at a time.

To make it easier to think about, one chooses two elements at every step toward the path.
Do not try to think too much about what it actually
means across all possible choices,
because this will blow your mind.

The definition of higher homotopy levels is extremely simple, but it packs an enormous amount of meaning:

```text
hlev_sn : (n : nat') ->
    HLev'(s'(n), x) == sym(n, sym(x, all(
        (a : x') & (b : x') => HLev'(n', (a ~~ b) : I' => x')
    )))(n)(x)
```

Notice how it uses lower homotopy levels.
This definition is usually unpacked into more straight-forward todo lists to get to the path at the end.

You do not have to worry about the precise meaning, unless you need to prove a h-level from some other axioms. This can be pretty hard.
