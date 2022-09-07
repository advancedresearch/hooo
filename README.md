# hooo
Propositional logic with exponentials

```text
=== HOOO 0.1 ===
For more information, type `help`
> use silence
> use zero
> use and
> use eq
> use hooo
> ((a = b) ^ True)
(((A □ B) ^ X) = ((A ^ X) □ (B ^ X))) by hooo
((a ^ ⊤) = (b ^ ⊤)) by eq
```

To run hooo from you Terminal, type:

```text
cargo install --example hooo hooo
```

Then, to run:

```text
hooo
```

### Motivation

The ongoing research on [PSQ](https://advancedresearch.github.io/quality/summary.html#psq---path-semantical-quantum-propositional-logic)
suggests that propositional logic can be extended with [Category Theory Exponentials](https://ncatlab.org/nlab/show/exponential+object).

The problem is that PSQ contains a qubit operator `~` with the special property
that it has congruence by tautological identity only.
In current theorem provers, it has not been possible to reason about this.

For example, `a == b` does not imply `~a == ~b`,
only when `a == b` is provable from none assumptions.

The `(a == b)^true` relation is an *exponential* proposition
which proves that `a == b` from none assumptions.
This gives `a == b` the *tautological identity* needed for substitution in the qubit operator `~`.

It turns out that this is semantically the same as [Higher Order Operator Overloading](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#higher-order-operator-overloading).

Or simply: hooo
