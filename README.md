# linear: Linear Algebra Done Lean

This project aims to formalize basic results in linear algebra using the [Lean proof assistant](http://leanprover.github.io/), loosely following the third edition of Axler's _Linear Algebra Done Right_. If you can, please contribute! Math is hard.

## Code style

**Exploit the typechecker**---consider defining the image of a function as [here](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf#46). The alternative way is the `set` predicate `∃ x, y = f x`. While both are equally valid, we would prefer the former since once the  `image_of`'s destructor is applied, the term `y` in question is unified with `f x` automatically. Whereas with the alternative definition, one would have to manually substitute `y` with `f x` using the given equality. Although the benefits aren't visible with such a small example, manual substitutions add up in larger proofs.

In general, we should structure definitions in a way that unifications that your average mathematician takes for granted when doing a proof are performed automatically. After all, we want to make the typechecker work for us---not the other way around.

**Separation of concerns**---TODO structuring sections for related definitions, namespaces, ...

**Use structured proofs if possible**---TODO for readability, especially if automation is doing magical things...

**Naming conventions**---TODO there is no right answer...

We should also the builtin projects & wiki features to track and document proofs, definitions, etc. with references to the textbook.