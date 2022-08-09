```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical-HoTT where

open import cubical-prelude
```

```agda
private
  variable
    A : Type ℓ
    B : A → Type ℓ
```

There are a couple goals to this project: formalize Van Kampen, formalize homology, and gather resources
for talks/presentations on synthetic homotopy theory. Existing sources include the cubical library and
its contributions, including Favonia's work on covering spaces and their Galois correspondence, Dan
Licata's work on Eilenberg-MacLane spaces, and Anders Mörtberg's work on ℤ-cohomology.

```agda
vanKampen : {A B C : Type} (f : C → A) (g : C → B) → || Pushout f g || ≡ Pushout || f || || g ||
vanKampen = ?
```
