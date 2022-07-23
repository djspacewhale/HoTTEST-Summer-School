```agda
{-# OPTIONS --without-K --rewriting #-}

open import new-prelude
open import Lecture4-notes

module Hatcher-1-6 where
```

The following code is for Hatcher, Exercise 1.6. I define conjugacy of unpointed loops,
then prove that two pointed loops are conjugate iff they are homotopic as unpointed loops.
What is unproven here is the equivalence (S1 → A) ≡ (Σ a : A , (a ≡ a)), which can be proved
from the universal property of S1.
```agda
is-conj : {A : Type} → (a b : A) → (p : (a ≡ a)) → (q : (b ≡ b)) → Type
is-conj a b p q = Σ r ꞉ (a ≡ b) , p ≡ r ∙ q ∙ (! r)

conj1 : {A : Type} (a b : A) (p : a ≡ a) (q : b ≡ b) → is-conj a b p q → ((a , p) ≡ (b , q))
conj1 a .a p q (refl .a , hyp) = lemma where
  lem1 : p ≡ q
  lem1 = p          ≡⟨ hyp ⟩
         refl a ∙ q ≡⟨ ∙unit-l _ ⟩
         q ∎

  lem2 : p ≡ q → (a , p) ≡ (a , q)
  lem2 (refl .p) = refl _

  lemma : (a , p) ≡ (a , q)
  lemma = lem2 lem1

conj2 : {A : Type} (a : A) (p q : (a ≡ a)) → ((p ≡ q) → is-conj a a p q)
conj2 a p .p (refl .p) = p , lemma where
  lem1 : p ∙ p ∙ ! p ≡ p
  lem1 = p ∙ p ∙ ! p   ≡⟨ ! (∙assoc p p (! p)) ⟩
         p ∙ (p ∙ ! p) ≡⟨ ap (λ x → p ∙ x) (!-inv-r p) ⟩
         p ∙ refl _    ≡⟨ ∙unit-r _ ⟩
         p ∎

  lemma : p ≡ p ∙ p ∙ ! p
  lemma = ! lem1

conj1-pointed : {A : Type} (a : A) (p q : a ≡ a) → is-conj a a p q → ((a , p) ≡ (a , q))
conj1-pointed a p q x = conj1 a a p q x
```
