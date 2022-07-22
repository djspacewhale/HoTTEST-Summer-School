# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module my-02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)

retr : {A B : Type} → (A → B) → Type
retr {A} {B} f = Σ g ꞉ (B → A) , ((x : A) → g (f x) ≡ x)

retr-is-inj : {A B : Type} → ((f : A → B) → (p : retr f) → (a b : A) → ((f a ≡ f b) → (a ≡ b)))
retr-is-inj f (g , h) a b p = a-to-b where
  a-to-gfa : g (f a) ≡ a
  a-to-gfa = h a

  b-to-gfb : g (f b) ≡ b
  b-to-gfb = h b

  gfagfb : g (f a) ≡ g (f b)
  gfagfb = ap g p

  a-to-b : a ≡ b
  a-to-b = trans (sym a-to-gfa) (trans gfagfb b-to-gfb)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = (inl a) , (inl b)
[i] (inr c) = (inr c) , (inr c)

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl x , c) = inl (x , c)
[ii] (inr x , c) = inr (x , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
pr₁ ([iii] x) = λ a → x (inl a)
pr₂ ([iii] x) = λ b → x (inr b)

[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] x = {!!}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] x nb a = nb (x a)

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] x b = {!!}

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] x = {!!}

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] x a b = x (a , b)

[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] x = {!!}

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
pr₁ ([x] x) a = x a .pr₁
pr₂ ([x] x) a = x a .pr₂
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne x a = x λ b → b a
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor x nna nb = nna λ a → nb (x a)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli x nna nb = nna λ a → x a nb
```
Hint: For the second goal use `tne` from the previous exercise

## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ true true x = id , id
bool-≡-char₁ false false x = id , id
```


### Exercise 3 (★★)

Using ex. 2, concldude that
```agda
true≢false : ¬ (true ≡ false)
true≢false x = bool-≡-char₁ true false x .pr₁ ⋆
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true (f , g) = refl true
bool-≡-char₂ true false (f , g) = 𝟘-elim (f ⋆)
bool-≡-char₂ false true (f , g) = 𝟘-elim (g ⋆)
bool-≡-char₂ false false (f , g) = refl false
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```
Prove that
```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
pr₁ (decidable-equality-char A) hyp = f , g
  where
  f' : (a b : A) → is-decidable (a ≡ b) → Bool
  f' a b (inl x) = true
  f' a b (inr x) = false

  f'-refl : (x : A) (d : is-decidable (x ≡ x)) → f' x x d ≡ true
  f'-refl x (inl _) = refl true
  f'-refl x (inr h) = 𝟘-nondep-elim (h (refl x))

  f : A → A → Bool
  f a b = f' a b (hyp a b)

  g : ∀ x y → x ≡ y ⇔ (f x y) ≡ true
  pr₁ (g x .x) (refl .x) = f'-refl x (hyp x x)
  pr₂ (g x y) h with hyp x y
  ... | (inl p) = p
  ... | (inr _) = 𝟘-nondep-elim (true≢false (sym h))

pr₂ (decidable-equality-char A) (f , g) a b
  with Bool-has-decidable-equality (f a b) true
... | (inl p) = inl (g a b .pr₂ p)
... | (inr h) = inr λ p → h (g a b .pr₁ p)
```
