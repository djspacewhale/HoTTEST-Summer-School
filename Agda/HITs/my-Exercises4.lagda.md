```agda
{-# OPTIONS --without-K --rewriting #-}

open import new-prelude
open import Lecture4-notes

module my-Exercises4 where
```

# Constructing homotopies between paths

(⋆) Give two "different" path-between-paths/homotopies between (loop ∙ !
loop) ∙ loop and loop.  They should be different in the sense that one
should cancel the !loop with the first loop, and one with the second
loop.  But these aren't really *really* different, in that there will be
a path-between-paths-between-paths between the two!  

```agda
homotopy1 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy1 = (loop ∙ ! loop) ∙ loop ≡⟨ ap (λ x → x ∙ loop) (!-inv-r loop) ⟩
            (refl _) ∙ loop        ≡⟨ ∙unit-l loop ⟩
            loop ∎

homotopy2 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy2 = (loop ∙ ! loop) ∙ loop ≡⟨ ∙assoc _ _ _ ⟩
            loop ∙ (! loop ∙ loop) ≡⟨ ap (λ x → loop ∙ x) (!-inv-l loop) ⟩
            loop ∙ refl _          ≡⟨ ∙unit-r loop ⟩
            loop ∎
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
  lem1 = p ∙ p ∙ ! p   ≡⟨ ∙assoc _ _ _ ⟩
         p ∙ (p ∙ ! p) ≡⟨ ap (λ x → p ∙ x) (!-inv-r _) ⟩
         p ∙ refl _    ≡⟨ ∙unit-r _ ⟩
         p ∎

  lemma : p ≡ p ∙ p ∙ ! p
  lemma = ! lem1

conj1-pointed : {A : Type} (a : A) (p q : a ≡ a) → is-conj a a p q → ((a , p) ≡ (a , q))
conj1-pointed a p q x = conj1 a a p q x
```

(Harder exercise (🌶️): give a path between homotopy1 and
homotopy2! I'd recommend saving this until later though, because there
is a trick to it that we haven't covered in lecture yet.)

```agda
path-between-paths-between-paths : homotopy1 ≡ homotopy2
path-between-paths-between-paths = {!!}
```

# Functions are group homomorphism 

(⋆⋆) State and prove a general lemma about what ap of a function on the
inverse of a path (! p) does (see ap-∙ for inspiration).  

State and prove a general lemma about what ! (p ∙ q) is.

Use them to prove that the double function takes loop-inverse to
loop-inverse concatenated with itself.

```agda
ap-inv : {A B : Type} {a b : A} (p : a ≡ b) (f : A → B) → ap f (! p) ≡ ! (ap f p)
ap-inv (refl _) f = refl _

ap-inv-dist : {A B : Type} {a b c : A} (p : a ≡ b) (q : b ≡ c) (f : A → B) → ap f (! (p ∙ q)) ≡ ! (ap f q) ∙ ! (ap f p)
ap-inv-dist (refl _) (refl _) f = refl _

double-!loop : ap double (! loop) ≡ ! loop ∙ ! loop
double-!loop = ap-inv-dist {!!} {!!} double
```

(⋆) Define a function invert : S1 → S1 such that (ap invert) inverts a path
on the circle, i.e. sends the n-fold loop to the -n-fold loop.  

```agda
invert : S1 → S1
invert = S1-rec base (! loop)
```

# Circles equivalence

See the maps between the 1 point circle and the 2 point circle in the
lecture code.  Check that the composite map S1 → S1
is homotopic to the identity on base and loop:

(⋆) 

```agda
to-from-base : from (to base) ≡ base
to-from-base = S1-rec (refl _) (refl _) base
```

(⋆⋆⋆) 

```
to-from-loop : ap from (ap to loop) ≡ loop
to-from-loop = S1-rec {!!} {!!} base
```

Note: the problems below here are progressively more optional, so if you
run out of time/energy at some point that is totally fine.  

# Torus to circles

The torus is equivalent to the product of two circles S1 × S1.  The idea
for the map from the torus to S1 × S1 that is part of this equivalence
is that one loop on on the torus is sent to to the circle loop in one
copy of S1, and the other loop on the torus to the loop in the other
copy of the circle.  Define this map.  

Hint: for the image of the square, you might want a lemma saying how
paths in product types compose (⋆⋆⋆):

```agda
compose-pair≡ : {A B : Type} {x1 x2 x3 : A} {y1 y2 y3 : B}
                (p12 : x1 ≡ x2) (p23 : x2 ≡ x3)
                (q12 : y1 ≡ y2) (q23 : y2 ≡ y3)
              → ((pair≡ p12 q12) ∙ (pair≡ p23 q23)) ≡ {!!} [ (x1 , y1) ≡ (x3 , y3) [ A × B ] ]
compose-pair≡ = {!!}
```

(🌶️)
```
torus-to-circles : Torus → S1 × S1
torus-to-circles x = T-rec ({!!} , {!!}) {!!} {!!} {!!} x
```

# Suspensions (🌶️)

Find a type X such that the two-point circle Circle2 is equivalent to
the suspension Susp X.  Check your answer by defining a logical
equivalence (functions back and forth), since we haven't seen how to
prove that such functions are inverse yet.

```agda
c2s : Circle2 → Susp Bool
c2s x = Circle2-rec northS southS (merid true) (merid false) x

s2c : Susp Bool → Circle2
s2c x = Susp-rec north south paths x where
  paths : Bool → north ≡ south
  paths true = west
  paths false = east
```

Suspension is a functor from types, which means that it acts on
functions as well as types.  Define the action of Susp on functions:

```agda
susp-func : {X Y : Type} → (f : X → Y) → Susp X → Susp Y
susp-func f x = Susp-rec northS southS (λ y → merid (f y)) x
```

To really prove that Susp is a functor, we should check that this action
on functions preserves the identity function and composition of
functions. But to do that we would need the dependent elimination rule
for suspensions, which we haven't talked about yet.

# Pushouts (🌶️)

Fix a type X.  Find types A,B,C with functions f : C → A and g : C → B
such that the suspension Susp X is equivalent to the Pushout C A B f g.
Check your answer by defining a logical equivalence (functions back and
forth), since we haven't seen how to prove that such functions are
inverse yet.

```agda
SuspFromPush : Type → Type
SuspFromPush A = Pushout A 𝟙 𝟙 (λ x → ⋆) λ x → ⋆

s2p : (A : Type) → Susp A → SuspFromPush A
s2p A x = Susp-rec (inl ⋆) (inr ⋆) (λ y → glue y) x

p2s : (A : Type) → SuspFromPush A → Susp A
p2s A x = Push-rec (λ y → northS) (λ y → southS) (λ c → merid c) x
```

