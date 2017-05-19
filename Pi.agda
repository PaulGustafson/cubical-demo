{-# OPTIONS --cubical --rewriting #-}

-- Ported from cubicaltt

module Pi where
open import PathPrelude
open import GradLemma
open import Sub


-----------------------------------
-- Example: Equality in pi types --
-----------------------------------

pi : ∀ {l m} (A : Set l) (P : A -> Set m) ->  Set (l ⊔ m) 
pi A P = (x : A) -> P x

idPi : ∀ {l m} {A : Set l} {B : A -> Set m} (f g : pi A B) -> Path ((x : A) -> Path (f x) (g x)) (Path f g)
idPi {l} {m} {A} {B} f g = sym (isoToPath F G S T )
  where T0 : Set (l ⊔ m)
        T0 = Path f g
        T1 : Set (l ⊔ m) 
        T1 = (x : A) -> Path (f x) (g x)
        F : T0 -> T1  
        F p = \ (x : A) -> \ i -> (p i) x
        G : T1 -> T0
        G p = \ i -> \ (x : A) -> (p x) i
        S : (p : T1) -> Path (F (G p)) p 
        S p = refl 
        T : (p : T0) -> Path (G (F p)) p 
        T p = refl 

setPi : ∀ {l m} {A : Set l} {B : A → Set m} (h : (x : A) -> set (B x)) (f g : pi A B) -> prop (Path f g)
setPi {l} {m} {A} {B} h f g = rem
  where
    T : Set (l ⊔ m)
    T = (x : A) -> Path (f x) (g x)

    rem1 : prop T
    rem1 = \ (p q : T) -> \ i -> \ (x : A) -> h x (f x) (g x) (p x) (q x) i

    rem : prop (Path f g)
    rem = subst prop (idPi f g) rem1

groupoidPi : ∀ {l m} {A : Set l} {B : A -> Set m} (h : (x : A) -> groupoid (B x)) (f g : pi A B) -> set (Path f g)
groupoidPi {l} {m} {A} {B} h f g = subst set {a = T} {b = Path f g} (idPi f g) rem1
  where
    T : Set (l ⊔ m)
    T = (x : A) -> Path (f x) (g x)

    rem1 : set T
    rem1 = setPi {B = \ (x : A) ->  Path (f x) (g x)} (\ (x : A) -> h x (f x) (g x))

propPi2 : ∀ {l m} {A : Set l} {B0 : A -> A -> Set m} (h0 : (x y : A) -> prop (B0 x y)) -> prop ((x y : A) -> B0 x y)
propPi2 {l} {m} {A} {B0} h0 = propPi p0
  where 
    p0 : (a : A) -> prop ((b : A) -> B0 a b)
    p0 a = propPi (h0 a)

propPi3 : ∀ {l m} {A : Set l} {B0 : A → A → A → Set m} (h0 : (x y z : A) -> prop (B0 x y z)) -> prop ((x y z : A) -> B0 x y z)
propPi3 {l} {m} {A} {B0} h0 = propPi2 p0
  where 
    p0 : (a b : A) -> prop ((c : A) -> B0 a b c)
    p0 a b = propPi (h0 a b)



