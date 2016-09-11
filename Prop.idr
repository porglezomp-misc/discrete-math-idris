module Prop

%default total
%access public export

||| The type of logical propositions
|||
||| Propositions must be either true or false. Because of this, Prop is
||| isomorphic to Bool. I provide it simply to introduce a semantic distinction.
data Prop : Type where
  ||| Propositional truth, a tautology
  T : Prop
  ||| Propositional falsehood, unsatisfiable
  F : Prop

%name Prop p,q,r,s,t,u,v

infixl 3 /\
infixl 3 \/
infix 2 :->
infix 2 <->

-- Operators for building compound propositions

||| Logical negation
not : Prop -> Prop
not T = F
not F = T

||| Logical conjunction (and), true only when both arguments are true
(/\) : Prop -> Prop -> Prop
(/\) F _ = F
(/\) T q = q

||| Logical disjunction (or), true if either argument is true
(\/) : Prop -> Prop -> Prop
(\/) F q = q
(\/) T _ = T

||| Logical implication, false in the case that F :-> T
(:->) : Prop -> Prop -> Prop
(:->) F _ = T
(:->) T q = q

||| Bidirectional implication, true when T <-> T and F <-> F
(<->) : Prop -> Prop -> Prop
(<->) T q = q
(<->) F q = not q

||| DeMorgan's law applied to the negation of a conjunction
deMorganAnd : (p : Prop) -> (q : Prop) -> not (p /\ q) = not p \/ not q
deMorganAnd F _ = Refl
deMorganAnd T _ = Refl

||| DeMorgan's law applied to the negation of a disjunction
deMorganOr : (p : Prop) -> (q : Prop) -> not (p \/ q) = not p /\ not q
deMorganOr F _ = Refl
deMorganOr T _ = Refl

||| The associative property of conjunctions
associativeAnd : (p : Prop) -> (q : Prop) -> (r : Prop) -> (p /\ q) /\ r = p /\ (q /\ r)
associativeAnd T _ _ = Refl
associativeAnd F _ _ = Refl

||| The associative property of disjunctions
associativeOr : (p : Prop) -> (q : Prop) -> (r : Prop) -> (p \/ q) \/ r = p \/ (q \/ r)
associativeOr F _ _ = Refl
associativeOr T _ _ = Refl

||| The commutative property of conjunctions
commutativeAnd : (p : Prop) -> (q : Prop) -> p /\ q = q /\ p
commutativeAnd T T = Refl
commutativeAnd T F = Refl
commutativeAnd F T = Refl
commutativeAnd F F = Refl

||| The commutative property of disjunctions
commutativeOr : (p : Prop) -> (q : Prop) -> p \/ q = q \/ p
commutativeOr T T = Refl
commutativeOr T F = Refl
commutativeOr F T = Refl
commutativeOr F F = Refl

||| The property that not (not p) is the same as p
doubleNegation : (p : Prop) -> not $ not p = p
doubleNegation T = Refl
doubleNegation F = Refl

||| Or distributes over and
distributeOverAnd : (p : Prop) -> (q : Prop) -> (r : Prop)
-> p \/ (q /\ r) = (p \/ q) /\ (p \/ r)
distributeOverAnd T _ _ = Refl
distributeOverAnd F _ _ = Refl

||| And distributes over or
distributeOverOr : (p : Prop) -> (q : Prop) -> (r : Prop)
  -> p /\ (q \/ r) = (p /\ q) \/ (p /\ r)
distributeOverOr T _ _ = Refl
distributeOverOr F _ _ = Refl

||| p and (not p) can't be true at the same time, so this eliminates to false
negateAnd : (p : Prop) -> not p /\ p = F
negateAnd T = Refl
negateAnd F = Refl

||| Either p or (not p) must be true, so this elimitates to true
negateOr : (p : Prop) -> not p \/ p = T
negateOr T = Refl
negateOr F = Refl

||| If we know that false is involved in a conjunction, the other argument is
||| irrelevent
dominateAnd : (p : Prop) -> p /\ F = F
dominateAnd T = Refl
dominateAnd F = Refl

||| If we know that true is involved in a disjunction, the other argument is
||| irrelevent
dominateOr : (p : Prop) -> p \/ T = T
dominateOr T = Refl
dominateOr F = Refl

||| True is the identity element for conjunctions
idAnd : (p : Prop) -> p /\ T = p
idAnd T = Refl
idAnd F = Refl

||| False is the identity element for disjunctions
idOr : (p : Prop) -> p \/ F = p
idOr T = Refl
idOr F = Refl

||| This lets you simplify proofs containing bidirectional implication into ones
||| containing single implicaations
biconditionalToConditional : (p : Prop) -> (q : Prop)
  -> p <-> q = (p :-> q) /\ (q :-> p)
biconditionalToConditional T T = Refl
biconditionalToConditional T F = Refl
biconditionalToConditional F T = Refl
biconditionalToConditional F F = Refl

||| This lets you simplify proofs containing implication into ones containing or
implicationToOr : (p : Prop) -> (q : Prop) -> p :-> q = not p \/ q
implicationToOr F _ = Refl
implicationToOr T _ = Refl
