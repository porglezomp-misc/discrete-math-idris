import Prop

commutativeLemma : (p : Prop) -> (q : Prop) -> (r : Prop) -> (s : Prop)
  -> p \/ q \/ (r \/ s) = p \/ r \/ (q \/ s)
commutativeLemma T _ _ _ = Refl
commutativeLemma F p q r =
  rewrite sym $ associativeOr p q r in
  rewrite commutativeOr p q in
  rewrite associativeOr q p r in
  Refl

problem30 : (p : Prop) -> (q : Prop) -> (r : Prop)
  -> (p \/ q) /\ (not p \/ r) :-> (q \/ r) = T
problem30 p q r =
  rewrite implicationToOr ((p \/ q) /\ (not p \/ r)) (q \/ r) in
  rewrite deMorganAnd (p \/ q) (not p \/ r) in
  rewrite deMorganOr (not p) r in
  rewrite doubleNegation p in
  rewrite deMorganOr p q in
  rewrite commutativeLemma (not p /\ not q) (p /\ not r) q r in
  rewrite commutativeOr (not p /\ not q) q in
  rewrite distributeOverAnd q (not p) (not q) in
  rewrite commutativeOr q (not q) in
  rewrite negateOr q in
  rewrite commutativeOr (p /\ not r) r in
  rewrite distributeOverAnd r p (not r) in
  rewrite commutativeOr r (not r) in
  rewrite negateOr r in
  rewrite idAnd (q \/ not p) in
  rewrite idAnd (r \/ p) in
  rewrite commutativeLemma q (not p) r p in
  rewrite negateOr p in
  rewrite associativeOr q r T in
  rewrite dominateOr r in
  rewrite dominateOr q in
  Refl
