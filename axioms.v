(* Hilbert's Axioms, based off of https://en.wikipedia.org/wiki/Hilbert%27s_axioms *)

Parameter Point : Set.

Parameter Line : Set.

Parameter Plane : Set.

Parameter LiesOnPL : Point -> Line -> Prop.

Parameter LiesOnPp : Point -> Plane -> Prop.

Parameter LiesOnLp : Line -> Plane -> Prop.

Definition distinct3 (A B C : Point) : Prop :=
  A <> B /\ B <> C /\ C <> A.

(* I will be using this to make my life easier, would probably be better to only axiomatize _certain_ things as decidable *)
Axiom excluded_middle : forall (P : Prop),
  P \/ ~P.

(* I Incidence *)
(* I1 *)
Axiom exists_line : forall (A B : Point),
  A <> B -> exists L, LiesOnPL A L /\ LiesOnPL B L.

(* I2 TODO: instead of = maybe use an equivalence relation?? *)
Axiom equivalent_line : forall (A B : Point) (L M : Line),
  A <> B -> LiesOnPL A L -> LiesOnPL B L -> LiesOnPL A M -> LiesOnPL B M -> L = M.

(* I3 *)
Axiom two_points_on_line : forall (L : Line),
  exists A B, A <> B /\ LiesOnPL A L /\ LiesOnPL B L.

Axiom three_points_not_on_line : forall (L : Line),
  exists A B C, distinct3 A B C /\ ~ LiesOnPL A L /\ ~ LiesOnPL B L /\ ~ LiesOnPL C L.

(* I4 *)
Axiom exists_plane : forall (A B C : Point),
  distinct3 A B C ->
  (~ exists L, LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPL C L) ->
  exists p, LiesOnPp A p /\ LiesOnPp B p /\ LiesOnPp C p.

Axiom point_on_plane : forall (p : Plane),
  exists A, LiesOnPp A p.

(* I5 *)
Axiom equivalent_plane : forall (A B C : Point) (p o : Plane),
  (~ exists L, LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPL C L) ->
  LiesOnPp A p -> LiesOnPp B p -> LiesOnPp C p ->
  LiesOnPp A o -> LiesOnPp B o -> LiesOnPp C o ->
  p = o.

(* I6 *)
Axiom line_on_plane : forall (L : Line) (p : Plane),
  (exists A B, A <> B /\ LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPp A p /\ LiesOnPp B p) ->
  LiesOnLp L p.

Axiom all_points_line_on_plane : forall (L : Line) (p : Plane),
  LiesOnLp L p -> (forall P, LiesOnPL P L -> LiesOnPp P p).

(* I7 *)
Axiom plane_intersection : forall (A : Point) (p o : Plane),
  LiesOnPp A p -> LiesOnPp A o ->
  (exists B, A <> B /\ LiesOnPp B p /\ LiesOnPp B o).

(* I8 TODO: make distinctness easy *)
Axiom four_points_on_plane : forall (p : Plane),
  exists A B C D, A <> B /\ B <> C /\ C <> D /\ D <> A /\ A <> C /\ B <> D /\
  LiesOnPp A p /\ LiesOnPp B p /\ LiesOnPp C p /\ LiesOnPp D p.

(* II Order *)
Parameter Between : Point -> Point -> Point -> Prop.

(* II1 *)
Axiom between_rev : forall (A B C : Point),
  Between A B C -> Between C B A.

Axiom between_line : forall (A B C : Point),
  Between A B C ->
  (exists L, LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPL C L) /\ distinct3 A B C.

(* II2 *)
Axiom exists_point_between_line : forall (A C : Point),
  A <> C ->
  exists B, Between A C B.

(* II3 *)
Axiom only_one_between : forall (A B C : Point),
  Between A B C ->
  ~ Between B A C /\ ~ Between A C B.

(* II4 *)
Axiom pasch : forall (A B C : Point) (L : Line) (p : Plane),
  distinct3 A B C ->
  (~ exists L, LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPL C L) ->
  LiesOnLp L p ->
  ~ LiesOnPL A L -> ~ LiesOnPL B L -> ~ LiesOnPL C L ->
  (exists P, LiesOnPL P L /\ Between A P B) ->
  (exists P, LiesOnPL P L /\ Between B P C) \/ (exists P, LiesOnPL P L /\ Between A P C).

(* III Congruence *)
(* Congruence for line segments *)
Parameter CongruentLS : Point -> Point -> Point -> Point -> Prop.

Axiom congruentls_refl : forall (A B : Point),
  CongruentLS A B A B.

Axiom congruentls_equiv : forall (A B A' B' : Point),
  CongruentLS A B A' B' -> CongruentLS A' B' A B.

(* III2 *)
Axiom congruentls_trans : forall (A B A' B' A'' B'' : Point),
  CongruentLS A B A' B' -> CongruentLS A B A'' B'' -> CongruentLS A' B' A'' B''.

(* III1 *)
Axiom exists_congruent_line_segment : forall (A B A' Side : Point) (L : Line),
  A <> B ->
  LiesOnPL A' L ->
  Side <> A' ->
  LiesOnPL Side L ->
  exists B', LiesOnPL B' L /\ CongruentLS A B A' B' /\ (Between A' B' Side \/ Between A' Side B' \/ B' = Side).

(* III3 *)
Axiom adding_congruent_line_segments : forall (A B C A' B' C' : Point),
  A <> B -> B <> C -> A' <> B' -> B' <> C' ->
  (exists L, LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPL C L) ->
  (~ exists P, Between A P B /\ Between B P C) ->
  (exists L, LiesOnPL A' L /\ LiesOnPL B' L /\ LiesOnPL C' L) ->
  (~ exists P, Between A' P B' /\ Between B' P C') ->
  CongruentLS A B A' B' -> CongruentLS B C B' C' ->
  CongruentLS A C A' C'.

(* Congruence for angles *)
Parameter CongruentA : Point -> Point -> Point -> Point -> Point -> Point -> Prop.

Axiom congruenta_refl : forall (A B C : Point),
  CongruentA A B C A B C.

Axiom congruenta_equiv : forall (A B C A' B' C' : Point),
  CongruentA A B C A' B' C' -> CongruentA A' B' C' A B C.

Axiom congruenta_flip : forall (A B C : Point),
  CongruentA A B C C B A.

(* III5 *)
Axiom congruenta_trans : forall (A B C A' B' C' A'' B'' C'' : Point),
  CongruentA A B C A' B' C' -> CongruentA A B C A'' B'' C'' -> CongruentA A' B' C' A'' B'' C''.

(* III4 TODO: do we need these 180 degree angle specs? *)
(* Says that all interior points of an angle are on the C side of A-Origin *)
Definition interior_points_same_side (A Origin C : Point) : Prop :=
  (* Can't be a 180 angle *)
  (~ exists L, LiesOnPL A L /\ LiesOnPL Origin L /\ LiesOnPL C L) ->
  distinct3 A Origin C ->
  forall P,
  exists L', LiesOnPL P L' /\ LiesOnPL Origin L' ->
  (exists B, LiesOnPL B L' /\ Between A B C /\ (Between Origin B P \/ Between Origin P B)) ->
  (forall AO, LiesOnPL A AO /\ LiesOnPL Origin AO -> (~ exists M, Between P M C /\ LiesOnPL M AO))
.

(* TODO: is exists! enough for uniqueness or should I add another axiom? *)
(* Kind of weird, but basically Side is a point on the side of the line A-Origin that we want our angle to be on *)
Axiom exists_congruent_angle : forall (A B C Origin H Side : Point) (p : Plane),
  distinct3 A B C ->
  (* Can't be a 180 angle, otherwise sides don't work *)
  (~ exists L, LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPL C L) ->
  Origin <> H ->
  LiesOnPp A p -> LiesOnPp B p -> LiesOnPp C p -> LiesOnPp Origin p -> LiesOnPp H p ->
  exists! K, CongruentA A B C H Origin K /\ LiesOnPp K p /\ (forall AO, LiesOnPL A AO /\ LiesOnPL Origin AO -> (~ exists M, Between K M Side /\ LiesOnPL M AO)) /\ interior_points_same_side H Origin C.
  
(* III6 *)
Axiom congruent_angles_of_triangles : forall (A B C A' B' C' : Point),
  distinct3 A B C -> (~ exists L, LiesOnPL A L /\ LiesOnPL B L /\ LiesOnPL C L) ->
  distinct3 A' B' C' -> (~ exists L, LiesOnPL A' L /\ LiesOnPL B' L /\ LiesOnPL C' L) ->
  CongruentLS A B A' B' -> CongruentLS A C A' C' -> CongruentA B A C B' A' C' ->
  CongruentA A B C A' B' C'.

(* IV Parallels*)
Definition intersect (L1 L2 : Line) : Prop :=
  exists P, LiesOnPL P L1 /\ LiesOnPL P L2.

(* IV1 *)
Axiom euclids_axiom : forall (A : Point) (L : Line) (p : Plane),
  LiesOnLp L p -> LiesOnPp A p -> ~ LiesOnPL A L ->
  exists! L', LiesOnPL A L' /\ (~ intersect L L').

(* TODO: Definitely useful for certain proofs, but hard to implement and use because of their second-order logical properties. *)
(* V Continuity *)
(* V1 TODO *)

(* V2 TODO *)