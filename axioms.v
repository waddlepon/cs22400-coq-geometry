(* Hilbert's Axioms, based off of https://en.wikipedia.org/wiki/Hilbert%27s_axioms *)

(* TODO: figure out point/line/plane equivalence since there are no objects *)

Inductive Point : Type :=
.

Inductive Line : Type :=
.

Inductive Plane : Type :=
.

Inductive LiesOnPL : Point -> Line -> Prop :=
.

Inductive LiesOnPp : Point -> Plane -> Prop :=
.

Inductive LiesOnLp : Line -> Plane -> Prop :=
.

Definition distinct3 (A B C : Point) : Prop :=
  A <> B /\ B <> C /\ C <> A.

(* I Incidence *)
(* I1 *)
Axiom exists_line : forall (A B : Point),
  A <> B -> exists L, LiesOnPL A L /\ LiesOnPL B L.

(* I2 TODO: instead of = maybe use an equivalence relation?? *)
Axiom equivalent_line : forall (A B C : Point) (L M : Line),
  B <> C -> LiesOnPL A L -> LiesOnPL B L -> LiesOnPL A M -> LiesOnPL C M -> L = M.

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
(* II1 *)
Inductive Between : Point -> Point -> Point -> Prop :=
| between_rev (A B C : Point) : Between A B C -> Between C B A.

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
Inductive CongruentLS : Point -> Point -> Point -> Point -> Prop :=
| congruentls_refl (A B : Point) : CongruentLS A B A B
| congruentls_equiv (A B A' B' : Point) : CongruentLS A B A' B' -> CongruentLS A' B' A B
(* III2 *)
| congruentls_trans (A B A' B' A'' B'' : Point) : CongruentLS A B A' B' -> CongruentLS A B A'' B'' -> CongruentLS A' B' A'' B''
.

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
Inductive CongruentA : Point -> Point -> Point -> Point -> Point -> Point -> Prop :=
| congruenta_refl (A B C : Point) : CongruentA A B C A B C
| congruenta_equiv (A B C A' B' C' : Point) : CongruentA A B C A' B' C' -> CongruentA A' B' C' A B C
| congruenta_flip (A B C : Point) : CongruentA A B C C B A
(* III5 *)
| congruenta_trans (A B C A' B' C' A'' B'' C'' : Point) : CongruentA A B C A' B' C' -> CongruentA A B C A'' B'' C'' -> CongruentA A' B' C' A'' B'' C''
.

(* III4 *)