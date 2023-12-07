From Coq Require Import Setoids.Setoid.

From LF Require Export axioms.

(* Going to stick with 2D geometry *)
Module Flat. 

(* My 2D plane with the assumption that all points and lines in this module are on it *)
Parameter MPlane : Plane.

Axiom mplane_point : forall (P : Point),
  LiesOnPp P MPlane.

Axiom mplane_line : forall (L : Line),
  LiesOnLp L MPlane.

(* Some of these proofs following sketches from https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1354311965&disposition=inline *)

(* Two distinct lines intersect at only one point *)
Theorem unique_intersection : forall (L1 L2 : Line) (P1 P2 : Point),
  P1 <> P2 ->
  LiesOnPL P1 L1 /\ LiesOnPL P1 L2 ->
  LiesOnPL P2 L1 /\ LiesOnPL P2 L2 ->
  L1 = L2.
Proof.
  intros L1 L2 P1 P2 Hneq [H11 H12] [H21 H22].
  specialize (equivalent_line P2 P1 L1 L2) as Heq.
  apply Heq; auto.
Qed.

Lemma lines_not_equivalent : forall (L1 L2 : Line) (P : Point),
  LiesOnPL P L1 ->
  ~ LiesOnPL P L2 -> 
  L1 <> L2.
Proof.
  intros.
  destruct (excluded_middle (L1 = L2)).
  - rewrite <- H1 in H0. contradiction.
  - assumption.
Qed.

Lemma neq_lines_exists_point : forall (L1 L2 : Line),
  L1 <> L2 ->
  exists P, LiesOnPL P L1 /\ ~ LiesOnPL P L2.
Proof.
  intros.
  specialize (two_points_on_line L1) as HL1.
  destruct HL1 as [A [B [Hneq [HA HB]]]].
  destruct (excluded_middle (LiesOnPL A L2)).
  - destruct (excluded_middle (LiesOnPL B L2)).
    * specialize (unique_intersection L1 L2 A B) as HUI. apply HUI in Hneq; auto. contradiction.
    * exists B. auto.
  - exists A. auto.
Qed.

(* Defining this equivalence relation for proving plane separation *)
Definition same_side (A B : Point) (L : Line) : Prop :=
  (A = B \/ (~ exists P, LiesOnPL P L /\ Between A P B)).

Theorem same_side_reflexive : forall (A : Point) (L : Line),
  same_side A A L.
Proof.
  intros. unfold same_side.
  left. reflexivity.
Qed.

Theorem same_side_symmetric : forall (A B : Point) (L : Line),
  same_side A B L -> same_side B A L.
Proof.
  intros. unfold same_side.
  destruct H as [H1 | H2].
  - left. symmetry. assumption.
  - right. unfold not in *.
    intros. destruct H. apply H2.
    exists x. destruct H. apply between_rev in H0. split; assumption.
Qed.

Theorem same_side_transitive : forall (A B C : Point) (L : Line),
  distinct3 A B C ->
  ~ LiesOnPL A L ->
  ~ LiesOnPL B L ->
  ~ LiesOnPL C L ->
  same_side A B L ->
  same_side B C L ->
  same_side A C L.
Proof.
  intros A B C L HD HAL HBL HCL HAB HBC.
  specialize (excluded_middle (exists L', LiesOnPL A L' /\ LiesOnPL B L' /\ LiesOnPL C L')) as case.
  destruct case.
  - destruct H as [I HI].
    specialize (lines_not_equivalent I L A) as Hneq.
    destruct HI as [HAI [HBI HCI]].
    pose proof (Hneq HAI HAL) as Hneq.
    specialize (neq_lines_exists_point L I) as HP.
    apply not_eq_sym in Hneq. apply HP in Hneq.
    destruct Hneq as [D HPD]. 
    specialize (exists_line A D) as HAD.
    assert (A <> D) as HneqAD.
    { destruct (excluded_middle (A = D)).
      * rewrite H in HAI. destruct HPD. contradiction.
      * assumption. }
    apply HAD in HneqAD as HADL. clear HAD. destruct HADL as [AD [HAAD HDAD]].
    specialize (exists_point_between_line D A) as HEDA.
    apply not_eq_sym in HneqAD. apply HEDA in HneqAD as HE.
    destruct HE as [E HE].
    specialize (between_line D A E) as HDAEbtwn. apply HDAEbtwn in HE as HLE.
    destruct HLE as [[EL HEL] HDAED]. destruct HEL as [HDEL [HAEL HEEL]].
    assert (EL = AD).
    {
      apply (equivalent_line D A EL AD); auto.
    }
    subst.
    specialize (only_one_between D A E) as only_one. apply only_one in HE as Hnbtw.
    assert (same_side E A L).
    { 
      unfold same_side. right.
      unfold not. intros. destruct H as [P [contra HPbtwn]].
      specialize (between_line E P A) as HEPAbtwn. apply HEPAbtwn in HPbtwn as HL.
      destruct HL as [[SL HSL] HLD]. 
      assert (SL = AD).
      {
        apply (equivalent_line E A SL AD); auto.
        - unfold distinct3 in HLD. intuition.
        - intuition.
        - intuition.
      }
      subst. admit.
      (* find contradiction showing that L is the same as AD, using equivalent_line an P D*)
    } admit.
  - destruct (excluded_middle (same_side A C L)).
    * assumption.
    * specialize (pasch A C B L MPlane) as Hpasch. 
      unfold same_side in H0. destruct H0. right. unfold not. intros.
      unfold distinct3 in *. assert (A <> C /\ C <> B /\ B <> A) as HD2. { intuition. } apply Hpasch in HD2; auto.
      + destruct HD2.
        -- unfold same_side in HBC. destruct HBC.
           ** intuition.
           ** apply H2. destruct H1. exists x. destruct H1. apply between_rev in H3. split; assumption.
        -- unfold same_side in HAB. destruct HAB.
           ** intuition.
           ** apply H2. destruct H1. exists x. destruct H1. split; assumption.
      + unfold not. intros. apply H. destruct H1. exists x. intuition.
      + apply (mplane_line L).
Admitted.

(* Shows that there are only two equivalence classes for this relation, so line divides plane into two sides *)
Theorem plane_separation : forall (A B C : Point) (L : Line),
  ~ LiesOnPL A L ->
  ~ LiesOnPL B L ->
  ~ LiesOnPL C L ->
  ~ same_side A C L ->
  ~ same_side B C L ->
  same_side A B L.


End Flat.