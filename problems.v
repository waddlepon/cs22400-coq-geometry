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
  LiesOnPL P1 L1 -> LiesOnPL P1 L2 ->
  LiesOnPL P2 L1 -> LiesOnPL P2 L2 ->
  L1 = L2.
Proof.
  intros L1 L2 P1 P2 Hneq H11 H12 H21 H22.
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

Lemma points_not_equivalent : forall (P1 P2 : Point) (L : Line),
  LiesOnPL P1 L ->
  ~LiesOnPL P2 L ->
  P1 <> P2.
Proof.
  intros.
  destruct (excluded_middle (P1 = P2)).
  - subst. contradiction.
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

Lemma no_line_connects : forall (A B C : Point) (L : Line),
  A <> B ->
  LiesOnPL A L ->
  LiesOnPL B L ->
  ~LiesOnPL C L ->
  ~ exists L', LiesOnPL A L' /\ LiesOnPL B L' /\ LiesOnPL C L'.
Proof.
  intros A B C L HD HA HB HNC.
  unfold not. intros.
  destruct H as [L' [HAL' [HBL' HCL']]].
  assert (L = L').
  { 
    specialize (equivalent_line A B L L') as HLL.
    apply HLL in HD; auto.
  }
  subst. contradiction.
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

(* Copied out the case here to make it more usable, proof is not that readable since I didn't fix the hypotheses name *)
Lemma same_side_transitive_case1 : forall (A B C : Point) (L : Line),
  (~exists L', LiesOnPL A L' /\ LiesOnPL B L' /\ LiesOnPL C L') ->
  distinct3 A B C ->
  ~ LiesOnPL A L ->
  ~ LiesOnPL B L ->
  ~ LiesOnPL C L ->
  same_side A B L ->
  same_side B C L ->
  same_side A C L.
Proof.
  intros.
  destruct (excluded_middle (same_side A C L)).
  - assumption.
  - specialize (pasch A C B L MPlane) as Hpasch. 
    unfold same_side in H6. destruct H6. right. unfold not. intros.
    unfold distinct3 in *. assert (A <> C /\ C <> B /\ B <> A) as HD2. { intuition. } apply Hpasch in HD2; auto.
    * destruct HD2.
      + unfold same_side in H5. destruct H5.
        -- intuition.
        -- apply H5. destruct H7. exists x. destruct H7. apply between_rev in H8. split; assumption.
      + unfold same_side in H4. destruct H4.
        -- intuition.
        -- apply H4. destruct H7. exists x. destruct H7. split; assumption.
    * unfold not. intros. apply H. destruct H7. exists x. intuition.
    * apply (mplane_line L). 
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
      subst.
      specialize (equivalent_line P D L AD) as HeqLAD.
      assert (P <> D).
      {
        destruct (excluded_middle (P = D)).
        - subst. apply between_rev in HPbtwn. destruct Hnbtw. contradiction.
        - assumption. 
      }
      apply HeqLAD in H; auto.
      * subst. contradiction.
      * destruct HPD. assumption.
      * destruct HSL. destruct H1. assumption.
    }
    assert (~LiesOnPL E I).
    {
      destruct (excluded_middle (LiesOnPL E I)).
      - specialize (unique_intersection I AD A E) as Hunq.
        unfold distinct3 in HDAED.
        destruct HDAED. destruct H2. apply Hunq in H2; auto. subst. destruct HPD. contradiction.
      - assumption.
    }
    assert (~LiesOnPL E L) as HEnL.
    {
      destruct (excluded_middle (LiesOnPL E L)).
      - assert (L = AD).
        {
          apply (unique_intersection L AD D E); auto.
          - unfold distinct3 in HDAED. intuition.
          - intuition.
        }
        subst. contradiction.
      - assumption.
    }
    assert (same_side E B L) as HEB.
    {
      specialize (no_line_connects A B E I) as HNLC.
      unfold distinct3 in HD. destruct HD. apply HNLC in H1 as HN; auto.
      apply (same_side_transitive_case1 E A B L); auto.
      - unfold not. intros. apply HN. destruct H3. exists x. destruct H3. destruct H4. split; auto.
      - unfold distinct3 in *. split.
        * intuition.
        * split.
          + assumption.
          + apply (points_not_equivalent B E I); auto.
    }
    assert (same_side E C L) as HEC.
    {
      specialize (no_line_connects B C E I) as HNLC.
      unfold distinct3 in HD. destruct HD. destruct H2. apply HNLC in H2 as HN; auto.
      apply (same_side_transitive_case1 E B C L); auto.
      - unfold not. intros. apply HN. destruct H4. exists x. intuition.
      - unfold distinct3 in *. split.
        * specialize (points_not_equivalent B E I); auto.
        * split.
          + intuition.
          + apply (points_not_equivalent C E I); auto.
    }
    specialize (no_line_connects A C E I) as HNLC.
    unfold distinct3 in HD. destruct HD. destruct H2. apply not_eq_sym in H3. apply HNLC in H3 as HN; auto.
    apply (same_side_transitive_case1 A E C L); auto.
    * unfold not. intros. apply HN. destruct H4. exists x. intuition.
    * unfold distinct3 in *. split.
      + intuition.
      + split.
        -- specialize (points_not_equivalent C E I); auto.
        -- intuition.
    * apply same_side_symmetric in H. assumption.
  - apply (same_side_transitive_case1 A B C L); auto.
Qed.

(* Shows that there are at least two equivalence classes for this relation *)
Theorem plane_separation_at_least_two : forall (L : Line),
  exists A B, ~LiesOnPL A L /\ ~LiesOnPL B L /\ ~same_side A B L.
Proof.
  intros.
  specialize (three_points_not_on_line L) as HP.
  destruct HP as [A [B [C [Hdistinct [HA [HB HC]]]]]].
  clear HB HC Hdistinct B C.
  specialize (two_points_on_line L) as HP.
  destruct HP as [D [E [Hneq [HD HE]]]].
  clear Hneq HE E.
  specialize (exists_point_between_line A D) as Hb.
  assert (A <> D).
  {
    specialize (points_not_equivalent D A L) as HDAneq.
    apply HDAneq in HD; auto.
  }
  apply Hb in H. destruct H as [B HB].
  exists A, B.
  split.
  - assumption.
  - split.
    * destruct (excluded_middle (LiesOnPL B L)).
      + apply between_line in HB. destruct HB as [HL Hdistinct].
        destruct HL as [L' [HAL' [HDL' HBL']]].
        assert (L = L').
        {
          apply (equivalent_line D B L L'); auto.
          - unfold distinct3 in Hdistinct. intuition.
        }
        subst. contradiction.
      + assumption.
    * unfold same_side. unfold not. intros. destruct H.
      + apply between_line in HB. destruct HB as [HL Hdistinct]. unfold distinct3 in Hdistinct. intuition.
      + apply H. exists D. split; auto.
Qed.

(* Shows that there are at most two equivalence classes for this relation *)
Theorem plane_separation_only_two : forall (A B C : Point) (L : Line),
  ~ LiesOnPL A L ->
  ~ LiesOnPL B L ->
  ~ LiesOnPL C L ->
  ~ same_side A C L ->
  ~ same_side B C L ->
  same_side A B L.
Proof.
  intros A B C L HA HB HC HAC HBC.
  Admitted.

(* Together the above two theorems show that there are only
   two equivalence classes for this relation(for points not on the line)
   and therefore the line separates the plane *)

End Flat.