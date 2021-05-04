(** * Main Results *)

From HoTT Require Import HoTT.

From Sierpinski Require Import Sierpinski Ordinals.

Definition AC :=
  forall (X Y : hSet) (R : X -> Y -> hProp), (forall x, hexists (R x)) -> hexists (fun f => forall x, R x (f x)).

Open Scope type.

Lemma ordinal_has_minimal_hsolutions {LEM : ExcludedMiddle} (A : Ordinal) (P : A -> hProp) :
  merely (exists a, P a) -> merely (exists a, P a /\ forall b, P b -> a < b \/ a = b).
Proof.
  intros H'. eapply merely_destruct; try apply H'.
  intros [a Ha]. induction (well_foundedness a) as [a _ IH].
  destruct (SEM (merely (exists b, P b /\ b < a))) as [H|H].
  - eapply merely_destruct; try apply H. intros [b Hb]. apply (IH b); apply Hb.
  - apply tr. exists a. split; try apply Ha. intros b Hb.
    specialize (trichotomy_ordinal a b). intros H1.
    eapply merely_destruct; try apply H1.
    intros [H2|H2]. { apply tr. now left. }
    eapply merely_destruct; try apply H2.
    intros [H3|H3]. { apply tr. now right. }
    apply Empty_rec, H, tr. exists b. now split.
Qed.

Lemma WO_AC {LEM : ExcludedMiddle} :
  (forall (X : hSet), hexists (fun (A : Ordinal) => hinject X A)) -> AC.
Proof.
  intros H X Y R HR. specialize (H Y).
  eapply merely_destruct; try apply H.
  intros [A HA]. eapply merely_destruct; try apply HA.
  intros [f Hf]. apply tr. unshelve eexists.
  - intros x. assert (HR' : hexists (fun y => merely (R x y * forall y', R x y' -> f y < f y' \/ f y = f y'))).
    + pose proof (HAR := ordinal_has_minimal_hsolutions A (fun a => BuildhProp (merely (exists y, f y = a /\ R x y)))).
      eapply merely_destruct; try apply HAR.
      * eapply merely_destruct; try apply (HR x). intros [y Hy].
        apply tr. exists (f y). apply tr. exists y. now split.
      * intros [a [H1 H2]]. eapply merely_destruct; try apply H1.
        intros [y [<- Hy]]. apply tr. exists y. apply tr. split; trivial.
        intros y' Hy'. apply H2. apply tr. exists y'. split; trivial.
    + apply UC in HR' as [y Hy]; try exact y. intros y y' Hy Hy'.
      eapply merely_destruct; try apply Hy. intros [H1 H2].
      eapply merely_destruct; try apply Hy'. intros [H3 H4]. apply Hf.
      eapply merely_destruct; try apply (H2 y'); trivial. intros [H5|H5]; trivial.
      eapply merely_destruct; try apply (H4 y); trivial. intros [H6| -> ]; trivial.
      apply Empty_rec. apply (irreflexive_ordinal_relation _ _ _ (f y)).
      eapply ordinal_transitivity; eauto.
  - intros x. cbn. destruct UC as [y Hy]. eapply merely_destruct; try apply Hy. now intros [].
Qed.


Theorem GCH_LEM :
  GCH -> ExcludedMiddle.
Proof.
Admitted.

Parameter hartogs_number : hSet@{i} -> Ordinal@{i _}.     

Theorem GCH_AC {UA : Univalence} {PR : PropResizing} :
  GCH -> AC.
Proof.
  intros gch. assert (LEM : ExcludedMiddle). { now apply GCH_LEM. }
  apply WO_AC. intros X. apply tr. exists (hartogs_number (BuildhSet (BuildhSet (nat + X) -> hProp))).
  apply (@Sierpinski UA LEM PR (fun X => hartogs_number X) _ 3 _ X gch).
