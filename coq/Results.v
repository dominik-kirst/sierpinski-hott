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

Section LEM.

  Variable X : hSet.
  Variable P : hProp.

  Context {PR : PropResizing}.
  Context {FE : Funext}.

  Definition hpaths (x y : X) :=
    BuildhProp (paths x y).

  Definition sing (p : X -> hProp) :=
    exists x, p = hpaths x.

  Definition Y :=
    { p : X -> hProp | sing p \/ (P + ~ P) }.

  Lemma Cantor_inj :
    ~ inject (X -> hProp) X.
  Proof.
    intros [i HI]. pose (p n := BuildhProp (resize_hprop (forall q, i q = n -> ~ q n))).
    enough (Hp : p (i p) <-> ~ p (i p)).
    { apply Hp; apply Hp; intros H; now apply Hp. }
    unfold p at 1. split.
    - intros H. apply equiv_resize_hprop in H. apply H. reflexivity.
    - intros H. apply equiv_resize_hprop. intros q -> % HI. apply H.
  Qed.

  Lemma Cantor_sing (i : (X -> hProp) -> (X -> hProp)) :
    IsInjective i -> exists p, ~ sing (i p).
  Proof.
    intros HI. pose (p n := BuildhProp (resize_hprop (forall q, i q = hpaths n -> ~ q n))).
    exists p. intros [n HN]. enough (Hp : p n <-> ~ p n).
    { apply Hp; apply Hp; intros H; now apply Hp. }
    unfold p at 1. split.
    - intros H. apply equiv_resize_hprop in H. apply H, HN.
    - intros H. apply equiv_resize_hprop. intros q HQ. rewrite <- HN in HQ. now apply HI in HQ as ->.
  Qed.

  Lemma sig_inj {Z} (r : Z -> hProp) :
    IsInjective (@proj1 Z r).
  Proof.
    intros [p Hp] [q Hq]; cbn.
    intros ->. unshelve eapply path_sigma; cbn.
    - reflexivity.
    - cbn. apply (r q).
  Qed.

  Lemma Y_inj :
    (P + ~ P) -> inject (X -> hProp) Y.
  Proof.
    intros HP. unshelve eexists.
    - intros p. exists p. apply tr. now right.
    - intros p q. intros H. change p with ((exist (fun r => sing r \/ (P + ~ P)) p (tr (inr HP))).1).
      rewrite H. cbn. reflexivity.
  Qed.

  Lemma IsInjective_trans {X' Y Z} (f : X' -> Y) (g : Y -> Z) :
    IsInjective f -> IsInjective g -> IsInjective (fun x => g (f x)).
  Proof.
    intros HF HG x y H. now apply HF, HG.
  Qed.

  Theorem CH_LEM :
    (inject X Y -> inject Y (X -> hProp) -> ~ (inject Y X) -> hinject (X -> hProp) Y) -> P \/ ~ P.
  Proof.
    intros ch. eapply merely_destruct; try apply ch.
    - unshelve eexists.
      + intros x. exists (hpaths x). apply tr. left. exists x. reflexivity.
      + intros x y. intros H % pr1_path. cbn in H. change (hpaths x y). now rewrite H.
    - exists (@proj1 _ _). now apply sig_inj.
    - intros H. assert (HP' : ~ ~ (P + ~ P)).
      { intros HP. apply HP. right. intros p. apply HP. now left. }
      apply HP'. intros HP % Y_inj. clear HP'.
      apply Cantor_inj. now apply (inject_trans HP).
    - intros [i Hi]. destruct (Cantor_sing (fun p => @proj1 _ _ (i p))) as [p HP].
      + apply IsInjective_trans; trivial. now apply sig_inj.
      + destruct (i p) as [q Hq]; cbn in *.
        eapply merely_destruct; try apply Hq.
        intros [H|H]; try now apply tr.
  Qed.

End LEM.

Theorem GCH_LEM {PR : PropResizing} {UA : Univalence} :
  GCH -> (forall P : hProp, P \/ ~ P).
Proof.
  intros gch P. eapply (CH_LEM (BuildhSet nat)); try exact _. intros H1 H2 H3.
  destruct (gch (BuildhSet nat) (BuildhSet (Y (BuildhSet nat) P))) as [H|H].
  - cbn. exists idmap. apply isinj_idmap.
  - apply tr. apply H1.
  - apply tr. apply H2.
  - apply Empty_rec. eapply merely_destruct; try apply H. apply H3.
  - apply H.
Qed.

Instance hProp_impred {FE : Funext} X (F : X -> Type) :
  (forall x, IsHProp (F x)) -> IsHProp (forall x, F x).
Proof.
  intros H. apply hprop_allpath. intros f g.
  apply path_forall. intros x. apply H.
Qed.

Lemma GCH_hProp {PR : PropResizing} {FE : Funext} :
  IsHProp GCH.
Proof.
  repeat (apply hProp_impred; intros).
  apply hprop_allpath. intros [H|H] [H'|H'].
  - enough (H = H') as ->; trivial. apply (hinject x0 x).
  - apply Empty_rec. eapply merely_destruct; try eapply (Cantor_inj x); trivial. now apply hinject_trans with x0.
  - apply Empty_rec. eapply merely_destruct; try eapply (Cantor_inj x); trivial. now apply hinject_trans with x0.
  - enough (H = H') as ->; trivial. apply (hinject (x -> hProp) x0).
Qed.

Parameter HN : hSet -> Ordinal.
Hypothesis HN_ninject : forall X, ~ hinject (HN X) X.
Hypothesis HN_inject : forall X, hinject (HN X) (powit X 3).

Theorem GCH_AC' {UA : Univalence} {PR : PropResizing} {LEM : ExcludedMiddle} :
  GCH -> AC.
Proof.
  intros gch.
  apply WO_AC. intros X. apply tr. exists (HN (BuildhSet (BuildhSet (nat + X) -> hProp))).
  eapply (@Sierpinski UA LEM PR HN HN_ninject 3 HN_inject X gch).
Qed.

Theorem GCH_AC {UA : Univalence} {PR : PropResizing} {LEM : ExcludedMiddle} :
  GCH -> AC.
Proof.
  intros gch.
  apply WO_AC. intros X. apply tr. exists (hartogs_number (BuildhSet (BuildhSet (nat + X) -> hProp))).
  unshelve eapply (@Sierpinski UA LEM PR hartogs_number _ 3 _ X gch).
  - admit.
  - intros Y. apply tr. apply hartogs_number_injection.
Qed.
