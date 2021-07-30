(* By an idea Andrew Swan brought forward in the HoTT-Zulip, the assumption that every type can be equipped with an irreflexive and extensional relation implies excluded middle, provided some mild extensionality assumptions that hold in HoTT. The result translates to Coq's type theory under the sole assumption of propositional extensionality. Also, a slight strengthening is that not full extensionality of the orders is required but only the uniqueness of minimal elements. *)

Require Import Init.Prelude.

Section WO.

  (* We first assume extensionality of propositions. *)

  Hypothesis PE : forall (P Q : Prop), (P <-> Q) -> P = Q.

  (* In Coq's type theory this implies proof irrelevance. *)

  Lemma PI (P : Prop) (H H' : P) :
    H = H'.
  Proof.
    assert (P = True) as ->.
    - apply PE. tauto.
    - destruct H, H'. reflexivity.
  Qed.

  (* Next we assume some proposition P and define the type X of propositions Q not apart from P. *)

  Variable P : Prop.

  Definition X := { Q | ~ P <> Q }.

  (* Finally we assume a relation lt on X that is irreflexive and has at most one minimum. *)

  Variable lt : X -> X -> Prop.

  Hypothesis lt_irref : forall x, ~ lt x x.
  Hypothesis lt_minunique : forall x y, (forall z, ~ lt z x) -> (forall z, ~ lt z y) -> x = y.

  (* The first lemma shows that the elements of X are not apart. *)

  Lemma X_eq' (x y : X) :
    ~ x <> y.
  Proof.
    intros H. destruct x as [Q HQ], y as [Q' HQ'].
    apply HQ. intros H1. apply HQ'. intros H2.
    apply H. rewrite H1 in H2. destruct H2. f_equal. apply PI.
  Qed.

  (* This implies that any element of X is minimal... *)

  Lemma X_min (y x : X) :
    ~ lt x y.
  Proof.
    intros H. apply (X_eq' x y). intros ->. now apply lt_irref in H.
  Qed.

  (* ...and therefore all elements of X are equal. *)

  Lemma X_eq (x y : X) :
    x = y.
  Proof.
    apply lt_minunique.
    all: apply X_min.
  Qed.

  (* This is enough to derive that P is stable under double negation. *)

  Lemma DN :
    ~ ~ P -> P.
  Proof.
    intros HDN.
    assert (HP : ~ P <> P). { intros H. now apply H. }
    assert (HT : ~ P <> True). { intros H. apply HDN. intros H'. apply H. apply PE. tauto. }
    specialize (X_eq (exist _ P HP) (exist _ True HT)). injection 1 as H. rewrite H. tauto.
  Qed.

End WO.
