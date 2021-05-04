From HoTT Require Import HoTT.


(** This file contains a definition of ordinals and some fundamental results that roughly follow the presentation in the HoTT book. Building on that, we have an incomplete definition of Hartogs numbers, including two important statements about their cardinality. The necessary steps to complete the definition are outlined at the bottom of the file. *)




(** * Well-foundedness *)

Inductive Accessible {A} (R : Lt A) (a : A) :=
acc : (forall b, b < a -> Accessible R b) -> Accessible R a.


Instance ishprop_Accessible `{Funext} {A} (R : Lt A) (a : A) :
IsHProp (Accessible R a).
Proof.
  apply hprop_allpath.
  intros acc1. induction acc1 as [a acc1' IH].
  intros [acc2']. apply ap.
  apply path_forall; intros b. apply path_forall; intros Hb.
  apply IH.
Qed.


Class WellFounded {A} (R : Relation A) :=
well_foundedness : forall a : A, Accessible R a.


Instance ishprop_WellFounded `{Funext} {A} (R : Relation A) :
IsHProp (WellFounded R).
Proof.
  apply hprop_allpath; intros H1 H2.
  apply path_forall; intros a.
  apply path_ishprop.
Qed.




(** * Extensionality *)

Class Extensional {A} (R : Lt A) :=
extensionality : forall a b : A, (forall c : A, c < a <-> c < b) -> a = b.

Instance ishprop_Extensional `{Funext} {A} `{IsHSet A} (R : Relation A)
  : IsHProp (Extensional R).
Proof. unfold Extensional. exact _. Qed.



(** * Ordinals *)

Class IsOrdinal@{carrier relation}
      (A : Type@{carrier}) (R : Relation@{carrier relation} A) :=
{ ordinal_is_hset :> IsHSet A
; ordinal_relation_is_mere :> is_mere_relation A R
; ordinal_extensionality :> Extensional R
; ordinal_well_foundedness :> WellFounded R
; ordinal_transitivity :> Transitive R
}.

Instance ishprop_IsOrdinal `{Funext} A R
  : IsHProp (IsOrdinal A R).
Proof.
  eapply trunc_equiv'. {
    issig.
  }
  unfold Transitive. exact _.
Qed.


Record Ordinal@{carrier relation +} :=
{ ordinal_carrier : Type@{carrier}
; ordinal_relation : Lt@{carrier relation} ordinal_carrier
; ordinal_property : IsOrdinal@{carrier relation} ordinal_carrier (<)
}.

Existing Instance ordinal_relation.
Existing Instance ordinal_property.

Coercion ordinal_as_hset (A : Ordinal) : hSet
  := BuildhSet (ordinal_carrier A).



Instance irreflexive_ordinal_relation A R
: IsOrdinal A R -> Irreflexive R.
Proof.
  intros is_ordinal a H.
  induction (well_foundedness a) as [a _ IH].
  apply (IH a); assumption.
Qed.


Definition TypeWithRelation
  := { A : Type & Relation A }.

Coercion ordinal_as_type_with_relation (A : Ordinal) : TypeWithRelation
  := (A : Type; (<)).




(** * Paths in Ordinal *)

Definition equiv_Ordinal_to_sig
  : Ordinal <~> { R : { A : Type & Relation A } & IsOrdinal _ R.2 }.
Proof.
  transitivity { A : Type & { R : Relation A & IsOrdinal A R } }. {
    symmetry. issig.
  }
  apply equiv_sigma_assoc'.
Defined.


Definition Isomorphism : TypeWithRelation -> TypeWithRelation -> Type
  := fun '(A; R__A) '(B; R__B) =>
       { f : A <~> B & forall a a', R__A a a' <-> R__B (f a) (f a') }.


Instance isomorphism_id : Reflexive Isomorphism.
Proof. intros A. exists equiv_idmap. cbn. intros a a'. reflexivity. Qed.

Lemma isomorphism_inverse
  : forall A B,
    Isomorphism A B ->
    Isomorphism B A.
Proof.
  intros [A R__A] [B R__B] [f H].
  exists (equiv_inverse f).
  intros b b'.
  cbn.
  rewrite <- (eisretr f b). set (a := f^-1 b). rewrite eissect.
  rewrite <- (eisretr f b'). set (a' := f^-1 b'). rewrite eissect.
  (* We don't apply the symmetry tactic because that would introduce bad universe constraints *)
  split; apply H.
Defined.


Instance transitive_iff
  : Transitive iff.
Proof.
  intros A B C A_B B_C.
  split.
  - intros a. apply B_C. apply A_B. exact a.
  - intros c. apply A_B. apply B_C. exact c.
Qed.


Lemma transitive_Isomorphism
  : forall A B C,
    Isomorphism A B
    -> Isomorphism B C
    -> Isomorphism A C.
Proof.
  intros [A R__A] [B R__B] [C R__C].
  intros [f Hf] [g Hg].
  exists (equiv_compose' g f).
  intros a a'.
  split.
  - intros a_a'. apply Hg. apply Hf. exact a_a'.
  - intros gfa_gfa'. apply Hf. apply Hg. exact gfa_gfa'.
Defined.


Instance isomorphism_compose_backwards
  : Transitive Isomorphism.
Proof.
  intros [A R__A] [B R__B] [C R__C] [f Hf] [g Hg].
  exists (equiv_compose' g f).
  intros a a'.
  transitivity (R__B (f a) (f a')). {
    apply Hf.
  }
  apply Hg.
Qed.





Definition equiv_path_Ordinal `{Univalence}
           (A B : Ordinal)
  : Isomorphism A B <~> A = B.
Proof.
  unfold Isomorphism. rapply symmetric_equiv.
  transitivity (equiv_Ordinal_to_sig A = equiv_Ordinal_to_sig B). {
    apply equiv_ap'.
  }
  transitivity ((equiv_Ordinal_to_sig A).1 = (equiv_Ordinal_to_sig B).1). {
    exists pr1_path. exact (isequiv_pr1_path_hprop _ _).
  }
  transitivity (exist Relation A (<) = exist Relation B (<)). {
    reflexivity.
  }
  transitivity { p : A = B :> Type & p # (<) = (<) }. {
    symmetry.
    exact (equiv_path_sigma Relation
                            (exist Relation A (<))
                            (exist Relation B (<))).
  }
  srapply equiv_functor_sigma'.
  - exact (equiv_equiv_path A B).
  - cbn. intros p.
    nrapply equiv_iff_hprop.
    + apply (trunc_equiv' (forall b b' : B, (p # (<)) b b' = (b < b'))). {
        transitivity (forall b : B, (p # lt) b = lt b). {
          apply equiv_functor_forall_id; intros b. apply equiv_path_arrow.
        }
        apply equiv_path_arrow.
      }
      exact _.
    + nrapply trunc_forall. { exact _. } intros a.
      nrapply trunc_forall. { exact _. } intros a'.
      nrapply trunc_prod.
      * nrapply trunc_arrow. { exact _. }
        apply ordinal_relation_is_mere.
      * nrapply trunc_arrow. { exact _. }
        apply ordinal_relation_is_mere.
    + intros <- a a'.
      rewrite transport_arrow. rewrite transport_arrow_toconst.
      repeat rewrite transport_Vp. reflexivity.
    + intros H0.
      by_extensionality b. by_extensionality b'.
      rewrite transport_arrow. rewrite transport_arrow_toconst.
      apply path_iff_ishprop_uncurried.
      specialize (H0 (transport idmap p^ b) (transport idmap p^ b')).
      repeat rewrite transport_pV in H0. exact H0.
Qed.


Lemma path_Ordinal `{Univalence}
      (A B : Ordinal)
  : forall f : A <~> B,
    (forall a a' : A, a < a' <-> f a < f a')
    -> A = B.
Proof. intros f H0. apply equiv_path_Ordinal. exists f. exact H0. Qed.


Lemma ordinal_has_minimal_solutions (A : Ordinal) (P : A -> hProp) `{ExcludedMiddle}
  : (exists a, P a) ->
    merely (exists a, P a /\ forall b, P b -> a < b \/ a = b).
Proof.
  intros [a P_a].
  induction (well_foundedness a) as [a _ IH].
Abort.


Lemma trichotomy_ordinal `{ExcludedMiddle} {A : Ordinal} (a b : A)
  : a < b \/ a = b \/ b < a.
Proof.
  revert b. induction (well_foundedness a) as [a _ IHa]. intros b.
  induction (well_foundedness b) as [b _ IHb].
  destruct (LEM (merely (exists b', b' < b /\ (a = b' \/ a < b')))) as [H1 | H1]; try exact _.
  - revert H1. rapply Trunc_rec. intros [b' [b'_b Hb']].
    revert Hb'. rapply Trunc_rec. intros [a_b' | b'_a].
    + apply tr. left. rewrite a_b'. exact b'_b.
    + apply tr. left. transitivity b'; assumption.
  - destruct (LEM (merely (exists a', a' < a /\ (a' = b \/ b < a')))) as [H2 | H2]; try exact _.
    + revert H2. rapply Trunc_rec. intros [a' [a'_a Ha']].
      revert Ha'. rapply Trunc_rec. intros [a'_b | b_a'].
      * apply tr. right. apply tr. right. rewrite <- a'_b. exact a'_a.
      * apply tr. right. apply tr. right. transitivity a'; assumption.
    + apply tr. right. apply tr. left.
      apply extensionality. intros c. split.
      * intros c_a. apply LEM_to_DNE; try exact _. intros not_c_b.
        apply H2. apply tr. exists c. split.
        -- exact c_a.
        -- refine (Trunc_rec _ (IHa c c_a b)). intros [c_b | H3].
           ++ apply Empty_rec. exact (not_c_b c_b).
           ++ exact H3.
      * intros c_b. apply LEM_to_DNE; try exact _. intros not_c_a.
        apply H1. apply tr. exists c. split.
        -- exact c_b.
        -- refine (Trunc_rec _ (IHb c c_b)). intros [a_c | H3].
           ++ apply tr. right. exact a_c.
           ++ refine (Trunc_rec _ H3). intros [a_c | c_a].
              ** apply tr. left. exact a_c.
              ** apply tr. right. apply Empty_rec. exact (not_c_a c_a).
Qed.



(** * Simulations *)

(* We define the notion of simulations between arbitrary relations. For simplicity, most lemmas about simulations are formulated for ordinals only, even if they do not need all properties of ordinals. The only exception is isordinal_simulation which can be used to prove that a relation is an ordinal. *)
Class IsSimulation
      {A B : Type} {R__A : Lt A} {R__B : Lt B} (f : A -> B) :=
{ simulation_is_hom {a a'}
  : a < a' -> f a < f a'
; simulation_is_merely_minimal {a b}
  : b < f a -> hexists (fun a' => a' < a /\ f a' = b)
}.
Arguments simulation_is_hom {_ _ _ _} _ {_ _ _}.


Instance ishprop_IsSimulation `{Funext}
         {A B : Ordinal} (f : A -> B) :
  IsHProp (IsSimulation f).
Proof.
  eapply trunc_equiv'.
  - issig.
  - exact _.
Qed.


Instance isinjective_simulation
         {A : Type} {R : Lt A} `{IsOrdinal A R}
         {B : Type} {Q : Lt B} `{IsOrdinal B Q}
         (f : A -> B) {is_simulation : IsSimulation f}
  : IsInjective f.
Proof.
  intros a. induction (well_foundedness a) as [a _ IHa].
  intros b.
  revert a IHa. induction (well_foundedness b) as [b _ IHb]. intros a IHa.
  intros fa_fb. apply extensionality; intros c. split.
  - intros c_a.
    assert (fc_fa : f c < f a)
      by exact (simulation_is_hom f c_a).
    assert (fc_fb : f c < f b)
      by (rewrite <- fa_fb; exact fc_fa).
    assert (H1 : hexists (fun c' => c' < b /\ f c' = f c))
      by exact (simulation_is_merely_minimal fc_fb).
    refine (Trunc_rec _ H1). intros (c' & c'_b & fc'_fc).
    assert (c = c') as ->. {
      apply IHa.
      + exact c_a.
      + symmetry. exact fc'_fc.
    }
    exact c'_b.
  - intros c_b.
    assert (fc_fb : f c < f b)
      by exact (simulation_is_hom f c_b).
    assert (fc_fa : f c < f a)
      by (rewrite fa_fb; exact fc_fb).
    assert (H1 : hexists (fun c' => c' < a /\ f c' = f c))
      by exact (simulation_is_merely_minimal fc_fa).
    refine (Trunc_rec _ H1). intros (c' & c'_a & fc'_fc).
    assert (c' = c) as <-.
    + apply IHb.
      * exact c_b.
      * intros a' a'_c'. apply IHa. exact (transitivity a'_c' c'_a).
      * exact fc'_fc.
    + exact c'_a.
Qed.


Lemma simulation_is_minimal
      {A : Type} {R : Lt A} `{IsOrdinal A R}
      {B : Type} {Q : Lt B} `{IsOrdinal B Q}
      (f : A -> B) {is_simulation : IsSimulation f}
  : forall {a b}, b < f a -> exists a', a' < a /\ f a' = b.
Proof.
  intros a b H1.
  refine (Trunc_rec _ (simulation_is_merely_minimal H1)). {
    apply hprop_allpath. intros (a1 & ? & p) (a2 & ? & <-).
    apply path_sigma_hprop; cbn. apply (injective f). exact p.
  }
  exact idmap.
Qed.


Lemma path_simulation `{Funext}
      {A B : Ordinal}
      (f : A -> B) {is_simulation_f : IsSimulation f}
      (g : A -> B) {is_simulation_g : IsSimulation g}
  : f = g.
Proof.
  apply path_forall; intros a.
  induction (well_foundedness a) as [a _ IH].
  apply (extensionality (f a) (g a)).
  intros b.
  split.
  - intros b_fa.
    destruct (simulation_is_minimal f b_fa) as (a' & a'_a & <-).
    rewrite (IH _ a'_a). apply (simulation_is_hom g). exact a'_a.
  - intros b_ga.
    destruct (simulation_is_minimal g b_ga) as (a' & a'_a & <-).
    rewrite <- (IH _ a'_a). apply (simulation_is_hom f). exact a'_a.
Qed.


Instance is_simulation_isomorphism
         {A : Type} {R__A : Lt A}
         {B : Type} {R__B : Lt B}
         (f : Isomorphism (A; R__A) (B; R__B))
  : IsSimulation f.1.
Proof.
  constructor.
  - intros a a' a_a'. apply f.2. exact a_a'.
  - intros a b b_fa. apply tr. exists (f.1^-1 b). split.
    + apply f.2. rewrite eisretr. exact b_fa.
    + apply eisretr.
Qed.


Instance ishprop_Isomorphism `{Univalence} (A B : Ordinal)
  : IsHProp (Isomorphism A B).
Proof.
  apply hprop_allpath; intros f g. apply path_sigma_hprop; cbn.
  apply path_equiv. apply path_simulation; exact _.
Qed.


Instance ishset_Ordinal `{Univalence}
  : IsHSet Ordinal.
Proof.
  intros A B.
  apply (trunc_equiv' (Isomorphism A B)). {
    apply equiv_path_Ordinal.
  }
  exact _.
Qed.



Lemma isordinal_simulation
      {A : Type}
     `{IsHSet A}

      {R : Lt A}
      {mere : is_mere_relation _ R}

      {B : Type}
      {Q : Lt B}
     `{IsOrdinal B Q}

      (f : A -> B)
     `{IsInjective _ _ f}
      {is_simulation : IsSimulation f}

  : IsOrdinal A R.
Proof.
  constructor.
  - exact _.
  - exact _.
  - intros a a' H1. apply (injective f). apply extensionality.
    intros b. split.
    + intros b_fa. refine (Trunc_rec _ (simulation_is_merely_minimal b_fa)).
      intros [a0 [a0_a <-]].
      apply (simulation_is_hom f). apply H1. exact a0_a.
    + intros b_fa'. refine (Trunc_rec _ (simulation_is_merely_minimal b_fa')).
      intros [a0 [a0_a' <-]].
      apply (simulation_is_hom f). apply H1. exact a0_a'.
  - intros a. remember (f a) as b eqn: fa_b.
    revert a fa_b. induction (well_foundedness b) as [b _ IH]. intros a <-.
    constructor; intros a' a'_a. apply (IH (f a')).
    + apply (simulation_is_hom f). exact a'_a.
    + reflexivity.
  - intros a b c a_b b_c.
    assert (fa_fc : f a < f c). {
      transitivity (f b). {
        apply (simulation_is_hom f). exact a_b.
      }
      apply (simulation_is_hom f). exact b_c.
    }
    refine (Trunc_rec _ (simulation_is_merely_minimal fa_fc)).
    intros [a' [a'_c fa'_fa]]. apply (injective f) in fa'_fa. subst a'.
    exact a'_c.
Qed.





(** * Initial segments *)

Definition initial_segment `{PropResizing}
           {A : Type} {R : Lt A} `{IsOrdinal A R} (a : A)
  : Ordinal.
Proof.
  srefine {| ordinal_carrier := {b : A & resize_hprop (b < a)}
           ; ordinal_relation := fun x y => x.1 < y.1
           |};
    try exact _.
  srapply (isordinal_simulation pr1).
  - unfold lt. exact _.
  - exact _.
  - exact _.
  - intros x y p. apply path_sigma_hprop. exact p.
  - constructor.
    + intros x y x_y. exact x_y.
    + intros b a' a'_b; cbn in *. apply tr.
      assert (b_a : b.1 < a). {
        exact ((equiv_resize_hprop _)^-1 b.2).
      }
      srapply exist. {
        exists a'.
        apply equiv_resize_hprop. exact (transitivity a'_b b_a).
      }
      cbn. split.
      * exact a'_b.
      * reflexivity.
Defined.


Notation "↓ a" := (initial_segment a) (at level 4, format "↓ a").
(* 3 is the level of most unary postfix operators in the standard lib, e.g. f^-1 *)

Definition in_
          `{PropResizing}
           {A : Ordinal} {a : A}
           (x : A) (H : x < a)
  : ↓a
  := (x; equiv_resize_hprop _ H).

Definition out
           `{PropResizing}
           {A : Ordinal} {a : A}
  : ↓a -> A
  := pr1.

Definition initial_segment_property
           `{PropResizing}
           {A : Ordinal} {a : A}
  : forall x : ↓a, out x < a.
Proof. intros x. exact ((equiv_resize_hprop _)^-1 (proj2 x)). Defined.


Instance is_simulation_out
         `{PropResizing}
         {A : Ordinal} (a : A)
  : IsSimulation (out : ↓a -> A).
Proof.
  unfold out.
  constructor.
  - auto.
  - intros x a' a'_x. apply tr.
    assert (a'_a : a' < a). {
      transitivity (out x). {
        assumption.
      }
      apply initial_segment_property.  (* TODO: Rename? *)
    }
    exists (in_ a' a'_a); cbn. auto.
Qed.


Instance isinjective_initial_segment `{Funext}
         `{PropResizing}
         (A : Ordinal)
  : IsInjective (initial_segment : A -> Ordinal).
Proof.
  enough (H1 : forall a1 a2 : A, ↓a1 = ↓a2 -> forall b : ↓a1, out b < a2). {
    intros a1 a2 p. apply extensionality; intros b. split.
    - intros b_a1. exact (H1 a1 a2 p (in_ b b_a1)).
    - intros b_a2. exact (H1 a2 a1 p^ (in_ b b_a2)).
  }

  intros a1 a2 p b.
  assert (out = transport (fun B : Ordinal => B -> A) p^ out)
    as ->. {
    apply path_simulation.
    - exact _.
    - apply transportD. exact _.
  }
  rewrite transport_arrow_toconst. rewrite inv_V. apply initial_segment_property.
Qed.




Lemma equiv_initial_segment_simulation `{Univalence}
      `{PropResizing}
      {A : Type@{A}} {R : Lt@{_ R} A} `{IsOrdinal A R}
      {B : Type@{B}} {Q : Lt@{_ Q} B} `{IsOrdinal B Q}
      (f : A -> B) {is_simulation : IsSimulation f} (a : A)
  : Isomorphism ↓(f a) ↓a.
Proof.
  apply isomorphism_inverse.
  srapply exist.
  - srapply equiv_adjointify.
    + intros x. exists (f x.1). apply equiv_resize_hprop.
      rapply simulation_is_hom. apply (equiv_resize_hprop _)^-1. exact x.2.
    + intros x.
      assert (x_fa : x.1 < f a). {
        exact ((equiv_resize_hprop _)^-1 x.2).
      }
      destruct (simulation_is_minimal f x_fa) as (a' & a'_a & _).
      exact (a'; equiv_resize_hprop _ a'_a).
    + cbn. intros x. apply path_sigma_hprop; cbn.
      transparent assert (x_fa : (x.1 < f a)). {
        exact ((equiv_resize_hprop _)^-1 x.2).
      }
      exact (snd (simulation_is_minimal f x_fa).2).
    + cbn. intros x. apply path_sigma_hprop; cbn.
      transparent assert (x_a : (x.1 < a)). {
        exact ((equiv_resize_hprop _)^-1 x.2).
      }
      apply (injective f).
      cbn. unfold initial_segment_property. cbn.
      rewrite eissect.
      exact (snd (simulation_is_minimal f (simulation_is_hom f x_a)).2).
  - cbn. intros [x x_a] [y y_a]; cbn. split.
    + apply (simulation_is_hom f).
    + intros fx_fy.
      destruct (simulation_is_minimal f fx_fy) as (a' & a'_y & p).
      apply injective in p; try exact _. subst a'. exact a'_y.
Qed.


Lemma path_initial_segment_simulation `{Univalence}
      `{PropResizing}
      {A : Type} {R : Lt A} `{IsOrdinal A R}
      {B : Type} {Q : Lt B} `{IsOrdinal B Q}
      (f : A -> B) {is_simulation : IsSimulation f} (a : A)
  : ↓(f a) = ↓a.
Proof.
  apply equiv_path_Ordinal. apply (equiv_initial_segment_simulation f).
Qed.





(** * `Ordinal` is an ordinal *)

Instance lt_Ordinal@{carrier relation +} `{PropResizing}
  : Lt Ordinal@{carrier relation}
  := fun A B => exists b : B, A = ↓b.


Instance is_mere_relation_lt_on_Ordinal `{Univalence} `{PropResizing}
  : is_mere_relation Ordinal lt_Ordinal.
Proof.
  intros A B.
  apply ishprop_sigma_disjoint.
  intros b b' -> p. apply (injective initial_segment). exact p.
Qed.


Definition bound
           `{PropResizing}
           {A B : Ordinal} (H : A < B)
  : B
  := H.1.

(* We use this notation to hide the proof of A < B that `bound` takes as an argument *)
Notation "A ◁ B" := (@bound A B _) (at level 70).


Definition bound_property
           `{PropResizing}
           {A B : Ordinal} (H : A < B)
  : A = ↓(bound H)
  := H.2.


Lemma isembedding_initial_segment `{Univalence}
      `{PropResizing}
      {A : Ordinal} (a b : A)
  : a < b <-> ↓a < ↓b.
Proof.
  split.
  - intros a_b. exists (in_ a a_b).
    exact (path_initial_segment_simulation out (in_ a a_b)).
  - intros a_b.
    assert (a = out (bound a_b))
           as ->. {
      apply (injective initial_segment).
      rewrite (path_initial_segment_simulation out).
      apply bound_property.
    }
    apply initial_segment_property.
Qed.


Instance Ordinal_is_ordinal `{Univalence}
         `{PropResizing}
  : IsOrdinal Ordinal (<).
Proof.
  constructor.
  - exact _.
  - exact is_mere_relation_lt_on_Ordinal.
  - intros A B H1.
    srapply path_Ordinal.
    + srapply equiv_adjointify.
      * assert (lt_B : forall a : A, ↓a < B). {
          intros a. apply H1. exists a. reflexivity.
        }
        exact (fun a => bound (lt_B a)).
      * assert (lt_A : forall b : B, ↓b < A). {
          intros b. apply H1. exists b. reflexivity.
        }
        exact (fun b => bound (lt_A b)).
      * cbn. intros b. apply (injective initial_segment).
        repeat rewrite <- bound_property. reflexivity.
      * cbn. intros a. apply (injective initial_segment).
        repeat rewrite <- bound_property. reflexivity.
    + cbn. intros a a'. split.
      * intros a_a'.
        apply isembedding_initial_segment.
        repeat rewrite <- bound_property.
        apply isembedding_initial_segment.
        assumption.
      * intros a_a'.
        apply isembedding_initial_segment in a_a'.
        repeat rewrite <- bound_property in a_a'.
        apply isembedding_initial_segment in a_a'.
        assumption.
  - intros A.
    constructor. intros ? [a ->].
    induction (well_foundedness a) as [a _ IH].
    constructor. intros ? [x ->].
    rewrite <- (path_initial_segment_simulation out).
    apply IH. apply initial_segment_property.
  - intros ? ? A [x ->] [a ->]. exists (out x).
    rewrite (path_initial_segment_simulation out).
    reflexivity.
Qed.


(* This is analogous to the set-theoretic statement that an ordinal is the set of all smaller ordinals. *)
Lemma isomorphism_to_initial_segment `{PropResizing} `{Univalence}
      (B : Ordinal@{A _})
  : Isomorphism B ↓B.
Proof.
  srapply exist.
  - srapply equiv_adjointify.
    + intros b. exists ↓b.
      apply equiv_resize_hprop.
      exists b. reflexivity.
    + intros [C HC]. eapply (equiv_resize_hprop _)^-1 in HC.
      exact (bound HC).
    + cbn. intros [C HC]. apply path_sigma_hprop; cbn.
      symmetry. apply bound_property.
    + cbn. intros x. rewrite eissect. reflexivity.
  - cbn. intros b b'. apply isembedding_initial_segment.
Qed.





(** * Ordinal successor *)

Definition successor (A : Ordinal) : Ordinal.
Proof.
  set (carrier := (A + Unit)%type).
  set (relation (x y : carrier) :=
         match x, y with
         | inl x, inl y => x < y
         | inl x, inr _ => Unit
         | inr _, inl y => Empty
         | inr _, inr _ => Empty
         end).
  exists carrier relation. constructor.
  - exact _.
  - intros [x | ?] [y | ?]; cbn; exact _.
  - intros [x | []] [y | []] H.
    + f_ap. apply extensionality. intros z. exact (H (inl z)).
    + enough (H0 : relation (inl x) (inl x)). {
        cbn in H0. destruct (irreflexivity _ _ H0).
      }
      apply H. cbn. exact tt.
    + enough (H0 : relation (inl y) (inl y)). {
        cbn in H0. destruct (irreflexivity _ _ H0).
      }
      apply H. cbn. exact tt.
    + reflexivity.
  - assert (H : forall a, Accessible relation (inl a)). {
      intros a. induction (well_foundedness a) as [a _ IH].
      constructor; intros [b | []]; cbn; intros H.
      + apply IH. exact H.
      + destruct H.
    }
    intros [x | []].
    + apply H.
    + constructor; intros [b | []]; cbn; intros H0.
      * apply H.
      * destruct H0.
  - intros [x | []] [y | []] [z | []]; cbn; auto.
    intros _ [].
Defined.


Lemma lt_successor `{Univalence} (A : Ordinal)
      `{PropResizing}
  : A < successor A.
Proof.
  exists (inr tt).
  srapply path_Ordinal.
  - srapply equiv_adjointify.
    + intros a. srapply in_.
      * exact (inl a).
      * exact tt.
    + intros [[a | []] Ha]; cbn in *.
      * exact a.
      * apply equiv_resize_hprop in Ha. destruct Ha.
    + intros [[a | []] Ha].
      * unfold in_. cbn. f_ap.
        assert (IsHProp (resize_hprop Unit)) by exact _.
        apply path_ishprop.
      * destruct ((equiv_resize_hprop _)^-1 Ha).
    + intros a. reflexivity.
  - cbn. intros a a'. reflexivity.
Qed.




(** * Ordinal limit *)

Definition image@{i j} {A : Type@{i}} {B : hSet@{j}} (f : A -> B) : Type@{i}
  := quotient (fun a a' : A => f a = f a').

Definition factor1 {A} {B : hSet} (f : A -> B)
  : A -> image f
  := Quotient.class_of _.

Lemma image_ind_prop {A} {B : hSet} (f : A -> B)
  (P : image f -> Type) `{forall x, IsHProp (P x)}
  : (forall a : A, P (factor1 f a))
    -> forall x : image f, P x.
Proof.
  intros step.
  srefine (quotient_ind_prop _ _ _); intros a; cbn.
  apply step.
Qed.

Definition image_rec {A} {B : hSet} (f : A -> B)
      {C : hSet} (step : A -> C)
  : (forall a a', f a = f a' -> step a = step a')
    -> image f -> C
  := quotient_rec _ step.



Definition factor2 {A} {B : hSet} (f : A -> B)
  : image f -> B
  := quotient_rec _ f (fun a a' fa_fa' => fa_fa').

Instance isinjective_factor2 `{Funext} {A} {B : hSet} (f : A -> B)
  : IsInjective (factor2 f).
Proof.
  unfold IsInjective, image.
  refine (quotient_ind_prop _ _ _); intros x; cbn.
  refine (quotient_ind_prop _ _ _); intros y; cbn.
  rapply related_classes_eq.
Qed.


Definition limit `{Univalence} `{PropResizing}
           {X : Type} (F : X -> Ordinal) : Ordinal.
Proof.
  set (f := fun x : {i : X & F i} => ↓x.2).
  set (carrier := image f : Type@{i}).
  set (relation := fun A B : carrier =>
                     resize_hprop (factor2 f A < factor2 f B)
                     : Type@{i}).
  exists carrier relation.
  srapply (isordinal_simulation (factor2 f)).
  - exact _.
  - exact _.
  - constructor; cbn.
    + intros x x' x_x'.
      unfold lt, relation. apply equiv_resize_hprop in x_x'. exact x_x'.
    + rapply image_ind_prop; intros a. cbn.
      intros B B_fa. apply tr.
      exists (factor1 f (a.1; out (bound B_fa))). cbn.
      unfold lt, relation, f; cbn.
      assert (↓(out (bound B_fa)) = B) as ->. {
        rewrite (path_initial_segment_simulation out).
        symmetry. apply bound_property.
      }
      split.
      * apply equiv_resize_hprop. exact B_fa.
      * reflexivity.
Defined.




Instance le_on_Ordinal : Le Ordinal :=
  fun A B => exists f : A -> B, IsSimulation f.


Definition limit_is_upper_bound `{Univalence} `{PropResizing}
           {X : Type} (F : X -> Ordinal)
  : forall x, F x <= limit F.
Proof.
  unfold le_on_Ordinal.
  intros x. unfold le.
  exists (fun u => factor1 _ (x; u)).
  split.
  - intros u v u_v. unfold lt; cbn. apply equiv_resize_hprop.
    apply isembedding_initial_segment. exact u_v.
  - intros u. rapply image_ind_prop; intros a.
    intros a_u. apply equiv_resize_hprop in a_u. cbn in a_u.
    apply tr. exists (out (bound a_u)). split.
    + apply initial_segment_property.
    + apply (injective (factor2 _)). cbn.
      rewrite (path_initial_segment_simulation out).
      symmetry. apply bound_property.
Qed.




  (** * Cardinals *)

Definition Cardinal := Trunc 0 hSet.
Definition card A `{IsHSet A} : Cardinal
  := tr (BuildhSet A).


Instance le_cardinal `{Univalence} : Le Cardinal
  := fun A B => Trunc_rec (fun A : hSet =>
             Trunc_rec (fun B : hSet =>
             (hexists (fun f : A -> B => IsInjective f)))
             B)
             A.

Instance is_mere_relation_le_cardinal `{Univalence}
  : is_mere_relation Cardinal (<=).
Proof.
  rapply Trunc_ind; intros A.
  rapply Trunc_ind; intros B.
  exact _.
Qed.


Lemma isinjective_Compose {A B C} (f : B -> C) (g : A -> B) :
  IsInjective f ->
  IsInjective g ->
  IsInjective (f ∘ g).
Proof.
  intros injective_f injective_g.
  intros x y eq. apply injective_g, injective_f. assumption.
Qed.

Instance transitive_le_Cardinal `{Univalence}
  : Transitive (le : Le Cardinal).
Proof.
  unfold Transitive.
  rapply Trunc_ind; intros X.
  rapply Trunc_ind; intros Y.
  rapply Trunc_ind; intros Z.
  rapply Trunc_rec; intros [f injective_f].
  rapply Trunc_rec; intros [g injective_g].
  apply tr. exists (g ∘ f).
  apply isinjective_Compose; assumption.
Qed.






(*** Hartogs number *)


Section Hartogs_Number.

  Universe A.
  Context {univalence : Univalence}
          {prop_resizing : PropResizing}
          (A : hSet@{A}).

  Fail Check { B : Ordinal@{A _} | card B <= card A } : Type@{A}.

  Lemma le_Cardinal_lt_Ordinal (B C : Ordinal)
    : B < C -> card B <= card C.
  Proof.
    intros B_C. apply tr. cbn. rewrite (bound_property B_C).
    exists out. apply isinjective_simulation. apply is_simulation_out.
  Qed.

  Definition hartogs_number' : Ordinal.
  Proof.
    set (carrier := {B : Ordinal & card B <= card A}).
    set (relation := fun (B C : carrier) => B.1 < C.1).

    exists carrier relation. srapply (isordinal_simulation pr1).
    - exact _.
    - exact _.
    - intros B C. apply path_sigma_hprop.
    - constructor.
      + intros a a' a_a'. exact a_a'.
      + intros [B small_B] C C_B; cbn in *. apply tr.
        unshelve eexists (C; _); cbn; auto.
        revert small_B. srapply Trunc_rec. intros [f isinjective_f]. apply tr.
        destruct C_B as [b ->].
        exists (fun '(x; x_b) => f x); cbn.
        intros [x x_b] [y y_b] fx_fy. apply path_sigma_hprop; cbn.
        apply (isinjective_f x y). exact fx_fy.
  Defined.

  Definition power_type (A : Type) : Type
    := A -> hProp.
  Notation 𝒫 := power_type.
  Definition subtype_inclusion {A} (U V : 𝒫 A)
    := (forall a, U a -> V a) /\ merely (exists a : A, V a /\ ~U a).
  Coercion subtype_as_type' {X} (Y : 𝒫 X) : Type
    := { x : X & Y x }.

  Infix "⊂" := subtype_inclusion (at level 50).
  Notation "(⊂)" := subtype_inclusion.

  Lemma hartogs_number'_injection `{Univalence} `{lem: ExcludedMiddle}
    : exists f : hartogs_number' -> 𝒫 (𝒫 (𝒫 A)),
        IsInjective f.
  Proof.
    transparent assert (ϕ : (forall X : 𝒫 (𝒫 A), Lt X)). {
      intros X. intros x1 x2. exact (x1.1 ⊂ x2.1).
    }
    unshelve eexists.
    - intros [B _]. intros X.
      (* `resize_hprop` should be used here to get the right universe level. But for some reason, that caused very bad performance for the rest of the proof. If a direct fix is too much work then one could leave it as it is and compose `hartogs_number'_injection` aftwerwards with an injection that just fixes the universe levels. *)
      exact (BuildhProp (resize_hprop (merely (Isomorphism (X : Type; ϕ X) B)))).
    - intros [B B_A] [C C_A] H0. apply path_sigma_hprop; cbn.
      revert B_A. rapply Trunc_rec. intros [f injective_f].
      apply equiv_path_Ordinal.
      assert {X : 𝒫 (𝒫 A) & Isomorphism (X : Type; ϕ X) B} as [X iso]. {
        assert (H2 :
                  forall X : 𝒫 A,
                    IsHProp { b : B & forall a, X a <-> exists b', b' < b /\ a = f b' }). {
          intros X. apply hprop_allpath; intros [b1 Hb1] [b2 Hb2].
          snrapply path_sigma_hprop; cbn.
          - intros b. snrapply trunc_forall.
            { exact _. }
            intros a. srapply trunc_prod.
            srapply trunc_arrow.
            rapply ishprop_sigma_disjoint. intros b1' b2' [_ ->] [_ p].
            apply (injective f). exact p.
          - apply extensionality. intros b'. split.
            + intros b'_b1.
              specialize (Hb1 (f b')). apply snd in Hb1.
              specialize (Hb1 (b'; (b'_b1, idpath))).
              apply Hb2 in Hb1. destruct Hb1 as (? & H2 & H3).
              apply injective in H3; try exact _. destruct H3.
              exact H2.
            + intros b'_b2.
              specialize (Hb2 (f b')). apply snd in Hb2.
              specialize (Hb2 (b'; (b'_b2, idpath))).
              apply Hb1 in Hb2. destruct Hb2 as (? & H2 & H3).
              apply injective in H3; try exact _. destruct H3.
              exact H2.
        }
        exists (fun X : 𝒫 A =>
             BuildhProp { b : B & forall a, X a <-> exists b', b' < b /\ a = f b' }). {
          unfold subtype_as_type'.
          unshelve eexists.
          - srapply equiv_adjointify.
            + intros [X [b _]]. exact b.
            + intros b.
              unshelve eexists (fun a => BuildhProp (exists b', b' < b /\ a = f b'))
              ; try exact _. {
                apply hprop_allpath. intros [b1 [b1_b p]] [b2 [b2_b q]].
                apply path_sigma_hprop; cbn. apply (injective f).
                destruct p, q. reflexivity.
              }
              exists b. intros b'. cbn. reflexivity.
            + cbn. reflexivity.
            + cbn. intros [X [b Hb]]. apply path_sigma_hprop. cbn.
              apply path_forall; intros a. apply path_iff_hprop; apply Hb.
          - cbn. intros [X1 [b1 H'1]] [X2 [b2 H'2]].
            unfold ϕ, subtype_inclusion. cbn.
            split.
            + intros H3.
              refine (Trunc_rec _ (trichotomy_ordinal b1 b2)). intros [b1_b2 | H4].
              * exact b1_b2.
              * revert H4. rapply Trunc_rec. intros [b1_b2 | b2_b1].
                -- apply Empty_rec. destruct H3 as [_ H3]. revert H3. rapply Trunc_rec. intros [a [X2a not_X1a]].
                   apply not_X1a. apply H'1. rewrite b1_b2. apply H'2. exact X2a.
                -- apply Empty_rec. destruct H3 as [_ H3]. revert H3. rapply Trunc_rec. intros [a [X2a not_X1a]].
                   apply not_X1a. apply H'1.
                   apply H'2 in X2a. destruct X2a as [b' [b'_b2 a_fb']].
                   exists b'. split.
                   ++ transitivity b2; assumption.
                   ++ assumption.
            + intros b1_b2. split.
              * intros a X1a. apply H'2. apply H'1 in X1a. destruct X1a as [b' [b'_b1 a_fb']].
                exists b'. split.
                -- transitivity b1; assumption.
                -- assumption.
              * apply tr. exists (f b1). split.
                -- apply H'2. exists b1; auto.
                -- intros X1_fb1. apply H'1 in X1_fb1. destruct X1_fb1 as [b' [b'_b1 fb1_fb']].
                   apply (injective f) in fb1_fb'. destruct fb1_fb'.
                   apply irreflexivity in b'_b1; try exact _. assumption.
        }
      }
      assert (IsOrdinal X (ϕ X)). {
        srefine (isordinal_simulation iso.1); try exact _.
        intros x1 x2 p.
        rewrite <- (eissect iso.1 x1).
        rewrite <- (eissect iso.1 x2).
        f_ap.
      }
      apply apD10 in H0. specialize (H0 X). cbn in H0.
      refine (transitive_Isomorphism _ (X : Type; ϕ X) _ _ _). {
        apply isomorphism_inverse. assumption.
      }
      enough (merely (Isomorphism (X : Type; ϕ X) C)). {
        revert X1. rapply Trunc_rec. {
          exact (ishprop_Isomorphism (Build_Ordinal X (ϕ X) _) C).
        }
        auto.
      }
      eapply equiv_resize_hprop.
      change (trunctype_type (BuildhProp (resize_hprop (Trunc (-1) (Isomorphism (X : Type; ϕ X) C))))).
      rewrite <- H0. cbn. apply equiv_resize_hprop. apply tr. exact iso.
  Qed.

  Definition resize_ordinal@{i j +}
             (B : Ordinal@{i _}) (C : Type@{j}) (g : C <~> B)
    : Ordinal@{j _}.
  Proof.
    exists C (fun c1 c2 : C => resize_hprop (g c1 < g c2)).
    srapply (isordinal_simulation g); try exact _.
    - apply (trunc_equiv' B (equiv_inverse g)).
    - intros c1 c2. intros p.
      rewrite <- (eissect g c1).  rewrite <- (eissect g c2). f_ap.
    - constructor.
      + intros a a' a_a'. apply (equiv_resize_hprop _)^-1. exact a_a'.
      + intros a b b_fa. apply tr. exists (g^-1 b). split.
        * apply equiv_resize_hprop. rewrite eisretr. exact b_fa.
        * apply eisretr.
  Defined.

  (* This definition fails because the propositional resizing in the definition of `hartogs_number'_injection` had to be removed. For details, see the comment in the definition of `hartogs_number'_injection` *)
  Fail Definition hartogs_number_carrier `{ExcludedMiddle} : Type@{A} :=
    {X : 𝒫 (𝒫 (𝒫 A)) | resize_hprop (merely (exists a, X = hartogs_number'_injection.1 a))}.

  (* `resize_ordinal` should be used to transport the ordinal structure from `hartogs_number'`. Then one can transport the results about the cardinality of `hartogs_number`. *)


End Hartogs_Number.
