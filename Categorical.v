Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Coq.Unicode.Utf8
  Coq.Program.Tactics
  Coq.ZArith.ZArith
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  Coq.Init.Datatypes
  Coq.Classes.RelationClasses
  Coq.Relations.Relation_Definitions
  Hask.Control.Monad
  Hask.Control.Monad.Free.

Generalizable All Variables.

Close Scope nat_scope.

Reserved Notation "f ∙ g" (at level 50).
Reserved Notation "f ~> g" (at level 50).
Reserved Notation "f ≈ g" (at level 79).

Class Category (ob : Type) := {
  uhom := Type : Type;
  hom  : ob → ob → uhom where "a ~> b" := (hom a b);

  id : ∀ {A}, A ~> A;
  compose : ∀ {A B C}, B ~> C -> A ~> B -> A ~> C
    where "f ∙ g" := (compose f g);

  eqv : ∀ {A B : ob}, relation (A ~> B)
    where "f ≈ g" := (eqv f g);

  eqv_equivalence : ∀ A B, Equivalence (@eqv A B);
  compose_respects : ∀ A B C,
    Proper (@eqv B C ==> @eqv A B ==> @eqv A C) compose;

  id_left  : ∀ {X Y} {f : X ~> Y}, id ∙ f ≈ f;
  id_right : ∀ {X Y} {f : X ~> Y}, f ∙ id ≈ f;

  comp_assoc : ∀ {X Y Z W} {f : Z ~> W} {g : Y ~> Z} {h : X ~> Y},
    f ∙ (g ∙ h) ≈ (f ∙ g) ∙ h
}.

Infix "~>" := hom (at level 50).
Infix "≈" := eqv (at level 79).
Infix "~{ C }~>" := (@hom C _) (at level 50).
Infix "∙" := compose (at level 50).

Notation "id[ X  ]" := (@id _ _ X)  (at level 50).

Add Parametric Relation `{Category C} (a b : C) : (hom a b) eqv
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (eqv_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (eqv_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (eqv_equivalence a b))
    as parametric_relation_eqv.

Add Parametric Morphism `{Category C} (a b c : C) : (@compose C _ a b c)
  with signature (eqv ==> eqv ==> eqv) as parametric_morphism_compose.
Proof.
  exact (@compose_respects _ _ a b c).
Defined.

Add Parametric Morphism `{Category C} (a b : C) : eqv
  with signature (eqv --> @eqv _ _ a b ++> impl)
    as impl_eqv.
Proof.
  intros.
  rewrite H0, <- H1.
  reflexivity.
Qed.

Add Parametric Morphism `{Category C} (a b : C) : eqv
  with signature (eqv --> @eqv _ _ a b ++> flip impl)
    as flip_impl_eqv.
Proof.
  intros.
  rewrite H0, <- H1.
  reflexivity.
Qed.

Hint Constructors Equivalence.

Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.

Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 1 (Reflexive ?X) => unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) => unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) => unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) => apply Build_Equivalence.
Hint Extern 8 (respectful _ _ _ _) => unfold respectful; auto.

Hint Extern 4 (?A ≈ ?A) => reflexivity.
Hint Extern 6 (?X ≈ ?Y) => apply Equivalence_Symmetric.
Hint Extern 7 (?X ≈ ?Z) =>
  match goal with
    [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y
  end.
Hint Extern 10 (?X ∙ ?Y ≈ ?Z ∙ ?Q) => apply compose_respects; auto.

Definition arrow (A B : Type) := A -> B.

Program Instance Coq_Category : Category Type := {
  hom := arrow;
  id := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x);
  eqv := fun _ _ => eq
}.

Record isomorphism `{Category ob}
       `(iso_to : X ~> Y) `(iso_from: Y ~> X) : Prop := {
  iso_to_from : iso_to   ∙ iso_from ≈ id;
  iso_from_to : iso_from ∙ iso_to   ≈ id
}.

Record isomorphic `{Category ob} (X Y : ob) : Type := {
  iso_to   : X ~> Y;
  iso_from : Y ~> X;
  iso_witness : isomorphism iso_to iso_from
}.

Infix "≅" := isomorphic (at level 100).

Class Terminal (ob : Type) := {
  terminal_category :> Category ob;
  One : ob;
  one : ∀ {A}, A ~> One
}.

Program Instance Coq_Terminal : Terminal Type := {
  terminal_category := Coq_Category;
  One := unit : Type;
  one := fun _ a => tt
}.

(*
Class Constant `(_ : Terminal ob) (A : ob) := {
  constant : One ~> A
}.

Arguments Constant ob {_} A.

Definition Value `(x : A) : One ~> A := const x.
*)

Class Cartesian (ob : Type) := {
  cartesian_terminal :> Terminal ob;

  Prod : ob -> ob -> ob;

  fork : ∀ {X Z W}, X ~> Z -> X ~> W -> X ~> Prod Z W;
  exl  : ∀ {X Y}, Prod X Y ~> X;
  exr  : ∀ {X Y}, Prod X Y ~> Y;

  fork_respects : ∀ X Z W,
    Proper (@eqv _ _ X Z ==> @eqv _ _ X W ==> @eqv _ _ X (Prod Z W)) fork;

  univ_products : ∀ {X Y Z} {f : X ~> Y} {g : X ~> Z} {h : X ~> Prod Y Z},
    h ≈ fork f g <-> exl ∙ h ≈ f ∧ exr ∙ h ≈ g
}.

Infix "△" := fork (at level 40).

Add Parametric Morphism `(_ : Cartesian ob) (a b c : ob) : (@fork ob _ a b c)
  with signature (eqv ==> eqv ==> eqv) as parametric_morphism_fork.
Proof.
  exact (@fork_respects _ _ a b c).
Defined.

Corollary exl_fork `{Cartesian C} : ∀ {X Z W} (f : X ~> Z) (g : X ~> W),
  exl ∙ f △ g ≈ f.
Proof.
  intros.
  apply (proj1 (univ_products (f:=f) (g:=g) (h:=f △ g)) (reflexivity _)).
Qed.

Corollary exr_fork `{Cartesian C} : ∀ {X Z W} (f : X ~> Z) (g : X ~> W),
  exr ∙ f △ g ≈ g.
Proof.
  intros.
  apply (proj1 (@univ_products C H _ _ _ f g (f △ g)) (reflexivity _)).
Qed.

Corollary fork_exl_exr `{Cartesian C} : ∀ {X Y},
  exl △ exr ≈ @id C _ (Prod X Y).
Proof.
  intros.
  symmetry.
  apply (proj2 (@univ_products C H (Prod X Y) X Y exl exr id)).
  rewrite !id_right; auto.
Qed.

Corollary fork_compose `{Cartesian C} :
  ∀ {X Y Z V W} (f : Prod Y Z ~> V) (h : Prod Y Z ~> W) (g : X ~> Prod Y Z),
    (f ∙ g) △ (h ∙ g) ≈ f △ h ∙ g.
Proof.
  intros.
  symmetry.
  apply (@univ_products C H _ _ _ (f ∙ g) (h ∙ g) (f △ h ∙ g)).
  rewrite !comp_assoc.
  rewrite exl_fork.
  rewrite exr_fork.
  auto.
Qed.

Program Instance Coq_Cartesian : Cartesian Type := {
  cartesian_terminal := Coq_Terminal;
  Prod := prod;
  fork := fun _ _ _ f g x => (f x, g x);
  exl  := fun _ _ p => fst p;
  exr  := fun _ _ p => snd p
}.
Obligation 1.
  split; intros; subst.
    split; extensionality x; reflexivity.
  destruct H.
  subst; simpl.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Class Closed (ob : Type) := {
  closed_cartesian :> Cartesian ob;

  Exp : ob -> ob -> ob;   (* internal homs *)

  apply : ∀ {X Y}, Prod (Exp X Y) X ~> Y;

  curry : ∀ {X Y Z}, Prod X Y ~> Z -> X ~> Exp Y Z;
  uncurry : ∀ {X Y Z}, X ~> Exp Y Z -> Prod X Y ~> Z;

  curry_respects : ∀ X Y Z,
    Proper (@eqv _ _ (Prod X Y) Z ==> @eqv _ _ X (Exp Y Z)) curry;
  uncurry_respects : ∀ X Y Z,
    Proper (@eqv _ _ X (Exp Y Z) ==> @eqv _ _ (Prod X Y) Z) uncurry;

  curry_uncurry : ∀ {X Y Z} (f : X ~> Exp Y Z), curry (uncurry f) ≈ f;
  uncurry_curry : ∀ {X Y Z} (f : Prod X Y ~> Z), uncurry (curry f) ≈ f;

  curry_apply : ∀ {X Y}, curry apply ≈ @id _ _ (Exp X Y);

  univ_exponentials : ∀ {X Y Z} (f : Prod X Y ~> Z),
    apply ∙ (curry f ∙ exl) △ exr ≈ f
}.

Add Parametric Morphism `(_ : Closed C) (a b c : C) : (@curry C _ a b c)
  with signature (eqv ==> eqv) as parametric_morphism_curry.
Proof.
  exact (@curry_respects _ _ a b c).
Defined.

Add Parametric Morphism `(_ : Closed C) (a b c : C) : (@uncurry C _ a b c)
  with signature (eqv ==> eqv) as parametric_morphism_uncurry.
Proof.
  exact (@uncurry_respects _ _ a b c).
Defined.

Corollary apply_curry `{Closed C} :
  ∀ {X Y Z W} (f : Prod Y Z ~> W) (g : X ~> Y) (h : X ~> Z),
    apply ∙ ((curry f ∙ g) △ h) ≈ f ∙ g △ h.
Proof.
  intros.
  pose proof (@univ_exponentials C H _ _ _ f).
  rewrite <- H0 at 2; clear H0.
  rewrite <- comp_assoc.
  rewrite <- fork_compose.
  rewrite exr_fork.
  rewrite <- comp_assoc.
  rewrite exl_fork.
  reflexivity.
Qed.

Program Instance Coq_Closed : Closed Type := {
  closed_cartesian := Coq_Cartesian;
  Exp := arrow;
  apply := fun _ _ p => fst p (snd p);
  curry := fun _ _ _ f a b => f (a, b);
  uncurry := fun _ _ _ f p => f (fst p) (snd p)
}.
Obligation 2.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.
Obligation 4.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Class Initial `(_ : Category ob) := {
  Zero : ob;
  zero : ∀ {A}, Zero ~> A
}.

Arguments Initial ob {_}.

Program Instance Coq_Initial : Initial Type := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.

Class Cocartesian `(_ : Initial ob) := {
  Sum : ob -> ob -> ob;

  join : ∀ {X Z W}, Z ~> X -> W ~> X -> Sum Z W ~> X;
  inl  : ∀ {X Y}, X ~> Sum X Y;
  inr  : ∀ {X Y}, Y ~> Sum X Y;

  join_respects : ∀ X Z W,
    Proper (@eqv _ _ Z X ==> @eqv _ _ W X ==> @eqv _ _ (Sum Z W) X) join;

  univ_sums : ∀ {X Y Z} {f : Y ~> X} {g : Z ~> X} {h : Sum Y Z ~> X},
    h ≈ join f g <-> h ∙ inl ≈ f ∧ h ∙ inr ≈ g
}.

Arguments Cocartesian ob {_ _}.

Infix "▽" := join (at level 40).

Add Parametric Morphism `(_ : Cocartesian ob) (a b c : ob) : (@join ob _ _ _ a b c)
  with signature (eqv ==> eqv ==> eqv) as parametric_morphism_join.
Proof.
  exact (@join_respects _ _ _ _ a b c).
Defined.

Corollary inl_join `{Cocartesian C} : ∀ {X Z W} (f : Z ~> X) (g : W ~> X),
  f ▽ g ∙ inl ≈ f.
Proof.
  intros.
  apply (proj1 (@univ_sums C H _ _ _ _ _ f g (f ▽ g)) (reflexivity _)).
Qed.

Corollary inr_join `{Cocartesian C} : ∀ {X Z W} (f : Z ~> X) (g : W ~> X),
  f ▽ g ∙ inr ≈ g.
Proof.
  intros.
  apply (proj1 (@univ_sums C H _ _ _ _ _ f g (f ▽ g)) (reflexivity _)).
Qed.

Corollary join_inl_inr `{Cocartesian C} : ∀ {X Y},
  inl ▽ inr ≈ @id C _ (Sum X Y).
Proof.
  intros.
  symmetry.
  apply (proj2 (@univ_sums C H _ _ (Sum X Y) X Y inl inr id)).
  rewrite !id_left.
  auto.
Qed.

Corollary join_compose `{Cocartesian C} :
  ∀ {X Y Z V W} (f : V ~> Sum Y Z) (h : W ~> Sum Y Z) (g : Sum Y Z ~> X),
    (g ∙ f) ▽ (g ∙ h) ≈ g ∙ f ▽ h.
Proof.
  intros.
  symmetry.
  apply (@univ_sums C H _ _ _ _ _ (g ∙ f) (g ∙ h) (g ∙ f ▽ h)).
  rewrite <- !comp_assoc.
  rewrite inl_join.
  rewrite inr_join.
  auto.
Qed.

Program Instance Coq_Cocartesian : Cocartesian Type := {
  Sum := sum;
  join := fun _ _ _ f g x =>
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  inl  := fun _ _ p => Datatypes.inl p;
  inr  := fun _ _ p => Datatypes.inr p
}.
Obligation 1.
  split; intros; subst.
    split; extensionality x; reflexivity.
  destruct H.
  subst; simpl.
  extensionality x.
  destruct x; auto.
Qed.

Class Bicartesian `(_ : Cartesian C) `(_ : Cocartesian C).

Program Instance Coq_Bicartesian : Bicartesian Coq_Cartesian Coq_Cocartesian.

Class Distributive `(_ : Bicartesian C) := {
  prod_sum_distl : ∀ {X Y Z : C}, Prod (Sum Y Z) X ≅ Sum (Prod Y X) (Prod Z X);
  prod_sum_distr : ∀ {X Y Z : C}, Prod X (Sum Y Z) ≅ Sum (Prod X Y) (Prod X Z)
}.

Program Instance Coq_Distributive : Distributive Coq_Bicartesian.
Obligation 1.
  apply Build_isomorphic with
    (iso_to:=
       fun p : ((Y + Z) * X) =>
         match p with
         | (Datatypes.inl y, x) => Datatypes.inl (y, x)
         | (Datatypes.inr z, x) => Datatypes.inr (z, x)
         end)
    (iso_from:=
       fun p : ((Y * X) + (Z * X)) =>
         match p with
         | Datatypes.inl (y, x) => (Datatypes.inl y, x)
         | Datatypes.inr (z, x) => (Datatypes.inr z, x)
         end).
  constructor; simpl;
  extensionality p;
  intuition.
Qed.
Obligation 2.
  apply Build_isomorphic with
    (iso_to:=
       fun p : (X * (Y + Z)) =>
         match p with
         | (x, Datatypes.inl y) => Datatypes.inl (x, y)
         | (x, Datatypes.inr z) => Datatypes.inr (x, z)
         end)
    (iso_from:=
       fun p : ((X * Y) + (X * Z)) =>
         match p with
         | Datatypes.inl (x, y) => (x, Datatypes.inl y)
         | Datatypes.inr (x, z) => (x, Datatypes.inr z)
         end).
  constructor; simpl;
  extensionality p;
  intuition.
Qed.

Class CategoryFunctor `(_ : Category C) `(_ : Category D) := {
  fobj : C -> D;
  fmap : ∀ {X Y : C}, X ~> Y → fobj X ~> fobj Y;

  fmap_respects : ∀ X Y,
    Proper (@eqv _ _ X Y ==> @eqv _ _ (fobj X) (fobj Y)) fmap;

  fmap_id : ∀ {X : C}, fmap (@id C _ X) ≈ id;
  fmap_comp : ∀ {X Y Z} (f : Y ~> Z) (g : X ~> Y),
    fmap (f ∙ g) ≈ fmap f ∙ fmap g
}.

Arguments CategoryFunctor C {_} D {_}.

Notation "C ⟶ D" := (CategoryFunctor C D) (at level 90, right associativity).

Add Parametric Morphism `(_ : CategoryFunctor C D) (a b : C) : (@fmap C _ D _ _ a b)
  with signature (eqv ==> eqv) as parametric_morphism_fmap.
Proof.
  exact (@fmap_respects _ _ _ _ _ a b).
Defined.

Class TerminalFunctor `(_ : Terminal C) `(_ : Terminal D) := {
  terminal_category_functor :> @CategoryFunctor C _ D _;

  map_one : One ~> fobj One;

  fmap_one : ∀ {X : C}, fmap one ≈ map_one ∙ @one _ _ (fobj X)
}.

Arguments TerminalFunctor C {_} D {_}.

Class CartesianFunctor `(_ : Cartesian C) `(_ : Cartesian D) := {
  terminal_functor :> TerminalFunctor C D;

  fobj_prod_iso : ∀ {X Y : C}, fobj (Prod X Y) ≅ Prod (fobj X) (fobj Y);

  prod_in  := fun X Y => iso_from (@fobj_prod_iso X Y);
  prod_out := fun X Y => iso_to   (@fobj_prod_iso X Y);

  fmap_exl : ∀ {X Y : C}, fmap (@exl C _ X Y) ≈ exl ∙ prod_out _ _;
  fmap_exr : ∀ {X Y : C}, fmap (@exr C _ X Y) ≈ exr ∙ prod_out _ _;
  fmap_fork : ∀ {X Y Z : C} (f : X ~> Y) (g : X ~> Z),
    fmap (f △ g) ≈ prod_in _ _ ∙ fmap f △ fmap g
}.

Arguments CartesianFunctor C {_} D {_}.

Arguments prod_in {C _ D _ _ _ _} /.
Arguments prod_out {C _ D _ _ _ _} /.

Notation "prod_in[ C -> D | X ~> Y  ]" := (@prod_in C _ _ _ D _ _ _ _ X Y).
Notation "prod_out[ C -> D | X ~> Y  ]" := (@prod_out C _ _ _ D _ _ _ _ X Y).

Corollary prod_in_out `{CartesianFunctor C D} : ∀ (X Y : C),
  prod_in ∙ prod_out ≈ @id _ _ (fobj (Prod X Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_prod_iso _ _ _ _ _ X Y))).
Qed.

Corollary prod_out_in `{CartesianFunctor C D} : ∀ (X Y : C),
  prod_out ∙ prod_in ≈ @id _ _ (Prod (fobj X) (fobj Y)).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_prod_iso _ _ _ _ _ X Y))).
Qed.

Corollary prod_in_inj `{CartesianFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> Prod (fobj X) (fobj Y)),
    prod_in ∙ f ≈ prod_in ∙ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- prod_out_in.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite prod_out_in.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Corollary prod_out_inj `{CartesianFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> fobj (Prod Y Z)),
    prod_out ∙ f ≈ prod_out ∙ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- prod_in_out.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite prod_in_out.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Class ClosedFunctor `(_ : Closed C) `(_ : Closed D) := {
  cartesian_functor :> CartesianFunctor C D;

  fobj_exp_iso : ∀ {X Y : C}, fobj (Exp X Y) ≅ Exp (fobj X) (fobj Y);

  exp_in  := fun X Y => iso_from (@fobj_exp_iso X Y);
  exp_out := fun X Y => iso_to   (@fobj_exp_iso X Y);

  fmap_apply : ∀ {X Y : C},
    fmap (@apply C _ X Y) ≈ uncurry (curry apply ∙ exp_out _ _) ∙ prod_out;
  fmap_curry : ∀ {X Y Z : C} {f : Prod X Y ~> Z},
    fmap (@curry C _ X Y Z f) ≈ exp_in _ _ ∙ curry (fmap f ∙ prod_in);
  fmap_uncurry : ∀ {X Y Z : C} (f : X ~> Exp Y Z),
    fmap (@uncurry C _ X Y Z f) ≈ uncurry (exp_out _ _ ∙ fmap f) ∙ prod_out
}.

Arguments ClosedFunctor C {_} D {_}.

Arguments exp_in {C _ D _ _ _ _} /.
Arguments exp_out {C _ D _ _ _ _} /.

Corollary exp_in_out `{ClosedFunctor C D} : ∀ (X Y : C),
  exp_in ∙ exp_out ≈ @id _ _ (fobj (Exp X Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_exp_iso _ _ _ _ _ X Y))).
Qed.

Corollary exp_out_in `{ClosedFunctor C D} : ∀ (X Y : C),
  exp_out ∙ exp_in ≈ @id _ _ (Exp (fobj X) (fobj Y)).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_exp_iso _ _ _ _ _ X Y))).
Qed.

Corollary exp_in_inj `{ClosedFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> Exp (fobj Y) (fobj Z)),
    exp_in ∙ f ≈ exp_in ∙ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- exp_out_in.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite exp_out_in.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Corollary exp_out_inj `{ClosedFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> fobj (Exp Y Z)),
    exp_out ∙ f ≈ exp_out ∙ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- exp_in_out.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite exp_in_out.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Class InitialFunctor `(_ : Initial C) `(_ : Initial D) := {
  initial_category_functor :> @CategoryFunctor C _ D _;
  map_zero : fobj Zero ~> Zero;

  fmap_zero : ∀ {X : C},
    @fmap C _ D _ _ Zero X zero ≈ @zero _ _ _ (fobj X) ∙ map_zero
}.

Arguments InitialFunctor C {_ _} D {_ _}.

Class CocartesianFunctor `(_ : Cocartesian C) `(_ : Cocartesian D) := {
  initial_functor :> InitialFunctor C D;

  fobj_sum_iso : ∀ {X Y : C}, fobj (Sum X Y) ≅ Sum (fobj X) (fobj Y);

  sum_in  := fun X Y => iso_from (@fobj_sum_iso X Y);
  sum_out := fun X Y => iso_to   (@fobj_sum_iso X Y);

  fmap_inl : ∀ {X Y : C}, fmap (@inl C _ _ _ X Y) ≈ sum_in _ _ ∙ inl;
  fmap_inr : ∀ {X Y : C}, fmap (@inr C _ _ _ X Y) ≈ sum_in _ _ ∙ inr;
  fmap_join : ∀ {X Y Z : C} (f : Y ~> X) (g : Z ~> X),
    fmap (f ▽ g) ≈ fmap f ▽ fmap g ∙ sum_out _ _
}.

Arguments CocartesianFunctor C {_ _ _} D {_ _ _}.

Arguments sum_in {C _ _ _ D _ _ _ _ _ _} /.
Arguments sum_out {C _ _ _ D _ _ _ _ _ _} /.

Notation "sum_in[ C -> D | X ~> Y  ]" := (@sum_in C _ _ _ D _ _ _ _ X Y).
Notation "sum_out[ C -> D | X ~> Y  ]" := (@sum_out C _ _ _ D _ _ _ _ X Y).

Corollary sum_in_out `{CocartesianFunctor C D} : ∀ (X Y : C),
  sum_in ∙ sum_out ≈ @id _ _ (fobj (Sum X Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_sum_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Corollary sum_out_in `{CocartesianFunctor C D} : ∀ (X Y : C),
  sum_out ∙ sum_in ≈ @id _ _ (Sum (fobj X) (fobj Y)).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_sum_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Corollary sum_in_surj `{CocartesianFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj (Sum X Y) ~> fobj X),
    f ∙ sum_in ≈ g ∙ sum_in <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- sum_in_out.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    rewrite sum_in_out.
    rewrite id_right.
    reflexivity.
  subst.
  rewrite H6.
  reflexivity.
Qed.

Corollary sum_out_inj `{CocartesianFunctor C D} :
  ∀ {X Y Z : C} (f g : Sum (fobj Y) (fobj Z) ~> fobj X),
    f ∙ sum_out ≈ g ∙ sum_out <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- sum_out_in.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    rewrite sum_out_in.
    rewrite id_right.
    reflexivity.
  subst.
  rewrite H6.
  reflexivity.
Qed.

Module CCC.

Section CCC.

Variable ob : Type.
Context `{Closed ob}.
Context `{F : @ClosedFunctor Type _ ob _}.

Import EqNotations.

Definition rel `(lam : a -> b) (ccc : fobj a ~> fobj b) : Prop :=
  fmap (H:=terminal_category
          (Terminal:=cartesian_terminal
             (Cartesian:=closed_cartesian
                (Closed:=Coq_Closed)))) lam ≈ ccc.

Infix "===>" := rel (at level 99).

Theorem ccc_id : ∀ (a : Type), (λ x : a, x) ===> id.
Proof.
  unfold rel; intros.
  rewrite <- fmap_id.
  reflexivity.
Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

Theorem ccc_apply :
  ∀ (a b c : Type)
    (U : a -> b -> c) (U' : fobj a ~> Exp (fobj b) (fobj c))
    (V : a -> b) (V' : fobj a ~> fobj b),
  U ===> exp_in ∙ U' ->
  V ===> V' ->
    (λ x, U x (V x)) ===> apply ∙ (U' △ V').
Proof.
  unfold rel; intros; subst.
  step (λ x, U x (V x)) => (λ x, @apply Type _ b c (U x, V x)).
  step (λ x, U x (V x)) => (λ x, @apply Type _ b c (U x, V x)).
  step (λ x, @apply Type _ b c (U x, V x))
    => (λ x, @apply Type _ b c ((U △ V) x)).
  step (λ x, @apply Type _ b c ((U △ V) x))
    => (@apply Type _ b c ∙ (U △ V)).
  rewrite fmap_comp.
  rewrite fmap_apply.
  rewrite fmap_fork.
  rewrite comp_assoc.
  rewrite <- (@comp_assoc _ _ _ _ _ _ _ prod_out).
  rewrite prod_out_in.
  rewrite id_right.
  generalize (proj2 (exp_out_inj (fmap U) (exp_in ∙ U')) H0).
  rewrite comp_assoc.
  rewrite exp_out_in.
  rewrite id_left.
  intros; subst.
  rewrite <- apply_curry.
  rewrite curry_uncurry.
  rewrite curry_apply.
  rewrite id_left.
  rewrite H1, H2.
  reflexivity.
Qed.

Theorem ccc_curry :
  ∀ (a b c : Type)
    (U : a * b -> c) (U' : Prod (fobj a) (fobj b) ~> fobj c),
    U ===> U' ∙ prod_out ->
      (λ x, λ y, U (x, y)) ===> exp_in ∙ curry U'.
Proof.
  unfold rel; intros; subst.
  generalize (@fmap_curry Type _ ob _ _ a b c U).
  simpl.
  unfold arrow.
  intro H1; rewrite H1; clear H1.
  pose proof (@exp_in_inj Type _ ob _ _ a b c) as H1.
  apply H1; clear H1.
  simpl in H0; rewrite H0; clear H0.
  rewrite <- comp_assoc.
  pose proof (@prod_out_in Type _ ob _ _ a b) as H1.
  simpl in H1; rewrite H1; clear H1.
  rewrite id_right.
  reflexivity.
Qed.

Theorem ccc_terminal : ∀ (a : Type),
  (λ _ : a, tt) ===> map_one ∙ @one _ _ (fobj a).
Proof.
  unfold rel; intros.
  step (λ _ : a, ()) => (@one _ _ a).
  pose proof @fmap_one.
  simpl in H0.
  rewrite H0.
  reflexivity.
Qed.

End CCC.

End CCC.

Module Expr.

Inductive Obj : Type :=
  | One_  : Obj
  | Prod_ : Obj -> Obj -> Obj
  | Exp_  : Obj -> Obj -> Obj
  | Zero_ : Obj
  | Sum_  : Obj -> Obj -> Obj.

Fixpoint denote (o : Obj) :
  ∀ `{Closed C} `{@Initial C _} `{@Cocartesian C _ _}, C :=
  fun _ _ _ _ => match o with
  | One_      => One
  | Prod_ x y => Prod (denote x) (denote y)
  | Exp_ x y  => Exp (denote x) (denote y)
  | Zero_     => Zero
  | Sum_ x y  => Sum (denote x) (denote y)
  end.

Inductive Hom : Obj -> Obj -> Type :=
  | Id      : ∀ a, Hom a a
  | Compose : ∀ a b c, Hom b c -> Hom a b -> Hom a c

  | One'      : ∀ a, Hom a One_
  (* | Constant' : ∀ a, Hom One_ a *)

  | Exl     : ∀ a b, Hom (Prod_ a b) a
  | Exr     : ∀ a b, Hom (Prod_ a b) b
  | Fork    : ∀ a c d, Hom a c -> Hom a d -> Hom a (Prod_ c d)

  | Apply   : ∀ a b, Hom (Prod_ (Exp_ a b) a) b
  | Curry   : ∀ a b c, Hom (Prod_ a b) c -> Hom a (Exp_ b c)
  | Uncurry : ∀ a b c, Hom a (Exp_ b c) -> Hom (Prod_ a b) c

  | Zero'   : ∀ a, Hom Zero_ a

  | Inl     : ∀ a b, Hom a (Sum_ a b)
  | Inr     : ∀ a b, Hom b (Sum_ a b)
  | Join    : ∀ a c d, Hom c a -> Hom d a -> Hom (Sum_ c d) a

  | Distl   : ∀ u v a, Hom (Prod_ (Sum_ u v) a) (Sum_ (Prod_ u a) (Prod_ v a))
  | Distr   : ∀ b u v, Hom (Prod_ b (Sum_ u v)) (Sum_ (Prod_ b u) (Prod_ b v)).

Fixpoint eval `(c : Hom a b) :
  ∀ `{Closed C}
    `{@Initial C _}
    `{@Cocartesian C _ _}
    `{@Bicartesian C _ _ _ _}
    `{@Distributive C _ _ _ _ _},
    denote a ~{C}~> denote b := fun C _ _ _ _ _ =>
  match c with
  | Id _              => id
  | Compose _ _ _ f g => eval f ∙ eval g

  | One' _            => one
  (* | Constant' _       => _ *)

  | Exl _ _           => exl
  | Exr _ _           => exr
  | Fork _ _ _ f g    => fork (eval f) (eval g)

  | Apply _ _         => apply
  | Curry _ _ _ f     => curry (eval f)
  | Uncurry _ _ _ f   => uncurry (eval f)

  | Zero' _           => zero

  | Inl _ _           => inl
  | Inr _ _           => inr
  | Join _ _ _ f g    => join (eval f) (eval g)

  | Distl _ _ _       => iso_to prod_sum_distl
  | Distr _ _ _       => iso_to prod_sum_distr
  end.

Program Instance Hom_Category : Category Obj := {
  hom := Hom;
  id := Id;
  compose := Compose;
  eqv := fun _ _ f g =>
    ∀ `{Closed C}
      `{@Initial C _}
      `{@Cocartesian C _ _}
      `{@Bicartesian C _ _ _ _}
      `{@Distributive C _ _ _ _ _},
      @eqv C _ _ _ (eval f) (eval g)
}.
Obligation 1.
  constructor.
  - intros ???.
    reflexivity.
  - intros ?????.
    symmetry.
    apply H.
  - intros ???????????.
    rewrite H, H0.
    reflexivity.
Defined.
Obligation 2.
  intros ????????????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 3.
  rewrite id_left.
  reflexivity.
Qed.
Obligation 4.
  rewrite id_right.
  reflexivity.
Qed.
Obligation 5.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Instance Hom_Terminal : Terminal Obj := {
  terminal_category := Hom_Category;
  One := One_;
  one := One'
}.

(* Program Instance Hom_Constant : Constant Obj := { *)
(*   constant := fun _ _ p => Constant' p *)
(* }. *)

Program Instance Hom_Cartesian : Cartesian Obj := {
  cartesian_terminal := Hom_Terminal;
  Prod := Prod_;
  fork := Fork;
  exl  := Exl;
  exr  := Exr
}.
Obligation 1.
  intros ????????????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 2.
  split; intros.
    split; intros ??????.
      rewrite H.
      rewrite exl_fork.
      reflexivity.
    rewrite H.
    rewrite exr_fork.
    reflexivity.
  destruct H.
  rewrite <- H.
  rewrite <- H5.
  rewrite fork_compose.
  rewrite fork_exl_exr.
  rewrite id_left.
  reflexivity.
Qed.

Program Instance Hom_Closed : Closed Obj := {
  closed_cartesian := Hom_Cartesian;
  Exp := Exp_;
  apply := Apply;
  curry := Curry;
  uncurry := Uncurry
}.
Obligation 1.
  intros ?????????.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Obligation 2.
  intros ?????????.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Obligation 3.
  apply curry_uncurry.
Qed.
Obligation 4.
  apply uncurry_curry.
Qed.
Obligation 5.
  apply curry_apply.
Qed.
Obligation 6.
  rewrite apply_curry.
  rewrite fork_exl_exr.
  rewrite id_right.
  reflexivity.
Qed.

Program Instance Hom_Initial : Initial Obj := {
  Zero := Zero_;
  zero := Zero'
}.

Program Instance Hom_Cocartesian : Cocartesian Obj := {
  Sum  := Sum_;
  join := Join;
  inl  := Inl;
  inr  := Inr
}.
Obligation 1.
  intros ????????????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 2.
  split; intros.
    split; intros ??????.
      rewrite H.
      rewrite inl_join.
      reflexivity.
    rewrite H.
    rewrite inr_join.
    reflexivity.
  destruct H.
  rewrite <- H.
  rewrite <- H5.
  rewrite join_compose.
  rewrite join_inl_inr.
  rewrite id_right.
  reflexivity.
Qed.

Section Hom.

Context `{Closed C}.
Context `{@Initial C _}.
Context `{@Cocartesian C _ _}.
Context `{@Bicartesian C _ _ _ _}.
Context `{@Distributive C _ _ _ _ _}.

Global Program Instance Hom_CategoryFunctor :
  CategoryFunctor Obj C := {
  fobj := fun x => denote x;
  fmap := fun _ _ f => eval f
}.

Global Program Instance Hom_TerminalFunctor :
  TerminalFunctor Obj C := {
  terminal_category_functor := Hom_CategoryFunctor;
  map_one := id
}.
Obligation 1.
  rewrite id_left.
  reflexivity.
Qed.

Global Program Instance Hom_CartesianFunctor :
  CartesianFunctor Obj C := {
  terminal_functor := Hom_TerminalFunctor;
  fobj_prod_iso := _
}.
Obligation 1.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor; rewrite id_left; reflexivity.
Defined.
Obligation 2.
  rewrite id_right.
  reflexivity.
Qed.
Obligation 3.
  rewrite id_right.
  reflexivity.
Qed.
Obligation 4.
  rewrite id_left.
  reflexivity.
Qed.

Global Program Instance Hom_ClosedFunctor : ClosedFunctor Obj C := {
  cartesian_functor := Hom_CartesianFunctor;
  fobj_exp_iso := _
}.
Obligation 1.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor; rewrite id_left; reflexivity.
Defined.
Obligation 2.
  rewrite !id_right.
  rewrite uncurry_curry.
  reflexivity.
Qed.
Obligation 3.
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Qed.
Obligation 4.
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Qed.

Global Program Instance Hom_InitialFunctor :
  InitialFunctor Obj C := {
  map_zero := id
}.
Obligation 1.
  rewrite id_right.
  reflexivity.
Qed.

Global Program Instance Hom_CocartesianFunctor :
  CocartesianFunctor Obj C := {
  initial_functor := Hom_InitialFunctor;
  fobj_sum_iso := _
}.
Obligation 1.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor; rewrite id_left; reflexivity.
Defined.
Obligation 2.
  rewrite id_left.
  reflexivity.
Qed.
Obligation 3.
  rewrite id_left.
  reflexivity.
Qed.
Obligation 4.
  rewrite id_right.
  reflexivity.
Qed.

End Hom.

(*
(* Coq abstract data types are represented in CCC by identifying their
   equivalent construction. *)
Class Represented (A : Type) `{Terminal C} (B : C) := {
  repr : A -> One ~> B;
  abst : One ~> B -> A;

  abst_repr : ∀ x, abst (repr x) = x
}.

Program Instance unit_Represented : Represented (unit : Type) One_ := {
  repr  := fun _ : unit => Constant' One_
}.
Obligation 1.
Obligation 2.
  destruct x.
  reflexivity.
Qed.

Program Instance bool_Represented : Represented bool := {
  Rep := Sum_ One_ One_;
  repr := fun b =>
            if b
            then inl
            else inr
}.
Obligation 1.
  destruct H.
    exact true.
  exact false.
Defined.
Obligation 2.
  destruct x; auto.
Qed.

Program Instance prod_Represented `{Represented a} `{Represented b} :
  Represented (@prod a b) := {
  Rep := Prod_ (Rep a) (Rep b);
  repr := fun p => match p with
                     (x, y) => repr x △ repr y
                   end
}.
Obligation 1.
  exact (abst d, abst d0).
Defined.
Obligation 2.
  destruct H, H0; simpl; subst.
  rewrite eval_repr0.
  rewrite eval_repr1.
  reflexivity.
Qed.
*)

Definition foo `(f : Prod A B ~> C) :=
  Eval simpl in apply ∙ (curry f ∙ exl) △ exr.
Print foo.

End Expr.
