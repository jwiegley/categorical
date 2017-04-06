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
(* implication respects equivalence *)
Proof.
  intros.
  rewrite H0, <- H1.
  reflexivity.
Qed.

Add Parametric Morphism `{Category C} (a b : C) : eqv
  with signature (eqv --> @eqv _ _ a b ++> flip impl)
    as flip_impl_eqv.
(* flipped implication respects equivalence *)
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

(*
Program Instance Iso_Equivalence `{Category C} : Equivalence (@isomorphic C _).
Obligation 1.
  unfold Reflexive; intros.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor;
  rewrite id_left; reflexivity.
Qed.
*)

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

(* Corollary curry_uncurry `{Closed C} : ∀ {X Y Z} (f : X ~> Exp Y Z), *)
(*   curry (uncurry f) ≈ f. *)
(* Proof. *)
(*   intros. *)
(*   replace (curry (uncurry f)) with ((@compose Type _ _ _ _ curry uncurry) f) by auto. *)
(*   rewrite (iso_to_from (@curry_uncurry_iso _ _ X Y Z)). *)
(*   reflexivity. *)
(* Qed. *)

(* Corollary uncurry_curry `{Closed C} : ∀ {X Y Z} (f : Prod X Y ~> Z), *)
(*   uncurry (curry f) ≈ f. *)
(* Proof. *)
(*   intros. *)
(*   replace (uncurry (curry f)) with ((@compose Type _ _ _ _ uncurry curry) f) by auto. *)
(*   rewrite (iso_from_to (@curry_uncurry_iso _ _ X Y Z)). *)
(*   reflexivity. *)
(* Qed. *)

Program Instance Coq_Closed : Closed Type := {
  closed_cartesian := Coq_Cartesian;
  Exp := arrow;
  apply := fun _ _ p => fst p (snd p);
  curry := fun _ _ _ f a b => f (a, b);
  uncurry := fun _ _ _ f p => f (fst p) (snd p)
}.
(* Obligation 2. *)
(*   constructor; intros. *)
(*     simpl. *)
(*     extensionality p; simpl; auto. *)
(*   simpl. *)
(*   extensionality x; simpl. *)
(*   extensionality p. *)
(*   rewrite <- surjective_pairing. *)
(*   reflexivity. *)
(* Qed. *)
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

  univ_sums : ∀ {X Y Z} {f : Y ~> X} {g : Z ~> X} {h : Sum Y Z ~> X},
    h ≈ join f g <-> h ∙ inl ≈ f ∧ h ∙ inr ≈ g
}.

Arguments Cocartesian ob {_ _}.

Infix "▽" := join (at level 40).

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

Class Constant `(_ : Initial ob) (A : Type) := {
  intro : A → Zero ~> A
}.

Arguments Constant ob {_ _} A.

Program Instance Coq_Constant {A : Type} : Constant Type A := {
  intro := fun b _ => b
}.

(* Coq abstract data types are represented in CCC by identifying their
equivalent construction. *)
Class Represented (A : Type) := {
  repr : ∀ `{Category C} (* `{Cocartesian C} `{Terminal C} *), C
}.

(* Program Instance bool_Represented : Represented bool := { *)
(*   repr := fun C _ _ _ => @Sum C _ One One *)
(* }. *)

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

(* Notation "fmap[ M ]" := (@fmap _ _ M _ _ _ _) (at level 9). *)

Class TerminalFunctor `(_ : Terminal C) `(_ : Terminal D) := {
  terminal_category_functor :> @CategoryFunctor C _ D _;

  map_one : One ~> fobj One;

  fmap_one : ∀ {X : C}, fmap one ≈ map_one ∙ @one _ _ (fobj X)
}.

Arguments TerminalFunctor C {_} D {_}.

Class CartesianFunctor `(_ : Cartesian C) `(_ : Cartesian D) := {
  terminal_functor :> TerminalFunctor C D;

  fobj_prod_iso : ∀ {X Y : C}, fobj (Prod X Y) ≅ Prod (fobj X) (fobj Y);

  prod_one_right_iso : ∀ {X Y : C}, Prod X One ≅ X;
  prod_one_left_iso  : ∀ {X Y : C}, Prod One X ≅ X;

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

Corollary prod_in_out `{CartesianFunctor C D} : forall(X Y : C),
  prod_in ∙ prod_out ≈ @id _ _ (fobj (Prod X Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_prod_iso _ _ _ _ _ X Y))).
Qed.

Corollary prod_out_in `{CartesianFunctor C D} : forall(X Y : C),
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

  exp_one_iso : ∀ {X Y : C}, Exp One X ≅ X;

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

Corollary exp_in_out `{ClosedFunctor C D} : forall(X Y : C),
  exp_in ∙ exp_out ≈ @id _ _ (fobj (Exp X Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_exp_iso _ _ _ _ _ X Y))).
Qed.

Corollary exp_out_in `{ClosedFunctor C D} : forall(X Y : C),
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

Infix "==>" := rel.

Theorem ccc_id : ∀ (a : Type), (λ x : a, x) ==> id.
Proof.
  unfold rel; intros.
  rewrite <- fmap_id.
  reflexivity.
Qed.

Theorem ccc_apply :
  ∀ (a b c : Type)
    (U : a -> b -> c) (U' : fobj a ~> Exp (fobj b) (fobj c))
    (V : a -> b) (V' : fobj a ~> fobj b),
  U ==> exp_in ∙ U' ->
  V ==> V' ->
    (λ x, U x (V x)) ==> apply ∙ (U' △ V').
Proof.
  unfold rel; intros; subst.
  replace (λ x, U x (V x))
     with (λ x, @apply Type _ b c (U x, V x)) by auto.
  replace (λ x, @apply Type _ b c (U x, V x))
     with (λ x, @apply Type _ b c ((U △ V) x)) by auto.
  replace (λ x, @apply Type _ b c ((U △ V) x))
     with (@apply Type _ b c ∙ (U △ V)) by auto.
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
    U ==> U' ∙ prod_out ->
      (λ x, λ y, U (x, y)) ==> exp_in ∙ curry U'.
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
  (λ _ : a, tt) ==> map_one ∙ @one _ _ (fobj a).
Proof.
  unfold rel; intros.
  replace (λ _ : a, ()) with (@one _ _ a) by auto.
  pose proof @fmap_one.
  simpl in H0.
  rewrite H0.
  reflexivity.
Qed.

End CCC.

End CCC.

Module Expr.

Section Expr.

Inductive Obj : Type :=
  | One_  : Obj
  | Prod_ : Obj -> Obj -> Obj
  | Exp_  : Obj -> Obj -> Obj.

Inductive Cat : Obj -> Obj -> Type :=
  | Id      : ∀ a, Cat a a
  | Compose : ∀ a b c, Cat b c -> Cat a b -> Cat a c

  | One'    : ∀ a, Cat a One_

  | Exl     : ∀ a b, Cat (Prod_ a b) a
  | Exr     : ∀ a b, Cat (Prod_ a b) b
  | Fork    : ∀ a c d, Cat a c -> Cat a d -> Cat a (Prod_ c d)

  | Apply   : ∀ a b, Cat (Prod_ (Exp_ a b) a) b
  | Curry   : ∀ a b c, Cat (Prod_ a b) c -> Cat a (Exp_ b c)
  | Uncurry : ∀ a b c, Cat a (Exp_ b c) -> Cat (Prod_ a b) c.

  (* | Zero    : ∀ a, Cat Zero a *)

  (* | Inl     : ∀ a b, Cat a (Sum a b) *)
  (* | Inr     : ∀ a b, Cat b (Sum a b) *)
  (* | Join    : ∀ a c d, Cat c a -> Cat d a -> Cat (Sum c d) a *)

  (* | Distl   : ∀ u v a, Cat (Prod (Sum u v) a) (Sum (Prod u a) (Prod v a)) *)
  (* | Distr   : ∀ b u v, Cat (Prod b (Sum u v)) (Sum (Prod b u) (Prod b v)). *)

End Expr.

Fixpoint denote (o : Obj) : ∀ `{Closed C}, C :=
  fun _ _ => match o with
  | One_ => One
  | Prod_ x y => Prod (denote x) (denote y)
  | Exp_ x y => Exp (denote x) (denote y)
  end.

Fixpoint eval `(c : Cat a b) :
  ∀ `{Closed C}, denote a ~{C}~> denote b := fun _ _ =>
  match c with
  | Id _              => id
  | Compose _ _ _ f g => eval f ∙ eval g

  | One' A            => one

  | Exl a b           => exl
  | Exr _ _           => exr
  | Fork _ _ _ f g    => fork (eval f) (eval g)

  | Apply _ _         => apply
  | Curry _ _ _ f     => curry (eval f)
  | Uncurry _ _ _ f   => uncurry (eval f)

  (* | Zero _            => zero *)

  (* | Inl _ _           => inl *)
  (* | Inr _ _           => inl *)
  (* | Join _ _ _ f g    => join (eval f) (eval g) *)

  (* | Distl _ _ _       => _ *)
  (* | Distr _ _ _       => _ *)
  end.

Program Instance Cat_Category : Category Obj := {
  hom := Cat;
  id := Id;
  compose := Compose;
  eqv := fun _ _ f g => ∀ `{Closed C}, @eqv C _ _ _ (eval f) (eval g)
}.
Obligation 1.
  constructor.
  - intros ???.
    reflexivity.
  - intros ?????.
    symmetry.
    apply H.
  - intros ???????.
    rewrite H, H0.
    reflexivity.
Defined.
Obligation 2.
  intros ????????.
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

Program Instance Cat_Terminal : Terminal Obj := {
  terminal_category := Cat_Category;
  One := One_;
  one := One'
}.

Program Instance Cat_Cartesian : Cartesian Obj := {
  cartesian_terminal := Cat_Terminal;
  Prod := Prod_;
  fork := Fork;
  exl  := Exl;
  exr  := Exr
}.
Obligation 1.
  intros ????????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 2.
  split; intros.
    split; intros ??.
      rewrite H.
      rewrite exl_fork.
      reflexivity.
    rewrite H.
    rewrite exr_fork.
    reflexivity.
  destruct H.
  rewrite <- H.
  rewrite <- H1.
  rewrite fork_compose.
  rewrite fork_exl_exr.
  rewrite id_left.
  reflexivity.
Qed.

Program Instance Cat_Closed : Closed Obj := {
  closed_cartesian := Cat_Cartesian;
  Exp := Exp_;
  apply := Apply;
  curry := Curry;
  uncurry := Uncurry
}.
Obligation 1.
  intros ?????.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Obligation 2.
  intros ?????.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Obligation 3.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.
Obligation 6.
Admitted.

Program Instance Cat_CategoryFunctor `{H : Closed C} :
  CategoryFunctor Obj C := {
  fobj := fun x => denote x;
  fmap := fun _ _ f => eval f
}.

Program Instance Cat_TerminalFunctor `{H : Closed C} :
  TerminalFunctor Obj C := {
  map_one := id
}.
Obligation 1.
  rewrite id_left.
  reflexivity.
Qed.

Program Instance Cat_CartesianFunctor `{H : Closed C} :
  CartesianFunctor Obj C := {
  fobj_prod_iso := _;

  prod_one_right_iso := _;
  prod_one_left_iso  := _
}.
Obligation 1.
  simpl.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor; rewrite id_left; reflexivity.
Defined.
Obligation 2.
  simpl.
Admitted.
Obligation 3.
  simpl.
Admitted.
Obligation 4.
  simpl.
Admitted.
Obligation 5.
  simpl.
Admitted.
Obligation 6.
  simpl.
Admitted.

(*
Program Instance Free_CategoryFunctor `{H : Closed C} `{Represented C} :
  CategoryFunctor
    (terminal_category
       (Terminal:=cartesian_terminal
                    (Cartesian:=@closed_cartesian C H)))
    Cat_Category := {
  fobj := fun x => @repr C _ x _;
  fmap := fun _ _ f => _
}.
*)

(* Program Instance Cat_Initial : Initial Obj := { *)
(*   initial_category := Cat_Category; *)
(*   Zero := False; *)
(*   zero := fun _ _ => False_rect _ _ *)
(* }. *)

(* Program Instance Cat_Cocartesian : Cocartesian Obj := { *)
(*   cocartesian_initial := Cat_Initial; *)
(*   Sum := sum; *)
(*   join := fun _ _ _ f g x => *)
(*             match x with *)
(*             | Datatypes.inl v => f v *)
(*             | Datatypes.inr v => g v *)
(*             end; *)
(*   inl  := fun _ _ p => Datatypes.inl p; *)
(*   inr  := fun _ _ p => Datatypes.inr p *)
(* }. *)

(* Program Instance Cat_Bicartesian : Bicartesian Cat_Cartesian Cat_Cocartesian. *)

(* Program Instance Cat_Distributive : Distributive Cat_Bicartesian. *)

(* Program Instance Cat_Constant {A : Obj} : Constant Obj A := { *)
(*   intro := fun b _ => b *)
(* }. *)

End Expr.

(*
Hint Rewrite (@apply_curry_law arrow Cat_Closed) : ccc.

Class ConstCat (ob : Type -> Type -> Type) (b : Type) := {
  constcat_terminal :> Terminal ob;
  unitArrow : b -> ob unit b
}.

Program Instance Cat_ConstCat (b : Type) : ConstCat arrow b := {
  unitArrow := fun b _ => b
}.

(* Definition const `{ConstCat ob b} (x : b) `(f : ob a b) := *)
(*     unitArrow x ∘ that a. *)

Class BoolCat (ob : Type -> Type -> Type) := {
  boolcat_cartesian :> Cartesian ob;
  notC : ob bool bool;
  andC : ob (bool * bool) bool;
  orC  : ob (bool * bool) bool
}.

Program Instance Cat_BoolCat : BoolCat arrow := {
  notC := negb;
  andC := uncurry andb;
  orC := uncurry orb
}.

Class NumCat (ob : Type -> Type -> Type) (a : Type) := {
  negateC : ob a a;
  addC : ob (a * a) a;
  mulC : ob (a * a) a
}.

Program Instance Cat_NumCat : NumCat arrow Z := {
  negateC := fun x => (0 - x)%Z;
  addC := uncurry Zplus;
  mulC := uncurry Zmult
}.

Definition sqr (x : Z) : Z := x * x.

Record HasClosed (A B : Type) := {
  arrowType : Type -> Type -> Type;
  _ : Closed arrowType;
  function : arrowType A B
}.

Require Import FunctionalExtensionality.

Corollary ccc_apply `(V : A) `(U : A -> B) : U V = apply (U, V).
Proof. reflexivity. Qed.

Corollary ccc_fork (T : Type) `(U : T -> A -> B) (V : T -> A) (x : T) :
  (U x, V x) = (U △ V) x.
Proof. reflexivity. Qed.

Corollary ccc_uncurry `(U : A -> B -> C) (x : A) (y : B) :
  U x y = uncurry U (x, y).
Proof. reflexivity. Qed.

Corollary ccc_curry `(U : A * B -> C) (x : A) (y : B) :
  U (x, y) = curry U x y.
Proof. reflexivity. Qed.

Lemma ccc_compose `(U : A -> (B -> C) * B) `(f : A -> C) (x : A) :
  apply ∘ U = f -> @apply arrow _ _ _ (U x) = f x.
Proof.
  simpl; intros.
  rewrite <- H.
  reflexivity.
Qed.

Ltac ccc :=
  repeat match goal with
  | [ |- { f : _ | f arrow Cat_Closed Cat_NumCat = ?F } ] =>
    eexists; unfold F; symmetry

  | [ |- (fun _ : ?T => _) = _ ]      => let x := fresh "x" in extensionality x
  | [ |- context [Z.mul] ]            => replace Z.mul with (curry mulC) by auto
  | [ |- apply (?F ?X, ?X) = _ ]      => replace (F X, X) with (F X, id X) by auto
  | [ |- apply (?X, ?F ?X) = _ ]      => replace (X, F X) with (id X, F X) by auto
  | [ |- apply (?F ?X, ?G ?X) = _ ]   => rewrite ccc_fork with (U:=F) (V:=G)
  | [ |- apply (?F ?X) = _ _ _ _ ?X ] => apply ccc_compose
  | [ |- apply ?F = _ ]               => idtac
  | [ |- apply ∘ ?F = _ ]             => idtac
  | [ |- ?F ?X = _ ]                  => rewrite ccc_apply with (U := F)
  end;
  repeat autorewrite with ccc.

Ltac higher_order_1_reflexivity' :=
  let a := match goal with |- ?R ?a (?f ?x) => constr:(a) end in
  let f := match goal with |- ?R ?a (?f ?x) => constr:(f) end in
  let x := match goal with |- ?R ?a (?f ?x) => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [reflexivity].

Lemma abstract_compose A B C f g :
  @compose arrow Cat_Category A B C f g = (fun _ _ => @compose arrow Cat_Category A B C f g) arrow Cat_Category.
Admitted.

Theorem sqr_cat  :
  { f : ∀ (ob : Type -> Type -> Type) `{Closed ob} `{NumCat ob Z}, ob Z Z
  | f arrow Cat_Closed Cat_NumCat = sqr }.
Proof.
  ccc.
  instantiate (1 := fun _ _ _ => _); hnf.
  (* I cannot automate this yet because I get the following:

       Unable to unify "?Goal@{T:=arrow; c:=Cat_Closed; n:=Cat_NumCat}" with
       "mulC ∘ (id △ id)"
       (unable to find a well-typed instantiation for "?Goal": cannot ensure that
       "arrow Z Z" is a subtype of "T Z Z").

     How do I tell Coq that in an environment where [T:=arrow], [arrow] must
     always be a subtype of [T]?

     For now I just copy the syntax show in the goal. *)
  instantiate (1 := mulC ∘ (id △ id)).
  reflexivity.
Defined.

Require Import Coq.Strings.String.

Open Scope string_scope.

Inductive Const (A B : Type) := mkC : string -> Const A B.

Arguments mkC {A B} _.

Definition unC `(x : Const A B) := match x with mkC s => s end.

Program Instance Const_Category : Category Const := {
  id := fun _ => mkC "id";
  compose := fun _ _ _ g f =>
    mkC (unC g ++ " ∘ " ++ unC f)
}.

Program Instance Const_Cartesian : Cartesian Const := {
  fork := fun _ _ _ f g => mkC (unC f ++ " △ " ++ unC g);
  exl  := fun _ _ => mkC "exl";
  exr  := fun _ _ => mkC "exr"
}.

Program Instance Const_Terminal : Terminal Const := {
  that := fun _ => mkC "that"
}.

Program Instance Const_Closed : Closed Const := {
  apply := fun _ _ => mkC "apply";
  curry := fun _ _ _ f => mkC "curry";
  uncurry := fun _ _ _ f => mkC "uncurry"
}.
Obligation 1.
Admitted.  (* we don't care about string differences *)

Program Instance Const_ConstCat (b : Type) : ConstCat Const b := {
  unitArrow := fun b => mkC "unitArrow"
}.

Program Instance Const_BoolCat : BoolCat Const := {
  notC := mkC "notC";
  andC := mkC "andC";
  orC := mkC "orC"
}.

Program Instance Const_NumCat : NumCat Const Z := {
  negateC := mkC "negateC";
  addC := mkC "addC";
  mulC := mkC "mulC"
}.

Definition sqr_cat' := Eval compute in proj1_sig sqr_cat.
Print sqr_cat'.

Compute unC (sqr_cat' Const _ Const_NumCat).
(*
     = "mulC ∘ id △ id"
     : string
*)

Inductive TeletypeF a b r :=
  | Get : (a -> r) -> TeletypeF a b r
  | GetMany : ((∀ s : Type, s -> (a -> s -> s) -> s) -> r) -> TeletypeF a b r
  | Put : b -> r -> TeletypeF a b r.

Arguments Get {a b r} ob.
Arguments GetMany {a b r} ob.
Arguments Put {a b r} x z.

Program Instance TeletypeF_Functor {a b} : Functor (@TeletypeF a b) := {
  fmap := fun _ _ f x => match x with
    | Get ob     => Get (f \o ob)
    | GetMany ob => GetMany (f \o ob)
    | Put b r   => Put b (f r)
    end
}.

Section Kleisli.

Context `{Monad m}.

Definition kleisli (A B : Type) := A -> m B.

Program Instance Kleisli_Category : Category kleisli := {
  id := fun _ x => pure x;
  compose := fun _ _ _ g f => g <=< f
}.

Program Instance Kleisli_Cartesian : Cartesian kleisli := {
  fork := fun _ _ _ f g x => liftA2 (fun x y => (x, y)) (f x) (g x);
  exl  := fun _ _ p => pure (fst p);
  exr  := fun _ _ p => pure (snd p)
}.

Program Instance Kleisli_Terminal : Terminal kleisli := {
  that := fun _ a => pure tt
}.

Program Instance Kleisli_Closed : Closed kleisli := {
  apply := fun _ _ p => fst p (snd p);
  curry := fun _ _ _ f x => _;
  uncurry := fun _ _ _ f p => f (fst p) >>= fun ob => ob (snd p)
}.
Obligation 1.
  unfold kleisli in *.
  eapply fmap; intros.
    exact (f (x, X0)).
  instantiate (1 := unit).
  exact (pure tt).
Defined.
Obligation 2.
  unfold Kleisli_Closed_obligation_1.
Admitted.

Program Instance Kleisli_ConstCat (b : Type) : ConstCat kleisli b := {
  unitArrow := fun b _ => pure b
}.

Program Instance Kleisli_BoolCat : BoolCat kleisli := {
  notC := fun b => pure (negb b);
  andC := fun p => pure (andb (fst p) (snd p));
  orC  := fun p => pure (orb (fst p) (snd p))
}.

Program Instance Kleisli_NumCat : NumCat kleisli Z := {
  negateC := fun x => pure (0 - x)%Z;
  addC := fun p => pure (Zplus (fst p) (snd p));
  mulC := fun p => pure (Zmult (fst p) (snd p))
}.

End Kleisli.

Definition Teletype a b := Free (TeletypeF a b).

Definition get {a b} : Teletype a b a := liftF (Get id).
Definition put {a b} (x : b) : Teletype a b unit := liftF (Put x tt).

Definition foo : Teletype nat nat unit :=
  x <- get;
  put x;;
  put x.

Class TeletypeCat (ob : Type -> Type -> Type) (a : Type) := {
  getC : ob unit a;
  putC : ob a unit
}.

Program Instance Kleisli_TeletypeCat : TeletypeCat (@kleisli (Teletype nat nat)) nat := {
  getC := fun _ => get;
  putC := put
}.

Theorem foo_cat  :
  { f : ∀ (ob : Type -> Type -> Type) `{Closed ob} `{TeletypeCat ob nat}, ob unit unit
  | f (@kleisli (Teletype nat nat)) Kleisli_Closed Kleisli_TeletypeCat = fun _ => foo }.
Proof.
  eexists.
  unfold foo.
  symmetry.
  instantiate (1 := fun _ _ _ => _).
  instantiate (1 := (exl ∘ (putC △ putC)) ∘ getC).
  compute.
  extensionality u; destruct u.
  f_equal.
  extensionality x.
  f_equal.
  extensionality u; destruct u.
  f_equal.
  extensionality u; destruct u.
  reflexivity.
Defined.

Definition foo_cat' := Eval compute in proj1_sig foo_cat.
Print foo_cat'.

Program Instance Const_TeletypeCat {a} : TeletypeCat Const a := {
  getC := mkC "getC";
  putC := mkC "putC"
}.

Compute unC (foo_cat' Const _ Const_TeletypeCat).
(*
     = "exl ∘ putC △ putC ∘ getC"
     : string
*)
*)