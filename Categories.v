Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Tactics.
Require Export Coq.ZArith.ZArith.

Generalizable All Variables.

Close Scope nat_scope.

Class Category (k : Type -> Type -> Type) := {
  id : forall {A}, k A A;
  compose : forall {A B C}, k B C -> k A B -> k A C
}.

Infix "∘" := compose (at level 40).

Definition arrow (A B : Type) := A -> B.

Program Instance Coq_Category : Category arrow := {
  id := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
}.

Class Cartesian (k : Type -> Type -> Type) := {
  cartesian_category :> Category k;
  fork : forall {A C D}, k A C -> k A D -> k A (C * D);
  exl  : forall {A B}, k (A * B) A;
  exr  : forall {A B}, k (A * B) B
}.

Infix "△" := fork (at level 40).

Program Instance Coq_Cartesian : Cartesian arrow := {
  fork := fun _ _ _ f g x => (f x, g x);
  exl  := fun _ _ p => fst p;
  exr  := fun _ _ p => snd p
}.

Class Terminal (k : Type -> Type -> Type) := {
  terminal_category :> Category k;
  it : forall {A}, k A unit
}.

Program Instance Coq_Terminal : Terminal arrow := {
  it := fun _ a => tt
}.

Class Closed (k : Type -> Type -> Type) := {
  closed_cartesian :> Cartesian k;
  apply : forall {A B}, k ((A -> B) * A) B;
  curry : forall {A B C}, k (A * B) C -> k A (B -> C);
  uncurry : forall {A B C}, k A (B -> C) -> k (A * B) C;

  apply_curry_law : forall {A B} {f : k (A * A) B},
    apply ∘ (curry f △ id) = f ∘ (id △ id)
}.

Program Instance Coq_Closed : Closed arrow := {
  apply := fun _ _ p => fst p (snd p);
  curry := fun _ _ _ f a b => f (a, b);
  uncurry := fun _ _ _ f p => f (fst p) (snd p)
}.

Hint Rewrite (@apply_curry_law arrow Coq_Closed) : ccc.

Class ConstCat (k : Type -> Type -> Type) (b : Type) := {
  constcat_terminal :> Terminal k;
  unitArrow : b -> k unit b
}.

Program Instance Coq_ConstCat (b : Type) : ConstCat arrow b := {
  unitArrow := fun b _ => b
}.

(* Definition const `{ConstCat k b} (x : b) `(f : k a b) := *)
(*     unitArrow x ∘ it a. *)

Class BoolCat (k : Type -> Type -> Type) := {
  boolcat_cartesian :> Cartesian k;
  notC : k bool bool;
  andC : k (bool * bool) bool;
  orC  : k (bool * bool) bool
}.

Program Instance Coq_BoolCat : BoolCat arrow := {
  notC := negb;
  andC := uncurry andb;
  orC := uncurry orb
}.

Class NumCat (k : Type -> Type -> Type) (a : Type) := {
  negateC : k a a;
  addC : k (a * a) a;
  mulC : k (a * a) a
}.

Program Instance Coq_NumCat : NumCat arrow Z := {
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
  | [ |- { f : _ | f arrow Coq_Closed Coq_NumCat = ?F } ] =>
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
  @compose arrow Coq_Category A B C f g = (fun _ _ => @compose arrow Coq_Category A B C f g) arrow Coq_Category.
Admitted.

Theorem sqr_cat  :
  { f : forall (k : Type -> Type -> Type) `{Closed k} `{NumCat k Z}, k Z Z
  | f arrow Coq_Closed Coq_NumCat = sqr }.
Proof.
  ccc.
  instantiate (1 := fun _ _ _ => _); hnf.
  (* I cannot automate this yet because I get the following:

       Unable to unify "?Goal@{T:=arrow; c:=Coq_Closed; n:=Coq_NumCat}" with
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
  it := fun _ => mkC "it"
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