Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Coq.Unicode.Utf8
  Coq.Program.Tactics
  Coq.ZArith.ZArith
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  Coq.Init.Datatypes
  Coq.Relations.Relation_Definitions
  Hask.Control.Monad
  Hask.Control.Monad.Free.

Generalizable All Variables.

Close Scope nat_scope.

Reserved Notation "f ∙ g" (at level 50).
Reserved Notation "f ~> g" (at level 50).

Class Category (ob : Type) := {
  uhom := Type : Type;
  hom  : ob → ob → uhom where "a ~> b" := (hom a b);

  id : ∀ {A}, A ~> A;
  compose : ∀ {A B C}, B ~> C -> A ~> B -> A ~> C
    where "f ∙ g" := (compose f g);

  id_left  : ∀ {X Y} {f : X ~> Y}, id ∙ f = f;
  id_right : ∀ {X Y} {f : X ~> Y}, f ∙ id = f;

  comp_assoc : ∀ {X Y Z W} {f : Z ~> W} {g : Y ~> Z} {h : X ~> Y},
    f ∙ (g ∙ h) = (f ∙ g) ∙ h
}.

Infix "~>" := hom (at level 50).
Infix "~{ C }~>" := (@hom C _) (at level 50).
Infix "∙" := compose (at level 50).

Notation "id[ X  ]" := (@id _ _ X)  (at level 50).

Definition arrow (A B : Type) := A -> B.

Program Instance Coq_Category : Category Type := {
  hom := arrow;
  id := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
}.

Class Cartesian (ob : Type) := {
  cartesian_category :> Category ob;

  Prod : ob -> ob -> ob;

  fork : ∀ {X Z W}, X ~> Z -> X ~> W -> X ~> Prod Z W;
  exl  : ∀ {X Y}, Prod X Y ~> X;
  exr  : ∀ {X Y}, Prod X Y ~> Y;

  univ_products : ∀ {X Y Z} {f : X ~> Y} {g : X ~> Z} {h : X ~> Prod Y Z},
    h = fork f g <-> exl ∙ h = f ∧ exr ∙ h = g
}.

Infix "△" := fork (at level 40).

Corollary exl_fork `{Cartesian C} : ∀ {X Z W} (f : X ~> Z) (g : X ~> W),
  exl ∙ f △ g = f.
Proof.
  intros.
  apply (proj1 (@univ_products C H _ _ _ f g (f △ g)) eq_refl).
Qed.

Corollary exr_fork `{Cartesian C} : ∀ {X Z W} (f : X ~> Z) (g : X ~> W),
  exr ∙ f △ g = g.
Proof.
  intros.
  apply (proj1 (@univ_products C H _ _ _ f g (f △ g)) eq_refl).
Qed.

Corollary fork_exl_exr `{Cartesian C} : ∀ {X Y},
  exl △ exr = @id C _ (Prod X Y).
Proof.
  intros.
  symmetry.
  apply (proj2 (@univ_products C H (Prod X Y) X Y exl exr id)).
  rewrite !id_right.
  auto.
Qed.

Corollary fork_compose `{Cartesian C} :
  ∀ {X Y Z V W} (f : Prod Y Z ~> V) (h : Prod Y Z ~> W) (g : X ~> Prod Y Z),
    (f ∙ g) △ (h ∙ g) = f △ h ∙ g.
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
  cartesian_category := Coq_Category;
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

Class Terminal (ob : Type) := {
  terminal_category :> Category ob;
  Terminus : Type;
  it : ∀ {A}, A ~> Terminus
}.

Program Instance Coq_Terminal : Terminal Type := {
  Terminus := unit : Type;
  it := fun _ a => tt
}.

Class Closed (ob : Type) := {
  closed_cartesian :> Cartesian ob;

  Exp : ob -> ob -> ob;   (* internal homs *)

  apply : ∀ {X Y}, Prod (Exp X Y) X ~> Y;
  curry : ∀ {X Y Z}, Prod X Y ~> Z -> X ~> Exp Y Z;
  uncurry : ∀ {X Y Z}, X ~> Exp Y Z -> Prod X Y ~> Z;

  curry_uncurry : ∀ {X Y Z} (f : X ~> Exp Y Z), curry (uncurry f) = f;
  uncurry_curry : ∀ {X Y Z} (f : Prod X Y ~> Z), uncurry (curry f) = f;

  curry_apply : ∀ {X Y}, curry apply = @id _ _ (Exp X Y);

  univ_exponentials : ∀ {X Y Z} (f : Prod X Y ~> Z),
    apply ∙ (curry f ∙ exl) △ exr = f
}.

Corollary apply_curry `{Closed C} :
  ∀ {X Y Z W} (f : Prod Y Z ~> W) (g : X ~> Y) (h : X ~> Z),
    apply ∙ ((curry f ∙ g) △ h) = f ∙ g △ h.
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
  extensionality p.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.
Obligation 4.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Class CategoryFunctor `(_ : Category C) `(_ : Category D) := {
  fobj : C -> D;
  fmap : ∀ {X Y : C}, X ~> Y → fobj X ~> fobj Y;

  fmap_id : ∀ {X : C}, fmap (@id C _ X) = id;
  fmap_comp : ∀ {X Y Z} (f : Y ~> Z) (g : X ~> Y),
    fmap (f ∙ g) = fmap f ∙ fmap g
}.

Notation "C ⟶ D" := (CategoryFunctor C D) (at level 90, right associativity).

Notation "fmap[ M ]" := (@fmap _ _ M _ _ _ _) (at level 9).

Class TerminalFunctor `(TC : Terminal C) `(TD : Terminal D) := {
  term_functor :> @CategoryFunctor C (@terminal_category C TC)
                                   D (@terminal_category D TD);
  term_eq : fobj (@Terminus C TC) ~> @Terminus D TD
}.

Class CartesianFunctor `(_ : Cartesian C) `(_ : Cartesian D) := {
  category_functor :> @CategoryFunctor C _ D _;

  prod_out : ∀ {X Y : C}, fobj (Prod X Y) ~> Prod (fobj X) (fobj Y);
  prod_in  : ∀ {X Y : C}, Prod (fobj X) (fobj Y) ~> fobj (Prod X Y);

  prod_out_in : ∀ {X Y : C}, prod_out ∙ prod_in = @id _ _ (Prod (fobj X) (fobj Y));
  prod_in_out : ∀ {X Y : C}, prod_in ∙ prod_out = @id _ _ (fobj (Prod X Y));

  fmap_exl : ∀ {X Y : C}, fmap (@exl C _ X Y) = exl ∙ prod_out;
  fmap_exr : ∀ {X Y : C}, fmap (@exr C _ X Y) = exr ∙ prod_out;
  fmap_fork : ∀ {X Y Z : C} (f : X ~> Y) (g : X ~> Z),
    fmap (f △ g) = prod_in ∙ fmap f △ fmap g
}.

Notation "prod_in[ C -> D | X ~> Y  ]" := (@prod_in C _ D _ _ X Y).
Notation "prod_out[ C -> D | X ~> Y  ]" := (@prod_out C _ D _ _ X Y).

Corollary prod_in_inj `{CartesianFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> Prod (fobj X) (fobj Y)),
    prod_in ∙ f = prod_in ∙ g <-> f = g.
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
  reflexivity.
Qed.

Corollary prod_out_inj `{CartesianFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> fobj (Prod Y Z)),
    prod_out ∙ f = prod_out ∙ g <-> f = g.
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
  reflexivity.
Qed.

Class ClosedFunctor `(_ : Closed C) `(_ : Closed D) := {
  cartesian_functor :> @CartesianFunctor C  _ D _;

  exp_out : ∀ {X Y : C}, fobj (Exp X Y) ~> Exp (fobj X) (fobj Y);
  exp_in  : ∀ {X Y : C}, Exp (fobj X) (fobj Y) ~> fobj (Exp X Y);

  exp_out_in : ∀ {X Y : C}, @exp_out X Y ∙ exp_in = id;
  exp_in_out : ∀ {X Y : C}, @exp_in X Y ∙ exp_out = id;

  fmap_apply : ∀ {X Y : C},
    fmap (@apply C _ X Y) = uncurry (curry apply ∙ exp_out) ∙ prod_out;
  fmap_curry : ∀ {X Y Z : C} {f : Prod X Y ~> Z},
    fmap (@curry C _ X Y Z f) = exp_in ∙ curry (fmap f ∙ prod_in);
  fmap_uncurry : ∀ {X Y Z : C} (f : X ~> Exp Y Z),
    fmap (@uncurry C _ X Y Z f) = uncurry (exp_out ∙ fmap f) ∙ prod_out
}.

Corollary exp_in_inj `{ClosedFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> Exp (fobj Y) (fobj Z)),
    exp_in ∙ f = exp_in ∙ g <-> f = g.
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
  reflexivity.
Qed.

Corollary exp_out_inj `{ClosedFunctor C D} :
  ∀ {X Y Z : C} (f g : fobj X ~> fobj (Exp Y Z)),
    exp_out ∙ f = exp_out ∙ g <-> f = g.
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
  reflexivity.
Qed.

Module CCC.

Section CCC.

Variable k : Type.
Context `{Closed k}.
Context `{F : @ClosedFunctor Type _ k _}.

Import EqNotations.

Definition rel `(lam : a -> b) (ccc : fobj a ~> fobj b) : Prop :=
  fmap (H:=cartesian_category
             (Cartesian:=closed_cartesian
                           (Closed:=Coq_Closed))) lam = ccc.

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
  pose proof (proj2 (exp_out_inj (fmap[ k] U) (exp_in ∙ U'))).
  apply H1 in H0.
  rewrite comp_assoc in H0.
  rewrite exp_out_in in H0.
  rewrite id_left in H0.
  subst.
  clear H1.
  rewrite curry_apply.
  rewrite id_left.
  rewrite <- apply_curry.
  rewrite curry_uncurry.
  reflexivity.
Qed.

Theorem ccc_curry :
  ∀ (a b c : Type)
    (U : a * b -> c) (U' : Prod (fobj a) (fobj b) ~> fobj c),
    U ==> U' ∙ prod_out ->
    (λ x, λ y, U (x, y)) ==> exp_in ∙ curry U'.
Proof.
  unfold rel; intros; subst.
  pose proof (@fmap_curry Type _ k _ _ a b c U).
  simpl in H1.
  unfold arrow in H1.
  simpl.
  rewrite H1; clear H1.
  pose proof (@exp_in_inj Type _ k _ _ a b c).
  apply H1; clear H1.
  simpl in H0.
  rewrite H0; clear H0.
  rewrite <- comp_assoc.
  pose proof (@prod_out_in Type _ k _ _ a b).
  simpl in H0.
  rewrite H0.
  rewrite id_right.
  reflexivity.
Qed.

Theorem ccc_const : ∀ (a b : Type) (c : b),
  (λ x : a, c) ==> fmap (@const b unit c) ∙ @it _ _ a.
Proof.
  unfold rel; intros.
  rewrite <- H0; clear H0.
  rewrite <- fmap_comp.
  reflexivity.
Qed.

Theorem ccc_const' : ∀ (a b : Type) (c : b),
  const c ==> fmap (@const b unit c) ∙ fmap it.
Proof.
  unfold rel; intros.
  rewrite <- H0; clear H0.
  rewrite <- fmap_comp.
  reflexivity.
Qed.

End CCC.

End CCC.

(*
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
  { f : ∀ (k : Type -> Type -> Type) `{Closed k} `{NumCat k Z}, k Z Z
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

Inductive TeletypeF a b r :=
  | Get : (a -> r) -> TeletypeF a b r
  | GetMany : ((∀ s : Type, s -> (a -> s -> s) -> s) -> r) -> TeletypeF a b r
  | Put : b -> r -> TeletypeF a b r.

Arguments Get {a b r} k.
Arguments GetMany {a b r} k.
Arguments Put {a b r} x z.

Program Instance TeletypeF_Functor {a b} : Functor (@TeletypeF a b) := {
  fmap := fun _ _ f x => match x with
    | Get k     => Get (f \o k)
    | GetMany k => GetMany (f \o k)
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
  it := fun _ a => pure tt
}.

Program Instance Kleisli_Closed : Closed kleisli := {
  apply := fun _ _ p => fst p (snd p);
  curry := fun _ _ _ f x => _;
  uncurry := fun _ _ _ f p => f (fst p) >>= fun k => k (snd p)
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

Class TeletypeCat (k : Type -> Type -> Type) (a : Type) := {
  getC : k unit a;
  putC : k a unit
}.

Program Instance Kleisli_TeletypeCat : TeletypeCat (@kleisli (Teletype nat nat)) nat := {
  getC := fun _ => get;
  putC := put
}.

Theorem foo_cat  :
  { f : ∀ (k : Type -> Type -> Type) `{Closed k} `{TeletypeCat k nat}, k unit unit
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