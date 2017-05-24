(**#+TITLE: galoisSolution.v

Proph

https://github.com/1337777/galois/blob/master/galoisSolution.v

solves some question of Galois [fn:1] which is how to program grammatical ("classifying")
functors-topos of some graph.

This starting lemma of polymorph mathematics ("categories") :

Coreflections( Set , Funtors( C* , Prop ) ) <=> Funtors( C , Set )

says that the senses ("functors models") onfrom some given primitive-syntax graph may be
instead dually-usefully-viewed as senses ("coreflective-functors models") into some
more-complete-grammatical ("classifying") functors-topos. And this starting lemma may be
upgraded such to perceive flat functors via geometric morphisms into some presheaf
functors-topos. Also this starting lemma may be upgraded such to perceive continuous flat
functors via geometric morphisms into some sheaf functors-topos ...

The question is whether these new more-complete-grammatical functors-topos are relatively
computational/decidable ? Some promised COQ program shall/may OK these. Promise only ...


[fn:1] ~Galois~ «Théorie des topos et cohomologie étale des schémas»

**)

(**

#+BEGIN_SRC coq :exports both :results silent **)

Require Import borceuxSolution_half_old.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import Setoid.
Require Omega. 

Set Implicit Arguments.
Unset Strict Implicits.
Unset Printing Implicit Defensive.

(**#+END_SRC

#+BEGIN_SRC coq :exports both :results silent **)

Parameter obIndexer : Type (* regular cardinal *).
Parameter Indexer : obIndexer -> obIndexer -> Type.
Notation "''Indexer' (0 A1 ~> A2 )0" :=
  (@Indexer A1 A2) (at level 25, format "''Indexer' (0  A1  ~>  A2  )0").
Parameter polyIndexer : forall (A2 A1 : obIndexer),
    Indexer A2 A1 -> forall A1' : obIndexer, (Indexer A1 A1') -> (Indexer A2 A1').
Notation "a_ o>Indexer a'" :=
  (@polyIndexer _ _ a_ _ a') (at level 25, right associativity).
Parameter unitIndexer : forall {A : obIndexer}, Indexer A A.
Parameter convIndexer : forall (A1 A2 : obIndexer),
    'Indexer(0 A1 ~> A2 )0 -> 'Indexer(0 A1 ~> A2 )0 -> Prop.
Notation "a2 ~~ a1" := (@convIndexer _ _ a2 a1) (at level 70).

Inductive obTopos : Type :=
| View0 : forall A : obIndexer, obTopos
| MetaFunctor : forall (func0 : obIndexer -> Type)
                  (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    obTopos.

Reserved Notation "''Topos' (0 F1 ~> F2 )0"
         (at level 25, format "''Topos' (0  F1  ~>  F2  )0").

(*
Inductive Topos00 : obTopos -> obTopos -> Type :=
| UnitTopos : forall {F : obTopos}, 'Topos(0 F ~> F )0
| PolyTopos : forall (F2 : obTopos) (F1 : obTopos)
  , 'Topos(0 F2 ~> F1 )0 -> forall F1' : obTopos,
      'Topos(0 F1 ~> F1' )0 -> 'Topos(0 F2 ~> F1' )0
| View1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 ->
                                'Topos(0 (View0 A') ~> (View0 A) )0
| MetaFunctor1 : forall (func0 : obIndexer -> Type)
                   (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
              forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> (MetaFunctor0 func1) )0
| Transf : forall (func0 : obIndexer -> Type)
             (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall (transf : forall A : obIndexer, func0 A -> func'0 A),
    forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> (MetaFunctor0 func'1) )0
where "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2).*)

Inductive Topos00 : obTopos -> obTopos -> Type :=

| UnitTopos : forall {F : obTopos}, 'Topos(0 F ~> F )0

| PolyTopos : forall (F2 : obTopos) (F1 : obTopos)
  , 'Topos(0 F2 ~> F1 )0 -> forall F1' : obTopos,
      'Topos(0 F1 ~> F1' )0 -> 'Topos(0 F2 ~> F1' )0

| View1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 ->
                                'Topos(0 (View0 A) ~> (View0 A') )0

| PolyMetaFunctor :
    forall (func0 : obIndexer -> Type (* regular cardinal *))
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      (forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)

| PolyMetaTransf :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      (forall (A : obIndexer), 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0
                          -> 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0)

| CoLimitator :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      (* cocone func1 v_ ->    cocone erased *)
      'Topos(0 (MetaFunctor func1) ~> F )0

where "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2).

Notation "'uTopos'" := (@UnitTopos _)(at level 0).
Notation "@ 'uTopos' F" :=
  (@UnitTopos F) (at level 11, only parsing).

Notation "f_ o>Topos f'" :=
  (@PolyTopos _ _ f_ _ f') (at level 25, right associativity).

Notation "f o>Topos_ transf" :=
  (@PolyMetaTransf _ _ _ _ transf _ f) (at level 25, right associativity).

Notation "[[ v_ @ func1 ]]" :=
  (@CoLimitator _ func1 _ v_ ) (at level 0).

Notation "[[ v_ ]]" :=
  (@CoLimitator _ _ _ v_ ) (at level 0).

Ltac rewriterTopos := repeat match goal with | [ HH : @eq (Topos00 _ _) _ _  |- _ ] =>  try rewrite -> HH in *; clear HH end. 


Reserved Notation "f2 ~~~ f1"  (at level 70).

(* Definition CoLimitator_Inject
           (func0 : obIndexer -> Type)
           (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A) (*lacked?*)
           (func'0 : obIndexer -> Type)
           (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
           (transf : forall A : obIndexer, func0 A -> func'0 A) : 
  'Topos(0 (MetaFunctor func1) ~> (MetaFunctor func'1) )0
   :=  [[Pol func1 func'1 transf]]. *)

Inductive convTopos : forall (F1 F2 : obTopos),
    'Topos(0 F1 ~> F2 )0 -> 'Topos(0 F1 ~> F2 )0 -> Prop :=

(* equivalence *)
  
| Topos_Refl : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
    f ~~~ f
      
| Topos_Trans : forall (F1 F2 : obTopos) (uTrans f : 'Topos(0 F1 ~> F2 )0),
    uTrans ~~~ f -> forall (f0 : 'Topos(0 F1 ~> F2 )0),
      f0 ~~~ uTrans -> f0 ~~~ f
                         
| Topos_Sym : forall (F1 F2 : obTopos) (f f0 : 'Topos(0 F1 ~> F2 )0),
    f ~~~ f0 -> f0 ~~~ f

(* congruences *)
                  
| PolyTopos_cong :
    forall (F F' : obTopos) (f_ f_0 : 'Topos(0 F ~> F' )0),
    forall (F'' : obTopos) (f' f'0 : 'Topos(0 F' ~> F'' )0),
      f_0 ~~~ f_ -> f'0 ~~~ f' -> ( f_0 o>Topos f'0 ) ~~~ ( f_ o>Topos f' )

| View_cong : forall (A A' : obIndexer) (a a0 : 'Indexer(0 A ~> A' )0),
    a0 ~~ a -> View1 a0 ~~~ ( View1 a
                             : 'Topos(0 View0 A ~> View0 A' )0 )

| PolyMetaFunctor_cong :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (A : obIndexer) (x x0 : func0 A),
      x0 = x -> PolyMetaFunctor func1 x0 ~~~ ( (PolyMetaFunctor func1 x)
                                              : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)
                               
| PolyMetaTransf_cong :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
    forall (A : obIndexer) (v v0 : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
      (* none lack to hold changes to transf because no such changes and uniform *)
      v0 ~~~ v -> v0 o>Topos_transf ~~~ ( v o>Topos_transf
                                          : 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0 )

| CoLimitator_cong :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (v_ v_0 : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      (* cocone func1 f_ ->    cocone erased *)
      ( forall (A : obIndexer) (x : func0 A), v_0 A x ~~~ v_ A x ) 
      ->  [[ v_0 @ func1 ]] ~~~ ( [[ v_ @ func1 ]]
                                 : 'Topos(0 MetaFunctor func1 ~> F )0 )

(* units *)

| Topos_unit :
    forall (F F' : obTopos) (f : 'Topos(0 F ~> F' )0),
      ( f )
        ~~~ ( ( uTopos ) o>Topos f
              : 'Topos(0 F ~> F' )0 )

| Topos_inputUnitTopos :
    forall (G F : obTopos) (g : 'Topos(0 G ~> F )0),
      ( g )
        ~~~  ( g o>Topos ( uTopos )
               : 'Topos(0 G ~> F )0 )

(* for sense only, non-necessary for reduction *)
| View_unitIndexer : forall (A : obIndexer),
    ( @UnitTopos (View0 A) )
      ~~~ ( View1 (@unitIndexer A)
            : 'Topos(0 View0 A ~> View0 A )0 )

(* polymorphism *)

(* non for reduction *)
| Topos_morphism :
    forall (G F : obTopos) (g : 'Topos(0 G ~> F )0)
      (F' : obTopos) (f_ : 'Topos(0 F ~> F' )0)
      (F'' : obTopos) (f' : 'Topos(0 F' ~> F'' )0),
      ( g o>Topos ( f_ o>Topos f' ) )
        ~~~ ( ( g o>Topos f_ ) o>Topos f'
              : 'Topos(0 G ~> F'' )0 )

| View_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A ~> A' )0)
                       (A'' : obIndexer) (a' : 'Indexer(0 A' ~> A'' )0),
    (View1 (a o>Indexer a'))
      ~~~ ( (View1 a) o>Topos (View1 a')
            : 'Topos(0 View0 A ~> View0 A'' )0 )

(* functoriality-polymorphism follows from this _cocone property and
associativity-polymorphism of PolyTopos and functoriality-polymorphism
of View1 *)
| PolyMetaFunctor_cocone :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (A : obIndexer) (x : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( PolyMetaFunctor func1 (func1 _ _ a x) )
        ~~~ ( (View1 a) o>Topos (PolyMetaFunctor func1 x)
              : 'Topos(0 View0 A' ~> MetaFunctor func1 )0 )

(* naturality-polymorphism is this, which is in operational form *)
| PolyMetaTransf_poly :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
      (transf : forall A : obIndexer, func0 A -> func'0 A),
    forall (A : obIndexer) (v : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)
      (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( ((View1 a) o>Topos v) o>Topos_transf )
        ~~~ ( (View1 a) o>Topos (v o>Topos_transf)
              : 'Topos(0 View0 A' ~> MetaFunctor func'1 )0 )

(* naturality-polymorphism of the bijection*)
| CoLimitator_morphism :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos) (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (F' : obTopos) (f : 'Topos(0 F ~> F' )0),
      ( [[ (fun A x => (v_ A x) o>Topos f) @ func1 ]] )
        ~~~ ( [[ v_ @ func1 ]] o>Topos f
              : 'Topos(0 MetaFunctor func1 ~> F' )0 )

| PolyMetaFunctor_CoLimitator :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (A : obIndexer) (x : func0 A),
      ( v_ A x )
        ~~~ ( (PolyMetaFunctor func1 x) o>Topos [[ v_ @ func1 ]]
              : 'Topos(0 View0 A ~> F )0 )

| PolyMetaTransf_CoLimitator :
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall F : obTopos,
    forall (v_ : forall (A : obIndexer), func'0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A)
      (A : obIndexer) (w : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
      (w o>Topos [[ (fun A0 => (v_ A0) \o (transf A0)) @ func1 ]])
        ~~~ (w o>Topos_transf) o>Topos [[ v_ @ func'1 ]]

(* for sense only, non-necessary for reduction *)
| PolyMetaTransf_PolyMetaFunctor :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
      (transf : forall A : obIndexer, func0 A -> func'0 A),
    forall (A : obIndexer) (x : func0 A),
      ( PolyMetaFunctor func'1 (transf A x) )
        ~~~ ( (PolyMetaFunctor func1 x o>Topos_transf)
              : 'Topos(0 View0 A ~> MetaFunctor func'1 )0 )

(* for sense only, non-necessary for reduction *)
| CoLimitator_PolyMetaFunctor :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      ( @UnitTopos (MetaFunctor func1) )
        ~~~ ( [[ PolyMetaFunctor func1 ]]
              : 'Topos(0 (MetaFunctor func1) ~> (MetaFunctor func1) )0 )
        
where "f2 ~~~ f1" := (@convTopos _ _ f2 f1).

Hint Constructors convTopos.

Definition cocone_def := 
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos)
      (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (A : obIndexer) (x : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( v_ A' (func1 _ _ a x) )
        ~~~ ( (View1 a) o>Topos (v_ A x)
              : 'Topos(0 View0 A' ~> F )0 ) .

Notation cocone func1 v_ :=
  (forall (A : obIndexer) (x : _ A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( v_ A' (func1 _ _ a x) )
        ~~~ ( (View1 a) o>Topos (v_ A x)
              : 'Topos(0 View0 A' ~> _ )0 )) .

Check 
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos)
      (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      cocone func1 v_ ->
      'Topos(0 (MetaFunctor func1) ~> F )0.

Module Sol.

  Section Section1.

    Reserved Notation "''Topos' (0 F1 ~> F2 )0"
             (at level 25, format "''Topos' (0  F1  ~>  F2  )0").

    Inductive Topos00 : obTopos -> obTopos -> Type :=

    | UnitTopos : forall {F : obTopos}, 'Topos(0 F ~> F )0

    | View1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 ->
                                    'Topos(0 (View0 A) ~> (View0 A') )0

    | PolyMetaFunctor :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
          (forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)

    | PolyMetaTransf :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        forall (func'0 : obIndexer -> Type)
          (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
        forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
          (forall (A : obIndexer), 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0
                              -> 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0)

    | CoLimitator :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        forall F : obTopos,
        forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
          (* cocone func1 v_ ->    cocone erased *)
          'Topos(0 (MetaFunctor func1) ~> F )0

    where "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2).

  End Section1.

  Module Import Ex_Notations.
    Delimit Scope sol_scope with sol.
    Notation "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2) : sol_scope.
    Notation "'uTopos'" := (@UnitTopos _)(at level 0) : sol_scope. 
    Notation "@ 'uTopos' F" :=
      (@UnitTopos F) (at level 11, only parsing) : sol_scope.

    Notation "f o>Topos_ transf" :=
      (@PolyMetaTransf _ _ _ _ transf _ f) (at level 25, right associativity) : sol_scope.

    Notation "[[ v_ @ func1 ]]" :=
      (@CoLimitator _ func1 _ v_ ) (at level 0) : sol_scope.

    Notation "[[ v_ ]]" :=
      (@CoLimitator _ _ _ v_ ) (at level 0) : sol_scope.
  End Ex_Notations.

  Definition toTopos :
    forall (F1 F2 : obTopos), 'Topos(0 F1 ~> F2 )0 %sol -> 'Topos(0 F1 ~> F2 )0.
  Proof.
    (move => F1 F2 f); elim : F1 F2 / f =>
    [ F
    | A A' a
    | func0 func1 A x
    | func0 func1 func'0 func'1 transf A fSol fSol_toMod
    | func0 func1 F vSol_ vSol_toMod ];
      [ apply: (@uTopos F)
      | apply: (Top.View1 a)
      | apply: (Top.PolyMetaFunctor func1 x)
      | apply: (fSol_toMod o>Topos_transf)
      | apply: [[ vSol_toMod ]]
      ].
  Defined.

End Sol.

Module isSol.

  Inductive isSol : forall (F1 F2 : obTopos),
    'Topos(0 F1 ~> F2 )0 -> Type :=

  | UnitTopos : forall {F : obTopos}, isSol (@uTopos F)

  | View1 : forall (A A' : obIndexer), forall (a : 'Indexer(0 A ~> A' )0),
        isSol (Top.View1 a)

  | PolyMetaFunctor :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (A : obIndexer), forall (x : func0 A), isSol (Top.PolyMetaFunctor func1 x)

  | PolyMetaTransf :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
      forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      forall (A : obIndexer), forall (f : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
          isSol f -> isSol (f o>Topos_transf : 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0 )

  | CoLimitator :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall F : obTopos,
      forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
        (* cocone func1 v_ ->    cocone erased *)
        (forall A x, isSol (v_ A x)) -> isSol ([[v_ @ func1 ]]).

  Module destruct1.
    Inductive destruct1 : forall A : obIndexer,
      forall func0 : obIndexer -> Type,
      forall func1 : forall A A' : obIndexer, 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A,
        'Topos(0 View0 A ~> MetaFunctor func1 )0 -> Type :=
    | PolyMetaFunctor :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        forall (A : obIndexer), forall (x : func0 A), destruct1 (Top.PolyMetaFunctor func1 x)
    | PolyMetaTransf :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
      forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      forall (A : obIndexer), forall (f : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
          isSol f ->
          destruct1 (f o>Topos_transf : 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0).

    Lemma destruct1P : forall (F1 F2 : obTopos)
        (f : 'Topos(0 F1 ~> F2 )0),  isSol f ->
    (fun F1 : obTopos =>
 match F1 as o return (forall F2 : obTopos, 'Topos(0 o ~> F2 )0 -> Type) with
 | View0 A =>
     fun F2 : obTopos =>
     match F2 as o return ('Topos(0 View0 A ~> o )0 -> Type) with
     | View0 A0 => fun _ : 'Topos(0 View0 A ~> View0 A0 )0 => unit
     | @MetaFunctor func0 func1 => [eta destruct1 (func1:=func1)]
     end
 | @MetaFunctor func0 func1 =>
     fun (_tmp : obTopos) (_ : 'Topos(0 MetaFunctor func1 ~> _tmp )0) => unit
 end) F1 F2 f.
      intros F1 F2 f f_isSol. case: f / f_isSol.
      - simpl. destruct F; intros. exact: tt.  exact: tt.
      - intros. exact: tt.
      - intros.  constructor.
        intros. constructor. assumption.
      - intros. exact: tt.
    Defined.
  End destruct1.
  Definition isSolb : forall (F1 F2 : obTopos), forall (f : 'Topos(0 F1 ~> F2 )0),
        isSol f +  (isSol f -> False).
    (* move => F1 F2 f; elim : F1 F2 / f =>
    [ F
    | F1 F2 f_ IH_f_ F1' f' IH_f'
    | A A' a
    | func0 func1 A x
    | func0 func1 func'0 func'1 transf A f IH_f
    | func0 func1 F v_ IH_v_ ].
    - left; constructor.
    - right. intro. inversion X.
    - left; constructor.
    - left; constructor.
    - case: IH_f => IH_f; [ left; constructor; apply: IH_f | right; intro; apply:IH_f].
      move: X. move: (Logic.eq_refl (f o>Topos_transf :'Topos(0 View0 A ~> MetaFunctor func'1 )0 )).
      move: {-2}(f o>Topos_transf :'Topos(0 View0 A ~> MetaFunctor func'1 )0 ).

      intros. move: H. move: (destruct1P X) => LL. Set Printing Implicit.
      Show. move LL at top. destruct LL. inversion 1. injection 1. intros. subst. inversion 1.
       move : X. case: t / LL .
      case: (destruct1P X). intro K. case: (f o>Topos_transf) / K .  inversion K.
      inversion_clear H.
      

      right. move : (Logic.eq_refl (f_ o>Topos f')). move : {-2}(f_ o>Topos f').
      move => t HH JJ. move: HH. case: t / JJ. case : (f_ o>Topos f') / H .
      [ left; constructor
      | apply: (Top.View1 a)
      | apply: (Top.PolyMetaFunctor func1 x)
      | apply: (fSol_toMod o>Topos_transf)
      | apply: [[ vSol_toMod ]]
      ].
      *)
  Admitted.

  Definition isSolbb : forall (F1 F2 : obTopos), forall (f : 'Topos(0 F1 ~> F2 )0), bool.
    intros. apply: (isSolb f).
  Defined.

  Import Sol.Ex_Notations.
  Lemma isSol_toTopos : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      isSol f -> ({ fSol : 'Topos(0 F1 ~> F2 )0 %sol | Sol.toTopos fSol = f}).
  Admitted.
  Lemma toTopos_isSol : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      ({ fSol : 'Topos(0 F1 ~> F2 )0 %sol | Sol.toTopos fSol = f}) -> isSol f.
  Admitted.

End isSol.


(* add indexer type parameter T instead of obIndexer *)
Definition regularCardinalMax : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                     (filter : (forall (A : obIndexer), func0 A -> Prop)),
    (forall (A : obIndexer), func0 A -> nat) -> nat.
Admitted.
Lemma regularCardinalMax_falsefilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                         (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x <-> False) ->
      regularCardinalMax filter v_ = 0 .
Admitted.
Lemma regularCardinalMax_subfilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
    forall (filter' : (forall (A : obIndexer), func0 A -> Prop)),
      (forall A x, filter' A x -> filter A x) ->
      ( regularCardinalMax filter' v_ <= regularCardinalMax filter v_ )%coq_nat.
Admitted.
Lemma regularCardinalMax_samefilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
    forall (filter' : (forall (A : obIndexer), func0 A -> Prop)),
      (forall A x, filter' A x <-> filter A x) ->
      ( regularCardinalMax filter' v_ = regularCardinalMax filter v_ )%coq_nat.
Admitted.
Lemma regularCardinalMax_unionfilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                       (filter filter' : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
      ( regularCardinalMax (fun A x => filter A x \/ filter' A x) v_ <= (regularCardinalMax filter v_ + regularCardinalMax filter' v_)%coq_nat )%coq_nat.
Admitted.
Lemma regularCardinalMax_congr : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x -> ( w_ A x = v_ A x )%coq_nat) ->
      ( regularCardinalMax filter w_ = regularCardinalMax filter v_ )%coq_nat.
Admitted.
Lemma regularCardinalMax_monotone_ge : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x -> ( w_ A x <= v_ A x )%coq_nat) ->
      ( regularCardinalMax filter w_ <= regularCardinalMax filter v_ )%coq_nat.
Admitted.
Lemma regularCardinalMax_monotone_gt : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x -> ( w_ A x < v_ A x )%coq_nat) ->
      forall A x, filter A x -> ( w_ A x < v_ A x )%coq_nat ->
             ( regularCardinalMax filter w_ < regularCardinalMax filter v_ )%coq_nat.
Admitted.
Lemma regularCardinalMax_addr_const : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      regularCardinalMax filter (fun A x => (v_ A x + n)%coq_nat) = ((regularCardinalMax filter v_) + n)%coq_nat.
Admitted.
Lemma regularCardinalMax_addl_const : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      regularCardinalMax filter (fun A x => (n + v_ A x)%coq_nat) = (n + (regularCardinalMax filter v_))%coq_nat.
Admitted.
Lemma regularCardinalMax_add_succ : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
      regularCardinalMax filter (fun A x => S (v_ A x)%coq_nat) = (S (regularCardinalMax filter v_))%coq_nat.
Admitted.
Lemma regularCardinalMax_add_le : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (regularCardinalMax filter (fun A x => (w_ A x + v_ A x)%coq_nat) <= ((regularCardinalMax filter w_) + (regularCardinalMax filter v_))%coq_nat)%coq_nat.
Admitted.
Lemma regularCardinalMax_ge : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                   (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) A (x : func0 A),
      filter A x -> ( (v_ A x) <= (regularCardinalMax filter v_) )%coq_nat .
Admitted.
Lemma regularCardinalMax_transf : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
    forall (func'0 : obIndexer -> Type) (transf : forall (A : obIndexer), func'0 A -> func0 A),
      ( regularCardinalMax (fun A => filter A \o transf A) (fun A => v_ A \o transf A) <= regularCardinalMax filter v_ )%coq_nat .
Admitted.
(*
Definition regularCardinalMax_index : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    (forall (A : obIndexer), func0 A -> nat) -> {A : obIndexer & func0 A}.
Admitted.
Lemma regularCardinalMax_regularCardinalMax_index : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (v_ : forall (A : obIndexer), func0 A -> nat),
    v_ (projT1 (regularCardinalMax_index v_)) (projT2 (regularCardinalMax_index v_)) = regularCardinalMax v_ .
Admitted.
*)
  
Fixpoint grade (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0) {struct f} : nat
with gradeMaxCom (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0) {struct f} : nat
with gradeTotal (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0) {struct f} : nat.
Proof. (* non-really mutual at the end *)
  case : F1 F2 / f.
  - intros F.
    exact (S O). (* UnitTopos *)
  - intros F2 F1 f_ F1' f'.
    refine ((S  (S (grade _ _ f_ + grade _ _ f')%coq_nat)) (* +
            (S  (S (gradeMaxCom _ _ f_ + (gradeMaxCom _ _ f' (* + (S (S (grade _ _ f_ + grade _ _ f')%coq_nat)) *))%coq_nat)%coq_nat)) *))%coq_nat. (* PolyTopos *)
  - intros A A' a.
    exact (S (S O)). (* View1 *)
  - intros func0 func1 A x.
    exact (S (S O)). (* PolyMetaFunctor *)
  - intros func0 func1 func'0 func'1 transf A f.
    refine ((S (S (grade _ _ f))) (* + (gradeMaxCom _ _ f) *))%coq_nat. (* PolyMetaTransf *)
  - intros func0 func1 F f_.
    refine (S (S ((regularCardinalMax (fun A x => ~~ isSol.isSolbb (f_ A x)) (fun A x => (  grade _ _ (f_ A x) (* +  gradeMaxCom _ _ (f_ A x) *) )%coq_nat)) +
                  (regularCardinalMax (fun A x => isSol.isSolbb (f_ A x)) (fun A x => (  grade _ _ (f_ A x) (* +  gradeMaxCom _ _ (f_ A x) *) )%coq_nat)))%coq_nat )). (* CoLimitator *)
Proof.
  case : F1 F2 / f.
  - intros F.
    exact (O). (* UnitTopos *)
  - intros F2 F1 f_ F1' f'.
    refine (  ( (gradeMaxCom _ _ f_ + (gradeMaxCom _ _ f' + (S (S (grade _ _ f_ + grade _ _ f')%coq_nat)))%coq_nat)%coq_nat)). (* PolyTopos *)
  - intros A A' a.
    exact (O). (* View1 *)
  - intros func0 func1 A x.
    exact (O). (* PolyMetaFunctor *)
  - intros func0 func1 func'0 func'1 transf A f.
    refine (gradeMaxCom _ _ f). (* PolyMetaTransf *)
  - intros func0 func1 F f_.
    refine ( ( ((regularCardinalMax (fun A x => ~~ isSol.isSolbb (f_ A x)) (fun A x => ( (* grade _ _ (f_ A x) + *) gradeMaxCom _ _ (f_ A x))%coq_nat)) +
             (regularCardinalMax (fun A x => isSol.isSolbb (f_ A x)) (fun A x => ( (* grade _ _ (f_ A x) + *) gradeMaxCom _ _ (f_ A x))%coq_nat)))%coq_nat)). (* CoLimitator *)
Proof.
  case : F1 F2 / f.
  - intros F.
    exact ((S O))%coq_nat. (* UnitTopos *)
  - intros F2 F1 f_ F1' f'.
    refine ((S  (S (gradeTotal _ _ f_ + gradeTotal _ _ f')%coq_nat)) +
            (  ( ((*gradeMaxCom _ _ f_ +*) ((*gradeMaxCom _ _ f' + *) (S (S (grade _ _ f_ + grade _ _ f')%coq_nat)) )%coq_nat)%coq_nat)) )%coq_nat. (* PolyTopos *)
  - intros A A' a.
    exact (S (S O)). (* View1 *)
  - intros func0 func1 A x.
    exact (S (S O)). (* PolyMetaFunctor *)
  - intros func0 func1 func'0 func'1 transf A f.
    refine ((S (S (gradeTotal _ _ f)))  (* + (gradeMaxCom _ _ f)*) )%coq_nat. (* PolyMetaTransf *)
  - intros func0 func1 F f_.
    refine (S (S ((regularCardinalMax (fun A x => ~~ isSol.isSolbb (f_ A x)) (fun A x => (  gradeTotal _ _ (f_ A x) )%coq_nat)) +
                 (regularCardinalMax (fun A x => isSol.isSolbb (f_ A x)) (fun A x => (  gradeTotal _ _ (f_ A x) )%coq_nat)) )%coq_nat)). (* CoLimitator *)
Defined.

(*
  case : F1 F2 / f.
  - intros F.
    exact ((S O) +
           (O))%coq_nat. (* UnitTopos *)
  - intros F2 F1 f_ F1' f'.
    refine ((S  (S (grade _ _ f_ + grade _ _ f')%coq_nat)) +
            ( ( (gradeMaxCom _ _ f_ + (gradeMaxCom _ _ f' + (S (S (grade _ _ f_ + grade _ _ f')%coq_nat)))%coq_nat)%coq_nat)) )%coq_nat. (* PolyTopos *)
  - intros A A' a.
    exact ((S (S O)) +
           (O) )%coq_nat. (* View1 *)
  - intros func0 func1 A x.
    exact ((S (S O)) +
           (O))%coq_nat. (* PolyMetaFunctor *)
  - intros func0 func1 func'0 func'1 transf A f.
    refine ((S (S (grade _ _ f))) +
            (gradeMaxCom _ _ f))%coq_nat. (* PolyMetaTransf *)
  - intros func0 func1 F f_.
    refine (S (S (regularCardinalMax (fun A x => (*gradeTotal _ _ (f_ A x) *)  (grade _ _ (f_ A x) + gradeMaxCom _ _ (f_ A x))%coq_nat  )))). (* CoLimitator *) *)


(*
Definition grade :
  forall (F1 F2 : obTopos), 'Topos(0 F1 ~> F2 )0 -> nat.
Proof.
    move => F1 F2 f; elim : F1 F2 / f.
    - intros; exact (S O). (* UnitTopos *)
    - move => ? ? f_ grade_f_ ? f' grade_f';
               refine (S  (S (grade_f_ + grade_f')%coq_nat)). (* PolyTopos *)
    - intros; exact (S (S O)). (* View1 *)
    - intros; exact (S (S O)). (* PolyMetaFunctor *)
    - intros; refine (S (S _)); assumption. (* PolyMetaTransf *)
    - intros ? ? ? f_ grades_f_A_f.
      refine (S (S (regularCardinalMax grades_f_A_f))). (* CoLimitator *)
Defined.

Definition gradeMaxCom : 
  forall (F1 F2 : obTopos), 'Topos(0 F1 ~> F2 )0 -> nat.
Proof.
  move => F1 F2 f; elim : F1 F2 / f.
  - intros; exact (O). (* UnitTopos *)
  - move => ? ? f_ grade_f_ ? f' grade_f';
             refine ((grade_f_ + (grade_f' + grade (f_ o>Topos f'))%coq_nat)%coq_nat ). (* PolyTopos *)
  - intros; exact (O). (* View1 *)
  - intros; exact (O). (* PolyMetaFunctor *)
  - intros; assumption. (* PolyMetaTransf *)
  - intros ? ? ? v_ grades_v_A_x.
    refine (regularCardinalMax grades_v_A_x). (* CoLimitator *)
Defined.

Definition gradeTotal : 
  forall (F1 F2 : obTopos), 'Topos(0 F1 ~> F2 )0 -> nat.
Proof.
  move => F1 F2 f; elim : F1 F2 / f.
  - intros F; exact ((grade (@UnitTopos F) + (O))%coq_nat). (* UnitTopos *)
  - move => F2 F1 f_ grade_f_ F1' f' grade_f';
             refine (grade (f_ o>Topos f') + (S (grade_f_ + (grade_f' + grade (f_ o>Topos f'))%coq_nat)%coq_nat ))%coq_nat. (* PolyTopos *)
  - intros A A' a; exact (grade (View1 a) + (O))%coq_nat. (* View1 *)
  - intros func0 func1 A x; exact (grade (PolyMetaFunctor func1 x) + (O))%coq_nat. (* PolyMetaFunctor *)
  - intros func0 func1 func'0 func'1 transf A f gradeMaxCom_f;
      exact (grade (PolyMetaTransf func'1 transf f) + gradeMaxCom_f)%coq_nat. (* PolyMetaTransf *)
  - intros func0 func1 F v_ grades_v_A_x.
    refine (regularCardinalMax (fun A x => (grade (v_ A x) + grades_v_A_x A x)%coq_nat)). (* CoLimitator *)
Defined.
 *)

(*
Definition gradeTotal : forall (F1 F2 : obTopos), 'Topos(0 F1 ~> F2 )0 -> nat.
Proof.
  move => F1 F2 f; elim : F1 F2 / f. Show Proof.
  - intros F; refine (grade (@UnitTopos F) + (gradeMaxCom (@UnitTopos F)))%coq_nat. (* UnitTopos *)
  - intros F2 F1 f_ F1' f'. refine (grade (f_ o>Topos f') + (gradeMaxCom (f_ o>Topos f')))%coq_nat.
    
  - move => ? ? v_ grade_v_ ? f' grade_f';
             refine ((grade_v_ + (grade_f' + grade (v_ o>Topos f'))%coq_nat)%coq_nat ). (* PolyTopos *)
  - intros; exact (O). (* View1 *)
  - intros; exact (O). (* PolyMetaFunctor *)
  - intros; assumption. (* PolyMetaTransf *)
  - intros ? ? ? v_ grades_v_A_x.
    refine (regularCardinalMax grades_v_A_x). (* CoLimitator *)
  move => f; refine ( (grade f) + (gradeMaxCom f) )%coq_nat.
Defined. *)



(**TODO : make func'1 of PolyMetaTransf maximally implicit *)
Module Red.

  Import Sol.Ex_Notations.
  Reserved Notation "f2 <~~ f1" (at level 70).

  Inductive convTopos : forall (F1 F2 : obTopos),
      'Topos(0 F1 ~> F2 )0 -> 'Topos(0 F1 ~> F2 )0 -> Prop :=

  (* equivalence *)
        
  | Topos_Trans : forall (F1 F2 : obTopos) (uTrans f : 'Topos(0 F1 ~> F2 )0),
      uTrans <~~ f -> forall (f0 : 'Topos(0 F1 ~> F2 )0),
        f0 <~~ uTrans -> f0 <~~ f
                         
  (* congruences *)
                  
  | PolyTopos_cong_Pre :
      forall (F F' : obTopos) (f_ f_0 : 'Topos(0 F ~> F' )0),
      forall (F'' : obTopos) (f' : 'Topos(0 F' ~> F'' )0),
        f_0 <~~ f_ -> ( f_0 o>Topos f' ) <~~ ( f_ o>Topos f' )

  | PolyTopos_cong_Post :
      forall (F F' : obTopos) (f_ : 'Topos(0 F ~> F' )0),
      forall (F'' : obTopos) (f' f'0 : 'Topos(0 F' ~> F'' )0),
        f'0 <~~ f' -> ( f_ o>Topos f'0 ) <~~ ( f_ o>Topos f' )

  | PolyMetaTransf_cong :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
      forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      forall (A : obIndexer) (v v0 : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
        (* none lack to hold changes to transf because no such changes and uniform *)
        v0 <~~ v -> v0 o>Topos_transf <~~ ( v o>Topos_transf
                                        : 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0 )

  | CoLimitator_cong :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall F : obTopos,
      forall (v_ v_0 : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
        (* cocone func1 f_ ->    cocone erased *)
        (* (gradeTotal (v_0 (projT1 (regularCardinalMax_index (fun A x => gradeTotal (v_0 A x)))) (projT2 (regularCardinalMax_index (fun A x => gradeTotal (v_0 A x))))) < gradeTotal (v_ (projT1 (regularCardinalMax_index (fun A x => gradeTotal (v_ A x)))) (projT2 (regularCardinalMax_index (fun A x => gradeTotal (v_ A x))))) )%coq_nat -> *)
(*        (forall (A : obIndexer) (x : func0 A),
            v_0 A x <~~ v_ A x \/
            (v_0 A x = v_ A x /\
             exists fSol : 'Topos(0 (View0 A) ~> F )0 %sol, Sol.toTopos fSol = v_0 A x)) -> *)
        (forall (A : obIndexer) (x : func0 A), ~~ isSol.isSolbb (v_ A x) -> v_0 A x <~~ v_ A x) ->
        (forall (A : obIndexer) (x : func0 A), isSol.isSolbb (v_ A x) -> v_0 A x = v_ A x) ->
        (forall (A : obIndexer) (x : func0 A), isSol.isSolbb (v_0 A x)) ->
        forall (A : obIndexer) (x : func0 A), ~~ isSol.isSolbb (v_ A x) ->
        [[ v_0 @ func1 ]] <~~ ( [[ v_ @ func1 ]]
                              : 'Topos(0 MetaFunctor func1 ~> F )0 )

  (* units *)

  | Topos_unit :
      forall (F F' : obTopos) (f : 'Topos(0 F ~> F' )0),
        ( f )
          <~~ ( ( uTopos ) o>Topos f
              : 'Topos(0 F ~> F' )0 )

  | Topos_inputUnitTopos :
      forall (G F : obTopos) (g : 'Topos(0 G ~> F )0),
        ( g )
          <~~  ( g o>Topos ( uTopos )
               : 'Topos(0 G ~> F )0 )

  (* polymorphism *)

  | View_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A ~> A' )0)
                         (A'' : obIndexer) (a' : 'Indexer(0 A' ~> A'' )0),
      (View1 (a o>Indexer a'))
        <~~ ( (View1 a) o>Topos (View1 a')
            : 'Topos(0 View0 A ~> View0 A'' )0 )

  (* functoriality-polymorphism follows from this _cocone property and
associativity-polymorphism of PolyTopos and functoriality-polymorphism
of View1 *)
  | PolyMetaFunctor_cocone :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (A : obIndexer) (x : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
        ( PolyMetaFunctor func1 (func1 _ _ a x) )
          <~~ ( (View1 a) o>Topos (PolyMetaFunctor func1 x)
              : 'Topos(0 View0 A' ~> MetaFunctor func1 )0 )

  (* naturality-polymorphism is this, which is in operational form *)
  | PolyMetaTransf_poly :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
        (transf : forall A : obIndexer, func0 A -> func'0 A),
      forall (A : obIndexer) (v : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)
        (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
        ( ((View1 a) o>Topos v) o>Topos_transf )
          <~~ ( (View1 a) o>Topos (v o>Topos_transf)
              : 'Topos(0 View0 A' ~> MetaFunctor func'1 )0 )

  (* naturality-polymorphism of the bijection*)
  | CoLimitator_morphism :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (F : obTopos) (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (F' : obTopos) (f : 'Topos(0 F ~> F' )0),
        ( [[ (fun A x => (v_ A x) o>Topos f) @ func1 ]] )
          <~~ ( [[ v_ @ func1 ]] o>Topos f
              : 'Topos(0 MetaFunctor func1 ~> F' )0 )

  | PolyMetaFunctor_CoLimitator :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall F : obTopos,
      forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (A : obIndexer) (x : func0 A),
        ( v_ A x )
          <~~ ( (PolyMetaFunctor func1 x) o>Topos [[ v_ @ func1 ]]
              : 'Topos(0 View0 A ~> F )0 )

  | PolyMetaTransf_CoLimitator :
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
      forall F : obTopos,
      forall (v_ : forall (A : obIndexer), func'0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (transf : forall (A : obIndexer), func0 A -> func'0 A)
        (A : obIndexer) (w : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
        (w o>Topos [[ (fun A0 => (v_ A0) \o (transf A0)) @ func1 ]])
          <~~ (w o>Topos_transf) o>Topos [[ v_ @ func'1 ]]
(*
  (* for sense only, non-necessary for reduction *)
  | CoLimitator_PolyMetaFunctor :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        ( @UnitTopos (MetaFunctor func1) )
          <~~ ( [[ PolyMetaFunctor func1 ]]
              : 'Topos(0 (MetaFunctor func1) ~> (MetaFunctor func1) )0 ) *)
          
  where "f2 <~~ f1" := (@convTopos _ _ f2 f1).

  Module Export Ex_Notations.

    Notation "f2 <~~ f1" := (@convTopos _ _ f2 f1).
    Hint Constructors convTopos.

  End Ex_Notations.
  
  Lemma Red_convTopos_convTopos :
  forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
    fDeg <~~ f -> fDeg ~~~ f.
  Proof.
    move => F1 F2 f fDeg. elim; rewriterTopos; try eauto.
    intros.
    apply: Top.CoLimitator_cong. intros. 
  Admitted.

  Lemma degrade :
    forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
      fDeg <~~ f ->  ((grade fDeg) <= (grade f))%coq_nat
                  (* /\  ((gradeMaxCom fDeg) <= (gradeMaxCom f))%coq_nat*)
                 /\ ((gradeTotal fDeg) < (gradeTotal f))%coq_nat.
  Proof.
    move => F1 F2 fDeg f red_f; elim : F1 F2 fDeg f / red_f;
             try solve [ rewrite (* /gradeTotal *)  /= => * ;
                                                    abstract intuition Omega.omega ].
    - (* CoLimitator_cong *)
      move => func0 func1 F v_ v_0 red_v_ IH_red_v iden_v_ sol_v0 A x red_v_A_x.

      move: (IH_red_v _ _ red_v_A_x) => IH_red_v_A_x.

      move: (fun A x p => congr1 (@grade _ _) (iden_v_ A x p)).
      move => /(@regularCardinalMax_congr _ _ (fun A x => isSol.isSolbb (v_ A x)) (fun A x => grade (v_0 A x)) (fun A x => grade (v_ A x))).
      move: (fun A x p => congr1 (@gradeTotal _ _) (iden_v_ A x p)).
      move => /(@regularCardinalMax_congr _ _ (fun A x => isSol.isSolbb (v_ A x)) (fun A x => gradeTotal (v_0 A x)) (fun A x => gradeTotal (v_ A x))).

      move: (fun A x p => proj1 (IH_red_v A x p)).
      move => /(@regularCardinalMax_monotone_ge _ _ (fun A x => ~~ isSol.isSolbb (v_ A x)) (fun A x => grade (v_0 A x)) (fun A x => grade (v_ A x))).

      move: (fun A x p => proj2 (IH_red_v A x p)).
      move => /(@regularCardinalMax_monotone_gt _ _ (fun A x => ~~ isSol.isSolbb (v_ A x)) (fun A x => gradeTotal (v_0 A x)) (fun A x => gradeTotal (v_ A x))) /(_ _ _ red_v_A_x (proj2 IH_red_v_A_x)) .

      have Hlogical : forall (A : obIndexer) (x : func0 A), ~~ isSol.isSolbb (v_0 A x) <-> False .
      { move => A0 x0. move: (sol_v0 A0 x0) -> => //. }
      move : (Hlogical) => /(regularCardinalMax_falsefilter (fun A x => grade (v_0 A x))).
      move : Hlogical => /(regularCardinalMax_falsefilter (fun A x => gradeTotal (v_0 A x))).
      
      have Hlogical2 : forall (A : obIndexer) (x : func0 A), isSol.isSolbb (v_0 A x) <-> (~~ isSol.isSolbb (v_ A x) \/ isSol.isSolbb (v_ A x)) .
      { move => A0 x0. by case: ( isSol.isSolbb (v_ A0 x0)); intuition. }
      move : (Hlogical2) => /(regularCardinalMax_samefilter (fun A x => grade (v_0 A x))).
      move : Hlogical2 => /(regularCardinalMax_samefilter (fun A x => gradeTotal (v_0 A x))).

      move: (regularCardinalMax_unionfilter (fun A x => ~~ isSol.isSolbb (v_ A x))
                                            (fun A x => isSol.isSolbb (v_ A x))
               (fun A x => grade (v_0 A x)) ).
      move: (regularCardinalMax_unionfilter (fun A x => ~~ isSol.isSolbb (v_ A x))
                                            (fun A x => isSol.isSolbb (v_ A x))
                                            (fun A x => gradeTotal (v_0 A x)) ).

      simpl; abstract intuition Omega.omega.

    - (* CoLimitator_cong *)
      move => func0 func1 F v_ v_0 red_v_ IH_red_v iden_v_ A x red_v_A_x. move: (IH_red_v _ _ red_v_A_x) => IH_red_v_A_x.

      have Hlogical : forall (A : obIndexer) (x : func0 A), ~~ isSol.isSolbb (v_0 A x) ->  ~~ isSol.isSolbb (v_ A x).
      { move => A0 x0. apply: contra => J. by move : (J) => /iden_v_ -> . }
      move : (Hlogical) => /(regularCardinalMax_subfilter (fun A x => grade (v_0 A x))).
      move : Hlogical => /(regularCardinalMax_subfilter (fun A x => gradeTotal (v_0 A x))).

      move: (fun A x p => proj1 (IH_red_v A x p)).
      move => /(@regularCardinalMax_monotone_ge _ _ (fun A x => ~~ isSol.isSolbb (v_ A x)) (fun A x => grade (v_0 A x)) (fun A x => grade (v_ A x))).

      move: (fun A x p => proj2 (IH_red_v A x p)).
      move => /(@regularCardinalMax_monotone_gt _ _ (fun A x => ~~ isSol.isSolbb (v_ A x)) (fun A x => gradeTotal (v_0 A x)) (fun A x => gradeTotal (v_ A x))) /(_ _ _ red_v_A_x (proj2 IH_red_v_A_x)) .

      simpl; abstract intuition Omega.omega.


      (** WAIT  /!\ REDEFINE GRADES **)

      
    - (* CoLimitator_morphism *)
      move => func0 func1 F v_ F' f /= .
      rewrite !(regularCardinalMax_add_succ , regularCardinalMax_addl_const , regularCardinalMax_addr_const) /=.
      move: (regularCardinalMax_add_le (fun A x => ~~ isSol.isSolbb (v_ A x)) (fun (A : obIndexer) (x : func0 A) => (gradeTotal (v_ A x) + gradeTotal f)%coq_nat)
                          (fun (A : obIndexer) (x : func0 A) => (grade (v_ A x) + grade f)%coq_nat.+2) ).
      rewrite !(regularCardinalMax_add_succ , regularCardinalMax_addl_const , regularCardinalMax_addr_const) /=.
      simpl; abstract intuition Omega.omega.
    - (* PolyMetaFunctor_CoLimitator *)
      move => func0 func1 F v_ A x /=. 
      move: (regularCardinalMax_ge (fun (A0 : obIndexer) (x0 : func0 A0) => grade (v_ A0 x0)) x)
              (regularCardinalMax_ge (fun (A0 : obIndexer) (x0 : func0 A0) => gradeTotal (v_ A0 x0)) x).
      abstract intuition Omega.omega.
    - (* PolyMetaTransf_CoLimitator *)
      move => func'0 func'1 F v_ func0 func1 transf A w /=.  
      move: (regularCardinalMax_transf (fun A0 x => grade (v_ A0 x)) transf)
              (regularCardinalMax_transf (fun A0 x => gradeTotal (v_ A0 x)) transf).
      rewrite /funcomp => /= . abstract intuition Omega.omega.
Qed.

  Lemma degradeTotal :
    forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
      fDeg <~~ f ->  ((gradeTotal fDeg) < (gradeTotal f))%coq_nat.
  Proof.
    eapply degrade.
  Qed.

  Lemma degrade_gt0 :
    forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      ((S O) <= (grade f))%coq_nat.
  Proof.
    move=> F1 F2 f; apply/leP; case : f; simpl; auto. (* alt: Omega.omega. *)
  Qed.

  Lemma degradeTotal_gt0 :
    forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      ((S O) <= (gradeTotal f))%coq_nat.
  Proof.
    move=> F1 F2 f; case : f => /= * ; Omega.omega.
  Qed.

End Red.


Section Section1.

  Import Sol.Ex_Notations.
  Import Red.Ex_Notations.

  Fixpoint solveTopos len {struct len} :
    forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0)
      (H_gradeTotal : (gradeTotal f <= len)%coq_nat),
      { fSol : 'Topos(0 F1 ~> F2 )0 %sol
      | ( (Sol.toMod fSol) <~~ f ) \/ ( (Sol.toMod fSol) = f ) }.
  Proof.
    case : len => [ | len ].

    (* n is O *)
    - clear; ( move => F1 F2 f H_gradeTotal ); exfalso;
        move : (Red.degradeTotal_gt0 f) => H_degradeTotal_gt0; abstract Omega.omega.

    (* n is (S n) *)
    - move => F1 F2 f; case : F1 F2 / f =>
      [ F  (* @uTopos F *)
      | F1 F2 f_ F1' f' (* f_ o>Topos f' *)
      | A A' a (* View1 a *)
      | func0 func1 A x (* PolyMetaFunctor func1 x *)
      | func0 func1 func'0 func'1 transf A f (* f o>Topos_transf *)
      | func0 func1 F v_ ] (* [[ v_ @ func1 ]] *).

      (* f is @uTopos F *)
      + move => H_gradeTotal. exists (@uTopos F)%sol. right. reflexivity.

      (* f id f_ o>Topos f' *)
      + all: cycle 1. 
        
      (* f is View1 a *)
      + move => H_gradeTotal. exists (Sol.View1 a). right. reflexivity.
      
      (* f is PolyMetaFunctor func1 x *)
      + move => H_gradeTotal. exists (Sol.PolyMetaFunctor func1 x). right. reflexivity.

        Ltac rewriterTopos := repeat match goal with | [ HH : @eq (Topos00 _ _) _ _  |- _ ] =>  try rewrite -> HH in *; clear HH end. 
        
    Ltac tac_reduce :=
    simpl in *; abstract (
    intuition (eauto; try subst; rewriterTopos; try congruence;
                               eauto 12)).

      (* f is f o>Topos_transf *)
      + move => H_gradeTotal.
        case : (solveTopos len _ _ f) =>
        [ | fSol fSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega.
        * exists (fSol o>Topos_transf)%sol.
          clear -fSol_prop. tac_reduce.

      (* f is [[ v_ @ func1 ]] *)
      + move => H_gradeTotal.
        case : (solveTopos len _ _ v_) =>
        [ | fSol fSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega.
        * exists (fSol o>Topos_transf)%sol.
          clear -fSol_prop. tac_reduce.



          
  (**

-------------------------------------------------------

   **)


