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

Parameter obIndexer : Type.
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

(* add indexer type parameter T instead of obIndexer *)
Definition mymax : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    (forall (A : obIndexer), func0 A -> nat) -> nat.
Admitted.
Lemma mymax_monotone_ge : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, ( w_ A x <= v_ A x )%coq_nat) -> ( mymax w_ <= mymax v_ )%coq_nat.
Admitted.
Lemma mymax_monotone_gt : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, ( w_ A x < v_ A x )%coq_nat) -> ( mymax w_ < mymax v_ )%coq_nat.
Admitted.
Lemma mymax_addr_const : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      mymax (fun A x => (v_ A x + n)%coq_nat) = ((mymax v_) + n)%coq_nat.
Admitted.
Lemma mymax_addl_const : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      mymax (fun A x => (n + v_ A x)%coq_nat) = (n + (mymax v_))%coq_nat.
Admitted.
Lemma mymax_add_succ : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
      mymax (fun A x => S (v_ A x)%coq_nat) = (S (mymax v_))%coq_nat.
Admitted.
Lemma mymax_add_le : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (mymax (fun A x => (w_ A x + v_ A x)%coq_nat) <= ((mymax w_) + (mymax v_))%coq_nat)%coq_nat.
Admitted.
Lemma mymax_ge : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) A (x : func0 A),
      ( (v_ A x) <= (mymax v_) )%coq_nat .
Admitted.
Lemma mymax_transf : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
    forall (func'0 : obIndexer -> Type) (transf : forall (A : obIndexer), func'0 A -> func0 A),
      ( mymax (fun A => v_ A \o transf A) <= mymax v_ )%coq_nat .
Admitted.

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
    refine (S (S (mymax (fun A x => (  grade _ _ (f_ A x) (* +  gradeMaxCom _ _ (f_ A x) *) )%coq_nat)))). (* CoLimitator *)
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
    refine ( ( (mymax (fun A x => ( (* grade _ _ (f_ A x) + *) gradeMaxCom _ _ (f_ A x))%coq_nat)))). (* CoLimitator *)
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
    refine (S (S (mymax (fun A x => (  gradeTotal _ _ (f_ A x) )%coq_nat)))). (* CoLimitator *)
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
    refine (S (S (mymax (fun A x => (*gradeTotal _ _ (f_ A x) *)  (grade _ _ (f_ A x) + gradeMaxCom _ _ (f_ A x))%coq_nat  )))). (* CoLimitator *) *)


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
      refine (S (S (mymax grades_f_A_f))). (* CoLimitator *)
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
    refine (mymax grades_v_A_x). (* CoLimitator *)
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
    refine (mymax (fun A x => (grade (v_ A x) + grades_v_A_x A x)%coq_nat)). (* CoLimitator *)
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
    refine (mymax grades_v_A_x). (* CoLimitator *)
  move => f; refine ( (grade f) + (gradeMaxCom f) )%coq_nat.
Defined. *)


(**TODO : make func'1 of PolyMetaTransf maximally implicit *)
Module Red.
    
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
        ( forall (A : obIndexer) (x : func0 A), v_0 A x <~~ v_ A x ) 
        ->  [[ v_0 @ func1 ]] <~~ ( [[ v_ @ func1 ]]
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

  Hint Constructors convTopos.

  Lemma Red_convTopos_convTopos :
  forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
    fDeg <~~ f -> fDeg ~~~ f.
  Proof.
    move => F1 F2 f fDeg. elim; eauto.
  Qed.

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
      move => func0 func1 F v_ v_0 red_v_ IH.
      move: (fun A x => proj1 (IH A x)).
      move => /(@mymax_monotone_ge _ _ (fun A x => grade (v_0 A x)) (fun A x => grade (v_ A x))).
      move: (fun A x => proj2 (IH A x)).
      move => /(@mymax_monotone_gt _ _ (fun A x => gradeTotal (v_0 A x)) (fun A x => gradeTotal (v_ A x))).
      move => /= . abstract intuition Omega.omega.
    - (* CoLimitator_morphism *)
      move => func0 func1 F v_ F' f /= .
      rewrite !(mymax_add_succ , mymax_addl_const , mymax_addr_const) /=.
      move: (mymax_add_le (fun (A : obIndexer) (x : func0 A) => (gradeTotal (v_ A x) + gradeTotal f)%coq_nat)
                          (fun (A : obIndexer) (x : func0 A) => (grade (v_ A x) + grade f)%coq_nat.+2) ).
      rewrite !(mymax_add_succ , mymax_addl_const , mymax_addr_const) /=.
      abstract intuition Omega.omega.
    - (* PolyMetaFunctor_CoLimitator *)
      move => func0 func1 F v_ A x /=. 
      move: (mymax_ge (fun (A0 : obIndexer) (x0 : func0 A0) => grade (v_ A0 x0)) x)
              (mymax_ge (fun (A0 : obIndexer) (x0 : func0 A0) => gradeTotal (v_ A0 x0)) x).
      abstract intuition Omega.omega.
    - (* PolyMetaTransf_CoLimitator *)
      move => func'0 func'1 F v_ func0 func1 transf A w /=.  
      move: (mymax_transf (fun A0 x => grade (v_ A0 x)) transf)
              (mymax_transf (fun A0 x => gradeTotal (v_ A0 x)) transf).
      rewrite /funcomp => /= . abstract intuition Omega.omega.
Qed.
