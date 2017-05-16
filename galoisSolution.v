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
      (forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> (MetaFunctor func0 func1) )0)

| PolyMetaTransf :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      (forall (A : obIndexer), 'Topos(0 (View0 A) ~> (MetaFunctor func0 func1) )0
                          -> 'Topos(0 (View0 A) ~> (MetaFunctor func'0 func'1) )0)

| CoLimitator :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (f_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      (* cocone func1 f_ ->    cocone erased *)
      'Topos(0 (MetaFunctor func0 func1) ~> F )0

where "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2).

Notation "'uTopos'" := (@UnitTopos _)(at level 0).
Notation "@ 'uTopos' F" :=
  (@UnitTopos F) (at level 11, only parsing).

Notation "f_ o>Topos f'" :=
  (@PolyTopos _ _ f_ _ f') (at level 25, right associativity).

Notation "f o>Topos' transf" :=
  (@PolyMetaTransf _ _ _ _ transf _ f) (at level 25, right associativity).

Notation "[[ f_ @ func1 ]]" :=
  (@CoLimitator _ func1 _ f_ ) (at level 0).

Notation "[[ f_ ]]" :=
  (@CoLimitator _ _ _ f_ ) (at level 0).


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

(* | View_cong : forall (A A' : obIndexer) (a a': 'Indexer(0 A ~> A' )0),
    a ~~ a' -> View1 a ~~~ ( View1 a'
                            : 'Topos(0 View0 A ~> View0 A' )0 ) *)

| View_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A ~> A' )0)
                        (A'' : obIndexer) (a' : 'Indexer(0 A' ~> A'' )0),
    (View1 (a o>Indexer a'))
      ~~~ ( (View1 a) o>Topos (View1 a')
            : 'Topos(0 View0 A ~> View0 A'' )0 )

| View_unitIndexer : forall (A : obIndexer),
    ( @UnitTopos (View0 A) )
      ~~~ ( View1 (@unitIndexer A)
            : 'Topos(0 View0 A ~> View0 A )0 )

| CoLimitator_morphism :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos) (f_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (F' : obTopos) (transf : 'Topos(0 F ~> F' )0),
      let f_o_transf := (fun A f => (f_ A f) o>Topos transf) in
      ( [[ f_o_transf @ func1 ]] )
        ~~~ ( [[ f_ @ func1 ]] o>Topos transf
              : 'Topos(0 MetaFunctor func0 func1 ~> F' )0 )

(* functoriality follows from this and associativity and functoriality of View1 *)
| PolyMetaFunctor_cocone :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (A : obIndexer) (f : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( PolyMetaFunctor func0 func1 A' (func1 _ _ a f) )
        ~~~ ( (View1 a) o>Topos (PolyMetaFunctor func0 func1 A f)
              : 'Topos(0 View0 A' ~> MetaFunctor func0 func1 )0 )

(* naturality is this, which is in operational form *)
| PolyMetaTransf_poly :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
      (transf : forall A : obIndexer, func0 A -> func'0 A),
    forall (A : obIndexer) (f : 'Topos(0 (View0 A) ~> (MetaFunctor func0 func1) )0)
      (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( ((View1 a) o>Topos f) o>Topos' transf )
        ~~~ ( (View1 a) o>Topos (f o>Topos' transf)
              : 'Topos(0 View0 A' ~> MetaFunctor func'0 func'1 )0 )

(* no cuts for ?? | Transf_comp : ?? ?? | Transf_id : ?? 
| Transf_id :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A) (*lacked?*),
      let id_transf : (forall A : obIndexer, func0 A -> func0 A) := (fun A f => f) in
      forall (A : obIndexer) (f : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
        f ~~~ (Transf func1 id_transf f) *)
          
(* what alternative *)
(* | CoLimitator_Inject_Id :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A), (*lacked?*)
      let transf : (forall A : obIndexer, func0 A -> func0 A) := (fun A f => f) in
      (@ uTopos (MetaFunctor func1))
        ~~~ ([[Inject func1 func1 transf]]
            : 'Topos(0 MetaFunctor func1 ~> MetaFunctor func1 )0 ) *)

| PolyMetaFunctor_CoLimitator :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (f_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (A : obIndexer) (g : func0 A),
      ( f_ A g )
        ~~~ ( (PolyMetaFunctor func0 func1 A g) o>Topos [[ f_ @ func1 ]]
              : 'Topos(0 View0 A ~> F )0 )

| CoLimitator_PolyMetaFunctor :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      ( @UnitTopos (MetaFunctor func0 func1) )
      ~~~ ( [[ PolyMetaFunctor func0 func1 ]]
            : 'Topos(0 (MetaFunctor func0 func1) ~> (MetaFunctor func0 func1) )0 )
        
where "f2 ~~~ f1" := (@convTopos _ _ f2 f1).

Definition cocone_def := 
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos)
      (f_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (A : obIndexer) (f : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( f_ A' (func1 _ _ a f) )
        ~~~ ( (View1 a) o>Topos (f_ A f)
              : 'Topos(0 View0 A' ~> F )0 ) .

Notation cocone func1 f_ :=
  (forall (A : obIndexer) (f : _ A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( f_ A' (func1 _ _ a f) )
        ~~~ ( (View1 a) o>Topos (f_ A f)
              : 'Topos(0 View0 A' ~> _ )0 )) .

Check 
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos)
      (f_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      cocone func1 f_ ->
      'Topos(0 (MetaFunctor func0 func1) ~> F )0.

(* add indexer type parameter T instead of obIndexer *)
Parameter mymax : forall {func0 : obIndexer -> Type},
    (forall (A : obIndexer), func0 A -> nat) -> nat.
Axiom mymax_addr_const : forall (func0 : obIndexer -> Type),
    forall (f_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      mymax (fun A f => (f_ A f + n)%coq_nat) = ((mymax f_) + n)%coq_nat.
Axiom mymax_addl_const : forall (func0 : obIndexer -> Type),
    forall (f_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      mymax (fun A f => (n + f_ A f)%coq_nat) = (n + (mymax f_))%coq_nat.
Axiom mymax_add_le : forall {func0 : obIndexer -> Type},
    forall (g_ f_ : forall (A : obIndexer), func0 A -> nat),
      (mymax (fun A f => (g_ A f + f_ A f)%coq_nat) <= ((mymax g_) + (mymax f_))%coq_nat)%coq_nat.
Axiom mymax_ge : forall {func0 : obIndexer -> Type},
    forall (f_ : forall (A : obIndexer), func0 A -> nat) A (f : func0 A),
      ( (f_ A f) <= (mymax f_) )%coq_nat .

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
  - intros ? ? ? f_ grades_f_A_f.
    refine (mymax grades_f_A_f). (* CoLimitator *)
Defined.

Definition gradeTotal (F1 F2 : obTopos) :
  'Topos(0 F1 ~> F2 )0 -> nat.
Proof.
  move => f; refine ( (grade f) + (gradeMaxCom f) )%coq_nat.
Defined.

Lemma degrade :
  forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
    fDeg ~~~ f -> ((grade fDeg) <= (grade f))%coq_nat
                 /\ ((gradeTotal fDeg) < (gradeTotal f))%coq_nat.
Proof.
  move => F1 F2 fDeg f red_f; elim : F1 F2 fDeg f / red_f;
           try solve [ rewrite /gradeTotal /= => * ;
                                                abstract intuition Omega.omega ].
  - rewrite /gradeTotal /= => func0 func1 F f_ F' transf. (* CoLimitator_morphism *)
    move : (mymax_add_le (fun (A : obIndexer) (f : func0 A) => gradeMaxCom (f_ A f))
                         (fun (A : obIndexer) (f : func0 A) => (gradeMaxCom transf + (2 + (grade (f_ A f) + grade transf)%coq_nat)%coq_nat)%coq_nat)).
    rewrite !(mymax_addl_const , mymax_addr_const) /=.
    abstract intuition Omega.omega.
  - rewrite /gradeTotal /= => func0 func1 F f_ A g. (* PolyMetaFunctor_CoLimitator *)
    move: (mymax_ge (fun (A0 : obIndexer) (f : func0 A0) => grade (f_ A0 f)) A g)
            (mymax_ge (fun (A0 : obIndexer) (f : func0 A0) => gradeMaxCom (f_ A0 f)) A g).
    abstract intuition Omega.omega.
Qed.
