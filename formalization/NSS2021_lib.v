(***** 
This library was developed in the folllowing work. 

Raja Natarajan, Suneel Sarswat, Abhishek Kr Singh: Verified Double Sided Auctions for Financial Markets. ITP 2021: 28:1-28:18.

We have combined their library files into a single file with very minimal editing to ensure no conflicts appear. Furthermore, we have added a few Lemmas that are needed for our work.
*****)

(*########################## First Part of the library ###############################*)


(* -----------------Description------------------------------------------

This file contains useful results about reflection techniques in Coq. 
Some of the important concepts formalized are:

Definition Prop_bool_eq (P: Prop) (b: bool):= P <-> b=true.
Lemma reflect_intro (P:Prop)(b:bool): Prop_bool_eq P b -> reflect P b.

Lemma impP(p q:bool): reflect (p->q)((negb p) || q).
Lemma switch1(b:bool): b=false -> ~ b. 
Lemma switch2(b:bool): ~ b -> b=false.


Some useful Ltac defined terms:

 Ltac switch:=  (apply switch1||apply switch2).
 Ltac switch_in H:= (apply switch1 in H || apply switch2 in H).
 Ltac right_ := apply /orP; right.
 Ltac left_ := apply /orP; left.
 Ltac split_ := apply /andP; split.   

--------------------- ------------------- ------------------------------*)



From Coq Require Export ssreflect  ssrbool.

Require Export Lia.


Set Implicit Arguments.

Section GeneralReflections.
Definition Prop_bool_eq (P: Prop) (b: bool):= P <-> b=true.

(* Inductive reflect (P : Prop) : bool -> Set :=  
   ReflectT : P -> reflect P true | ReflectF : ~ P -> reflect P false *)
Lemma reflect_elim (P:Prop)(b: bool): reflect P b -> Prop_bool_eq P b.
Proof. { intro H.
       split. case H. auto. auto. case H. auto. intros. discriminate H0. } Qed. 

Lemma reflect_intro (P:Prop)(b:bool): Prop_bool_eq P b -> reflect P b.
Proof. { intros. destruct H as  [H1 H2].
         destruct b. constructor;auto.
         constructor.  intro H. apply H1 in H;inversion H. } Defined.

Lemma reflect_dec P: forall b:bool, reflect P b -> {P} + {~P}.
Proof. intros b H; destruct b; inversion H; auto.  Qed.
Lemma reflect_EM P: forall b:bool, reflect P b -> P \/ ~P.
Proof. intros b H. case H; tauto. Qed.
Lemma dec_EM P: {P}+{~P} -> P \/ ~P.
  Proof. intro H; destruct H as [Hl |Hr];tauto. Qed.
Lemma pbe_EM P: forall b:bool, Prop_bool_eq P b -> P \/ ~P.
Proof. { intros b H; cut( reflect P b).
         apply reflect_EM. apply reflect_intro;auto. } Qed.


(* iffP : forall (P Q : Prop) (b : bool), reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b *)

(* idP : forall b1 : bool, reflect b1 b1 *)

(* negP
     : reflect (~ ?b1) (~~ ?b1) *)

(* andP
     : reflect (?b1 /\ ?b2) (?b1 && ?b2) *)

(*orP
     : reflect (?b1 \/ ?b2) (?b1 || ?b2) *)
Lemma impP(p q:bool): reflect (p->q)((negb p) || q).
  Proof. { case p eqn:pH; case q eqn:qH; simpl.
       constructor. auto. 
       constructor. intro H2. cut (false=true). discriminate. apply H2. auto. 
       constructor. auto. 
       constructor. discriminate. } Qed. 
Lemma impP1(P Q:Prop)(p q:bool)(HP: reflect P p)(HQ: reflect Q q):  reflect (P->Q)((negb p) || q).
Proof. { case p eqn:pH; case q eqn:qH; simpl.
       constructor. move /HP. apply /HQ.
       constructor. intro H2. absurd (Q). move /HQ. discriminate. apply H2; apply /HP;auto.
       constructor. move /HP. discriminate.
       constructor. move /HP. discriminate. } Qed.
Lemma switch1(b:bool): b=false -> ~ b.
Proof. intros H H1.  rewrite H1 in H. discriminate H. Qed.
Lemma switch2(b:bool): ~ b -> b=false.
Proof. intros H. case b eqn:H1. absurd (true);auto. auto. Qed.

Lemma bool_fun_equal (B1 B2: bool): (B1-> B2)-> (B2-> B1)-> B1=B2.
    Proof. intros H1 H2. destruct B1; destruct B2; auto.
           replace false with true. auto. symmetry; auto. Qed.

    Hint Resolve bool_fun_equal: core.

End GeneralReflections.


Hint Immediate reflect_intro reflect_elim  reflect_EM reflect_dec dec_EM: core.
Hint Resolve idP impP impP1: core.
Hint Resolve bool_fun_equal: core.

Ltac solve_dec := eapply reflect_dec; eauto.
Ltac solve_EM  := eapply reflect_EM; eauto.

Ltac switch:=  (apply switch1||apply switch2).
Ltac switch_in H:= (apply switch1 in H || apply switch2 in H).

Ltac right_ := apply /orP; right.
Ltac left_ := apply /orP; left.
Ltac split_ := apply /andP; split.


Section NaturalNumbers.

Lemma ltP (x y:nat): reflect (x < y) (Nat.ltb x y).
Proof. { apply reflect_intro. split.
       { unfold "<".  unfold Nat.ltb. 
         revert y. induction x. intro y; case y. simpl.
         intro H. inversion H. simpl. auto.
         intro y;case y.
         intro H; inversion H. intros n H. 
         apply IHx. lia. }
       { 
         revert y. induction x. intro y; case y. simpl.
         intro H. inversion H. intros; lia.
         intro y;case y. simpl. intro H; inversion H.
         intro n. 
         intro H; apply IHx in H. lia. } } Qed.

Lemma leP (x y: nat): reflect (x <= y) (Nat.leb x y).
Proof. { apply reflect_intro. split.
       { revert y. induction x. intro y; case y; simpl; auto.
         intro y;case y.
         intro H; inversion H. intros n H. 
         apply IHx. lia.
        }
       { revert y. induction x. intro y; case y; intros; lia. 
         intro y;case y. simpl. intro H; inversion H.
         intro n.
         intro H; apply IHx in H. lia. } } Qed.

Lemma nat_reflexive: reflexive Nat.leb.
  Proof. unfold reflexive; induction x; simpl; auto. Qed.

Lemma nat_transitive: transitive Nat.leb.
Proof. unfold transitive. intros x y z h1 h2. move /leP in h1. move /leP in h2.
         apply /leP. lia. Qed.

Hint Resolve leP ltP nat_reflexive nat_transitive: core.

End NaturalNumbers.

Hint Resolve leP ltP nat_reflexive nat_transitive: core.


(*########################## Next Part of the library ###############################*)






(* -----------------Description --------------------------------------------------
   
   This file summarises some useful results from List Module of standard Library. 
   We create a hint database to remember important results regarding lists (core).

   Some new definitions:
   Definition Empty (s:list A):Prop := forall a : A, ~ In a s.
   Definition Equal (s s': list A) := forall a : A, In a s <-> In a s'.
   Definition Subset (s s': list A) := forall a : A, In a s -> In a s'.

   Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
   Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
   Notation "| s |":= (length s) (at level 70, no associativity).

  --------------------   ------------------  ------------------------------------- *)



From Coq Require Export ssreflect  ssrbool.
Require Export Lists.List Lia.


Set Implicit Arguments.

Hint Resolve in_eq in_cons in_inv in_nil in_dec: core.

Section BasicListFacts.
  Variable A:Type.
  Lemma in_inv1 : forall (a b:A) (l:list A), In b (a :: l) -> b = a \/ In b l.
  Proof. { intros  a b l H. cut (a=b \/ In b l). 
       2: {  auto. } intros H1; destruct H1 as [H1 | H2].
       left; symmetry; auto. right;auto. } Qed.
  Lemma in_inv2: forall (x a:A) (l:list A), In x (a::l)-> x <> a -> In x l.
  Proof.  { intros x a l H. cut (x=a \/ In x l). intro H1;destruct H1 as [Hl1|Hr1].
          intro;contradiction. auto. eapply in_inv1;auto. } Qed.
  Lemma in_inv3: forall (x a:A) (l:list A), In x (a::l)-> ~ In x l -> x = a.
    Proof.  { intros x a l H. cut (x=a \/ In x l). intro H1;destruct H1 as [Hl1|Hr1].
          intro;auto. intro;contradiction.  eapply in_inv1;auto. } Qed.
  Lemma in_inv4: forall (a x:A) (l:list A), ~In x (a::l)-> ~ In x l /\ x <> a.
    Proof.  { intros x a l H. unfold not in H. split. intro. simpl in H.
              destruct H. right.  auto. simpl in H.  assert (a =x \/a<>x ). eauto.
              destruct H0. destruct H. left;auto. auto. } Qed.
  Hint Resolve in_inv1 in_inv2 in_inv3 in_inv4: core.
  (*---------Some facts about NoDup on a list --------------------------------*)
  Lemma nodup_intro (a:A)(l: list A): ~ In a l -> NoDup l -> NoDup (a::l).
    Proof.  intros H1 H2; eapply NoDup_cons_iff;tauto.  Qed. 
  Lemma nodup_elim1 (a:A)(l: list A): NoDup (a::l)-> NoDup (l).
  Proof. intro H. eapply NoDup_cons_iff; eauto. Qed.
  Lemma nodup_elim2 (a:A)(l: list A): NoDup (a::l) -> ~ In a l.
    Proof. intro H. eapply NoDup_cons_iff; eauto. Qed. 
  
  Hint Immediate nodup_elim1  nodup_elim2  nodup_intro : core.
  End BasicListFacts.
Hint Resolve in_inv1 in_inv2 in_inv3 in_inv4: core.
Hint Immediate nodup_elim1  nodup_elim2  nodup_intro : core.



Section SetSpec.
  Variable A:Type.
  Definition Empty (s:list A):Prop := forall a : A, ~ In a s.
  
  Definition Subset (s s': list A) := forall a : A, In a s -> In a s'.
  Definition Equal (s s': list A):= Subset s s' /\ Subset s' s.
  
  (* Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop := 
     | Forall_nil : Forall P nil 
     | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l)  *)
  
  (* Inductive Exists (A : Type) (P : A -> Prop) : list A -> Prop :=
      |Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l) 
      | Exists_cons_tl : forall (x : A) (l : list A), Exists P l -> Exists P (x :: l) *)
  
  (* Inductive NoDup (A : Type) : list A -> Prop := 
      | NoDup_nil : NoDup nil 
      | NoDup_cons : forall (x : A) (l : list A), ~ In x l -> NoDup l -> NoDup (x :: l) *)
End SetSpec.

Ltac unfold_spec := try(unfold Equal);try(unfold Subset);try(unfold Empty).



  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Notation "| s |":= (length s) (at level 70, no associativity).
  

Section BasicSetFacts.
  Variable A:Type.

  (*-----------------------Subset (spec) and its properties ------------------------*)
  Lemma Subset_intro (a:A)(l s: list A): l [<=] s -> (a::l) [<=] (a::s).
  Proof. intros H x H1.  destruct H1. subst a;auto. auto. Qed.
  Lemma Subset_intro1 (a:A)(l s: list A): l [<=] s -> l [<=] (a::s).
    Proof. intros H x H1. simpl;right;auto. Qed. 
  Lemma Subset_elim1 (a:A) (s s':list A): Subset (a:: s) s'-> In a s'.
  Proof. { unfold Subset. intro H. apply H. auto. } Qed.
   Lemma Subset_elim2 (a:A) (s s':list A): Subset (a:: s) s'->  Subset s s'.
  Proof. { unfold Subset. intro H.  intros a1 H1.
           apply H. auto. } Qed.
  Lemma self_incl (l:list A): l [<=] l.
  Proof. unfold Subset; tauto.  Qed. 
  Hint Resolve self_incl: core.

  Lemma Subset_nil (l: list A): nil [<=] l.
  Proof. unfold "[<=]"; simpl; intros; contradiction. Qed.
  Lemma Subset_of_nil (l: list A): l [<=] nil -> l=nil.
    Proof. induction l. auto. intro H. absurd (In a nil); auto. Qed.

  Lemma Subset_trans (l1 l2 l3: list A): l1 [<=] l2 -> l2 [<=] l3 -> l1 [<=] l3.
  Proof. intros H H1 x Hx1. eauto. Qed. 
 Lemma Subset_elim (a1 a2: A)(l1 l2:list A):
           (a1::l1) [<=](a2::l2) -> ~In a2 l1 ->  l1 [<=] l2.
  Proof. { unfold "[<=]". intros. assert (In a (a1 :: l1));eauto.
  apply H in H2.  destruct H2. subst a. eauto. exact. } Qed.

    Lemma Subset_elim0 (a1 a2: A)(l1 l2:list A):
           (a1::l1) [<=](a2::l2) -> ~In a2 l1 ->  a1<>a2 ->
           (a1::l1) [<=] l2.
  Proof. { unfold "[<=]". intros. apply H in H2 as H2a.  destruct H2a. subst a.
   eauto. exact. } Qed.
  Lemma Subset_elim3 (a:A)(l1 l2: list A):
       l1 [<=](a::l2) -> ~In a l1 -> l1 [<=] l2.
  Proof. unfold "[<=]". intros.  apply H in H1 as H1a.
       destruct H1a. subst. eauto. auto. Qed.
  Lemma Subset_elim4 (a:A)(l1 l2: list A): In a l1 -> Subset l1 l2 -> In a l2.
  Proof. unfold "[<=]". intros. apply H0 in H as H1a. auto. Qed.
  
Hint Extern 0 (?x [<=] ?z)  =>
match goal with
| H: (x [<=] ?y) |- _ => apply (@Subset_trans  x y z)
| H: (?y [<=] z) |- _ => apply (@Subset_trans  x y z)                                   
end : core.
  
  (* ---------------------- Equal (spec) and their properties--------------------*)
  Lemma Eq_refl (s: list A):  s [=] s.
  Proof.  unfold Equal. split;auto using self_incl.  Qed. 
  Lemma Eq_sym (s s':list A): s [=] s' -> s' [=] s.
  Proof. unfold Equal.  tauto. Qed. 
  Lemma Eq_trans1 ( x y z : list A) : x [=] y -> y [=] z -> x [=] z.
  Proof. { unfold Equal.  intros H H1. destruct H as [H0 H]; destruct H1 as [H1a H1].
           split; auto.  } Qed.

 Hint Extern 0 (?x [=] ?z)  =>
match goal with
| H: (x [=] ?y) |- _ => apply (@Eq_trans1  x y z)
| H: (?y [=] z) |- _ => apply (@Eq_trans1  x y z)                                   
end : core.


  Lemma Equal_intro (s s': list A): s [<=] s' -> s' [<=] s -> s [=] s'.
  Proof. unfold "[=]".  tauto. Qed.
  Lemma Equal_intro1 (s s': list A): s = s' -> Equal s s'.
  Proof. intro; subst s; apply Eq_refl; auto. Qed.
  Lemma Equal_elim ( s s': list A): s [=] s' ->  s [<=] s' /\ s' [<=] s.
  Proof. unfold_spec; unfold iff. intros H; split; intro a;apply H. Qed.

  (* ---------------- introduction and elimination for filter operation---------- *)
  (* Check filter :  forall A : Type, (A -> bool) -> list A -> list A *)
  (* Check filter_In : forall (A : Type) (f : A -> bool) (x : A) (l : list A),
       In x (filter f l) <-> In x l /\ f x = true *)
  Lemma filter_elim1 (f: A->bool)(l: list A)(x: A): In x (filter f l)-> In x l.
  Proof. apply filter_In. Qed.
  Lemma filter_elim2 (f: A->bool)(l: list A)(x: A): In x (filter f l)-> (f x).
  Proof. apply filter_In. Qed.
  Lemma filter_intro (f: A->bool)(l: list A)(x: A): In x l -> (f x)-> In x (filter f l).
  Proof. intros; apply filter_In; split;auto. Qed.

  Hint Immediate filter_elim1 filter_elim2 filter_intro: core.


 (*--------Strong Induction, Well founded induction and set cardinality ----------*)

  
Theorem strong_induction: forall P : nat -> Prop,
                    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
                    forall n : nat, P n.
Proof. { intros P Strong_IH n.
         pose (Q:= fun (n: nat)=> forall k:nat, k<= n -> P k). 
         assert (H: Q n);unfold Q. 
         { induction n. 
           { intros k H;apply Strong_IH.
             intros k0 H1.  cut (k0 < 0). intro H2; inversion H2. lia.  } 
           { intros k H0.
             assert (H1: k < (S n) \/ k = (S n) ).  lia.
             elim H1. intro. apply IHn. lia. 
             intro H. subst k. apply Strong_IH. intros. apply IHn. lia. } }
         unfold Q in H. apply H. lia. }   Qed. 

Definition lt_set (l1 l2: list A):= |l1| < |l2|.

Lemma lt_set_is_well_founded: well_founded lt_set.
Proof. { unfold well_founded. intro a.
       remember (|a|) as n. revert Heqn. revert a.
       induction n using strong_induction.
       { intros a H1. apply Acc_intro.
         intros a0 H2. apply H with (k:= |a0|).
         subst n; apply H2. auto. } } Qed.



Lemma non_zero_size (a:A)(l: list A): In a l -> |l| > 0.
  Proof. { induction l.
         { simpl; tauto. }
         { intros. simpl. lia. } } Qed.
         
Lemma non_nil_size (l: list A): |l| > 0 -> l<>nil.
  Proof. { induction l.
         { simpl. intro H. lia. }
         { intros. intro. assert (H1: In a nil).
           rewrite <- H0. auto. destruct H1. } } Qed.
           
Lemma element_list (l: list A)(a b : A): a<>b -> In b (a::l) -> In b l.
Proof. intros H1 H2. simpl in H2. destruct H2. destruct H1;auto. exact. Qed. 

Hint Resolve non_zero_size: core.  
 
End BasicSetFacts.


   
Hint Extern 0 (?x [<=] ?z)  =>
match goal with
| H: (x [<=] ?y) |- _ => apply (@Subset_trans _ x y z)
| H: (?y [<=] z) |- _ => apply (@Subset_trans _ x y z)                                   
end : core.

Hint Extern 0 (?x [=] ?z)  =>
match goal with
| H: (x [=] ?y) |- _ => apply (@Eq_trans1 _ x y z)
| H: (?y [=] z) |- _ => apply (@Eq_trans1 _ x y z)                                   
end : core.


Hint Immediate Eq_refl Eq_sym Equal_elim Equal_intro Equal_intro1: core.
Hint Immediate  Subset_elim1 Subset_elim2 Subset_nil Subset_of_nil Subset_elim3: core.
Hint Resolve  self_incl: core.
Hint Resolve Subset_intro Subset_intro1: core.

Hint Immediate filter_elim1 filter_elim2 filter_intro: core.

Hint Resolve lt_set_is_well_founded: core.

Hint Resolve non_zero_size element_list: core. 


(*########################## Next Part of the library ###############################*)





(* ------ This file contains results about minimum and maximum value in a list of elements 
   of an arbitrary type (A: Type) with a boolean comparison operator (lr: A-> A-> bool).
   

  The results in this file are prooved under the following three assumptions
  on the comparison operator lr:

  Hypothesis lr_refl : reflexive lr.      (*  forall x : A, lr x x *)
  Hypothesis lr_trans: transitive lr.     (*  forall y x z : A, lr x y -> lr y z -> lr x z *) 
  Hypothesis lr_comparable: comparable lr.    (*  forall x y : A, lr x y=false -> lr y x   *)
  
  Functions defined are: 
  maxof a b   => returns maximum among a and b
  maxin l d   => returns the maximum value in the list l (returns d if l is nil) 
  minof a b   => returns minimum among a and b
  minin l d   => returns the minimum value in the list l (returns d if l is nil) 

 Furthermore, we also prove some results about the existence of min and maximum the list l
 with respect to the lr relation as well as min and max with property P.

 Lemma min_exists (l: list A):
                       l<>nil -> exists min, In min l /\ (forall x, In x l -> min <=r x).

 Lemma max_exists (l: list A): 
                       l<>nil -> exists max, In max l /\ (forall x, In x l -> x <=r max).

 Lemma min_withP_exists (l: list A)(P: A->bool): (exists a, In a l /\ P a) -> 
                (exists min, In min l /\ P min /\ (forall x, In x l -> P x -> min <=r x)).

 Lemma max_withP_exists (l: list A)(P: A->bool): (exists a, In a l /\ P a) -> 
                (exists max, In max l /\ P max /\ (forall x, In x l -> P x -> x <=r max)).
  
 ---------------------------------------------------------------------------------------- *)

(*
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Lia.
*)


Set Implicit Arguments.

Section Min_Max.

  Context {A: Type }.

  Variable lr: A->A-> bool.
  Notation " a <=r b":= (lr a b)(at level 70, no associativity).
  Definition comparable (lr: A->A-> bool) := forall x y, lr x y=false -> lr y x.
  
 (*-----------Partial functions on lists ( maxin and minin ) ---------------------------  *)

  
  Definition maxof (a b :A): A := match a <=r b with
                                  |true => b
                                  |false => a           
                                  end.


  (* reflexive: forall x : T, R x x *)
  
  Hypothesis lr_refl : reflexive lr.
  
  Hypothesis lr_trans: transitive lr.
  Hypothesis lr_comparable: comparable lr.
  
  
  Lemma maxof_spec1 (a b: A): a <=r maxof a b.
  Proof. unfold maxof. destruct (a <=r b) eqn:H; eauto using lr_refl. Qed. (* refl *)
  Lemma maxof_spec2 (a b: A): b <=r maxof a b. 
  Proof. unfold maxof. destruct (a <=r b) eqn:H; eauto. Qed. (* refl and comparable *)
  Lemma maxof_spec3 (a b c:A): c <=r a -> c <=r maxof a b.
  Proof.  unfold maxof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.
  Lemma maxof_spec4 (a b c:A): c <=r b -> c <=r maxof a b.
  Proof. unfold maxof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.
  Lemma maxof_spec5 (a b: A): a=maxof a b \/b=maxof a b.
  Proof. unfold maxof. destruct (a <=r b). right. auto. left. auto.
  Qed.

  Hint Resolve maxof_spec1 maxof_spec2 maxof_spec3 maxof_spec4 maxof_spec5: core.
  
   Fixpoint maxin (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => maxof a (maxin l' a)  
    end.

   Lemma maxin_elim (l: list A)(a d:A): maxin (a::l) d = maxin (a::l) a.
   Proof. simpl; auto. Qed.

   Lemma maxin_elim1 (a:A) (l:list A) (d:A) : In (maxin (a::l) d) (a::l).
   Proof.  { revert a. revert d. induction l.
            { simpl. intros; left.
              unfold maxof. replace (a <=r a) with true. auto. symmetry;apply lr_refl. }
            { intros d a0. replace (maxin (a0 :: a :: l) d) with (maxof a0 (maxin (a::l) a0)).
              unfold maxof.
              destruct (a0 <=r maxin (a :: l) a0) eqn:H; eauto.
              simpl;auto.  } } Qed.

Lemma maxin_elim2 (l:list A) (d:A) :l<>nil -> In (maxin l d) l.
   Proof. { revert d. induction l. intros. destruct H. auto. intros. eapply maxin_elim1. } Qed.
   
         

 Lemma maxin_spec (l:list A)(d:A)(a:A): In a l -> (a <=r (maxin l d)).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl. destruct H.
            { subst a; eauto. } apply maxof_spec4. apply IHl. exact H. } } Qed.     
 
  Lemma maxin_spec0 (l:list A)(d:A)(a:A): In (maxin l d) l -> ((maxin l d) <=r (maxin (a::l) d)).
   Proof. { generalize d. induction l.
          { intros d0 H. simpl in H.  inversion H. }
          { intros d0 H. simpl. destruct H. auto.
            apply maxin_spec with (a:=maxof a0 (maxin l a0))(l:=(a::a0::l))(d:=d0).
             simpl in H. auto. } } Qed.     
 
   Hint Resolve maxin_spec maxin_spec0 maxin_elim maxin_elim1: core.

    Definition minof (a b :A): A:= match a <=r b with
                                  |true => a
                                  |false => b
                                   end.
    
    Lemma minof_spec1 (a b: A): minof a b <=r a.
     Proof. unfold minof. destruct (a <=r b) eqn:H; eauto. Qed.
   
   Lemma minof_spec2 (a b: A): minof a b <=r b.
   Proof. unfold minof. destruct (a <=r b) eqn:H; eauto. Qed.

   Lemma minof_spec3 (a b c:A): a <=r c -> minof a b <=r c.
   Proof. unfold minof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.  
   Lemma minof_spec4 (a b c:A): b <=r c ->  minof a b <=r c.
   Proof. unfold minof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed. 
   Lemma minof_spec5 (a b: A): a=minof a b \/b=minof a b.
  Proof. unfold minof. destruct (a <=r b). left. auto. right. auto.
  Qed.

   Hint Resolve minof_spec1 minof_spec2 minof_spec3 minof_spec4 minof_spec5: core.

   Fixpoint minin (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => minof a (minin l' a)
    end.

   Lemma minin_elim (l: list A)(a d:A): minin (a::l) d = minin (a::l) a.
   Proof. simpl; auto. Qed.

   Lemma minin_elim1 (a:A) (l:list A) (d:A) : In (minin (a::l) d) (a::l).
   Proof.  { revert a. revert d. induction l.
            { simpl. intros; left.
              unfold minof. replace (a <=r a) with true. auto. symmetry;apply lr_refl. }
            { intros d a0. replace (minin (a0 :: a :: l) d) with (minof a0 (minin (a::l) a0)).
              unfold minof.
              destruct (a0 <=r minin (a :: l) a0) eqn:H; eauto.
              simpl;auto. } } Qed.
              
Lemma minin_elim2 (l:list A) (d:A) :l<>nil -> In (minin l d) l.
   Proof. { revert d. induction l. intros. destruct H. auto.
        { case l eqn: Hl. simpl. left. unfold minof. destruct (a <=r a). auto. auto.
        intros. rewrite <- Hl. rewrite <- Hl in IHl.
        assert (l<>nil). subst. assert (| a0::l0|>0). simpl. 
        lia. apply non_nil_size.  exact.  apply IHl with (d:=a) in H0.
        simpl. assert (a=minof a (minin l a) \/ (minin l a)=minof a (minin l a)).
        eapply minof_spec5. destruct H1. left. exact. right.
        rewrite <- H1. exact. } }Qed.
        
   Lemma minin_spec (l:list A)(d:A)(a:A): In a l -> ((minin l d) <=r a).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl. destruct H.
            { subst a; eauto. } apply minof_spec4. apply IHl. exact H. } } Qed.

     Lemma minin_spec0 (l:list A)(d:A)(a:A): In (minin l d) l -> ((minin (a::l) d) <=r (minin l d)).
   Proof. { generalize d. induction l.
          { intros d0 H. simpl in H.  inversion H. }
          { intros d0 H. simpl. destruct H. auto. 
            apply minin_spec with (a:=minof a0 (minin l a0))(l:=(a::a0::l))(d:=d0).
             simpl in H. auto. } } Qed.     
 
   Hint Resolve minin_spec minin_spec0 minin_elim minin_elim1: core.

   (*---------------- Existence of Minimum and Maximum in the non-empty list------------- *)

   Lemma min_exists (l: list A): l<>nil -> exists min, In min l /\ (forall x, In x l -> min <=r x).
   Proof. intro H. case l eqn:H1. destruct H;auto.
          exists (minin (a::l0) a). split. auto. intro x. auto. Qed.
          
   Lemma max_exists (l: list A): l<>nil -> exists max, In max l /\ (forall x, In x l -> x <=r max).
   Proof.  intro H. case l eqn:H1. destruct H;auto.
           exists (maxin (a::l0) a). split. auto. intro x. auto. Qed.
   Lemma min_withP_exists (l: list A)(P: A->bool):
     (exists a, In a l /\ P a) -> (exists min, In min l /\ P min /\ (forall x, In x l -> P x -> min <=r x)).
   Proof. { intro H.
          assert (Hl: l <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            subst l. inversion H.  }
          set (lP:= filter P l).
          assert (HlP: lP <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            absurd (In a lP). rewrite H1. auto.  unfold lP. auto. }
          destruct (lP) eqn: HP. destruct HlP;auto.
          exists (minin (a::l0) a). split. 
          { cut  (In (minin (a :: l0) a) lP). unfold lP;eauto.
            rewrite HP. auto. } split.
          { rewrite <- HP. cut (In (minin lP a) (lP)).
            eauto. rewrite HP. auto. }
          { intros x H1 H2. assert (H3: In x (filter P l) ). auto.
            rewrite <-HP. unfold lP. auto. } } Qed.
   Lemma max_withP_exists (l: list A)(P: A->bool):
     (exists a, In a l /\ P a) -> (exists max, In max l /\ P max /\ (forall x, In x l -> P x -> x <=r max)).
   Proof. { intro H.
          assert (Hl: l <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            subst l. inversion H.  }
          set (lP:= filter P l).
          assert (HlP: lP <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            absurd (In a lP). rewrite H1. auto.  unfold lP. auto. }
          destruct (lP) eqn: HP. destruct HlP;auto.
          exists (maxin (a::l0) a). split. 
          { cut  (In (maxin (a :: l0) a) lP). unfold lP;eauto.
            rewrite HP. auto. } split.
          { rewrite <- HP. cut (In (maxin lP a) (lP)).
            eauto. rewrite HP. auto. }
          { intros x H1 H2. assert (H3: In x (filter P l) ). auto.
            rewrite <-HP. unfold lP. auto. } } Qed.
          
End Min_Max.


Hint Resolve maxof_spec1 maxof_spec2 maxof_spec3 maxof_spec4: core.
Hint Resolve maxin_spec maxin_elim maxin_elim1: core.
Hint Resolve minof_spec1 minof_spec2 minof_spec3 minof_spec4: core.
Hint Resolve minin_spec minin_elim minin_elim1: core.

Hint Immediate min_exists max_exists min_withP_exists max_withP_exists: core.



Section Nat_numbers.

 Lemma nat_comparable: comparable Nat.leb.
  Proof. unfold comparable. intros x y h1. move /leP in h1. apply /leP. lia. Qed.
  
End Nat_numbers.

Hint Resolve nat_comparable: core.


(*########################## Next Part of the library ###############################*)







(* ------   In this file we formalize the concept of sorting in a list.  We consider lists
   of elements (on an arbitrary type A) with a boolean comparison operator (lr: A-> A-> bool).
   Most of  the results in this file assumes only   
   1. reflexive, 
   2. transitive and 
   3. comparable 
   nature of the boolean operator lr. 
   Only the last result (equality of head) assumes the antisymmetric
   property of lr. 

   Following are the concepts formalized in this file: 

   Sorted l      <==> l is sorted w.r.t comp operator lr 
   putin a l      ==> puts the element a into a sorted list at its correct position w.r.t lr
   sort l         ==> sorts the list l w.r.t the comp operator lr 

   Some of the useful results in this file are:

   Lemma putin_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall (a:A) (l: list A), Sorted l -> Sorted (putin a l).

   Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).

   Lemma sort_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall(l: list A), Sorted (sort l).

   Lemma sort_equal (l: list A): Equal l (sort l).

   Lemma nodup_sort (l: list A): NoDup l -> NoDup (sort l). ------------------  *)


(*
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Lia.
*)

Set Implicit Arguments.

Section Sorting.
  Context {A: Type }.

  Variable lr: A->A-> bool.
  Notation " a <=r b":= (lr a b)(at level 70, no associativity).
  (* ------------- sorting a list of elements by lr relation ------------------------------*)

  Inductive  Sorted : list A-> Prop:=
  | nil_Sorted: Sorted nil
  | cons_Sorted (a:A)(l: list A): Sorted l -> (forall x, (In x l -> (a <=r x))) -> Sorted (a::l).

  Lemma Sorted_intro (a:A)(b:A)(l: list A)(Htrans: transitive lr):
    a <=r b -> Sorted (b::l)-> Sorted (a::b::l).
  Proof. { intros H H0. constructor. auto. intros x H1. destruct H1. subst x. auto.
         eapply Htrans with (y:=b). eauto. inversion H0. eauto. } Qed.


  Lemma Sorted_elim1 (a:A) (b:A) (l: list A): (Sorted (a::b::l)) -> (a <=r b).
  Proof. intro H. inversion H.  eapply H3. auto.  Qed.
  Lemma Sorted_elim4 (a:A) (l:list A): Sorted (a::l) ->(forall x, In x l -> a <=r x).
  Proof. intro H. inversion H. auto. Qed.
  Lemma Sorted_elim2 (a:A) (l:list A)(Hrefl: reflexive lr):
    Sorted (a::l) ->(forall x, In x (a::l) -> a <=r x).
  Proof. intro H. inversion H. intros. destruct H4. subst x.  eauto. eauto. Qed.
  Lemma Sorted_elim3 (a:A) (l:list A): (Sorted (a::l)) -> Sorted l.
  Proof. intro H. inversion H;auto. Qed.
  Lemma Sorted_subset (a1 a2:A) (l1 l2: list A) (Htrans: transitive lr)(Hrefl: reflexive lr):
  Sorted (a1::l1) -> Sorted (a2::l2) -> (a1::l1) [<=] (a2::l2) -> In a2 (a1::l1)
  -> (a1 <=r a2)/\a2 <=r a1.
  Proof. intros. eapply Sorted_elim2 with (a:=a1)(x:=a2) in H. assert (In a1 (a2::l2)).
  apply H1. auto. eapply Sorted_elim2 with (a:=a2)(x:=a1) in H3. auto. auto. auto.
  auto. auto. Qed.

  Lemma Sorted_single : forall a:A, (Sorted (a::nil)).
  Proof. constructor. constructor. intros;simpl;contradiction. Qed.
  
  Lemma last_in_Sorted (a d:A)(l:list A)(Htrans: transitive lr)(Hrefl: reflexive lr): 
   Sorted l -> In a l -> lr a (last l d).
  Proof. { revert a. 
         induction l as [|b1 l']. 
         { intros a H H0. simpl in H0. auto. }
         { intros a0 H H0. 
           destruct H0.
           { subst b1.
           case l' as [|b2 l''] eqn: H1.
           { simpl. auto. }
           { replace (last (a0 :: b2 :: l'') d) with (last (b2 :: l'') d). 
             assert (H2: b2 <=r (last (b2 :: l'') d)). 
             { apply IHl'. eapply Sorted_elim3. exact H. auto. }
             assert (H3: a0 <=r b2). 
             { eapply Sorted_elim1. exact H. }
             eauto. 
             simpl. destruct l'';auto. } }
            { case l' as [|b2 l''] eqn: H1.
             { destruct H0. }
             { replace (last (b1 :: b2 :: l'') d) with (last (b2 :: l'') d). 
             apply IHl'. eapply Sorted_elim3. exact H. auto. 
             simpl. destruct l'';auto. } } } } Qed.


  Hint Resolve Sorted_elim1 Sorted_elim2 Sorted_elim3 Sorted_elim4
       Sorted_single Sorted_intro last_in_Sorted : core.

     
  Fixpoint putin (a: A) (l: list A) : list A:=
    match l with
    |nil=> a::nil
    |b::l1 => match a <=r b with
             |true => a::l
             |false => b::(putin a l1)
                    end
    end.

  Lemma putin_intro (a:A) (l: list A): forall x, In x l -> In x (putin a l).
  Proof. { intros x H. induction l. simpl in H. contradiction. simpl.
           destruct ( a <=r a0). destruct H. subst x. all: auto.  destruct H. subst x; auto.
          apply IHl in H as H1;auto.  } Qed.
         
  Lemma putin_intro1 (a:A) (l: list A): In a (putin a l).
  Proof. { induction l. simpl. tauto. simpl. destruct ( a <=r a0). all: auto.  } Qed.

  Lemma putin_elim (a:A) (l: list A): forall x, In x (putin a l) -> (x=a)\/(In x l).
  Proof. { intros x H. induction l. simpl in H. simpl. destruct H. left. auto. auto.
           simpl in H. destruct ( a <=r a0).   destruct H. auto. auto. destruct H.
           right;subst x;auto. apply IHl in H as H2. destruct H2. auto. right. auto.  } Qed.
   
(*  Definition comparable (lr: A->A-> bool) := forall x y, lr x y =false-> lr y x.*)

Definition comparable2 (lr: A->A-> bool) := forall x y, lr x y =true \/ lr y x = true.
  Lemma putin_correct (H_trans: transitive lr)(H_comp: comparable2 lr):
    forall (a:A) (l: list A), Sorted l -> Sorted (putin a l).
  Proof. { intros a l. revert a.  induction l.
         { intros a1 H.  simpl. apply Sorted_single. }
           simpl. intros a1 H.  destruct ( a1 <=r a) eqn:H0.
         {  auto.  }
         { unfold comparable2 in H_comp. specialize (H_comp a1 a). 
           destruct H_comp. { rewrite H1 in H0. inversion H0. } { constructor. eauto. 
           intros x H2. apply putin_elim in H2 as H3. destruct H3.
           subst x;auto. eauto. } } } Qed.
  
  Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).
  Proof.  { revert a. induction l.
          { simpl. auto. }
          { intros a0 H. assert (Ha: NoDup (a::l)).  eauto. 
            simpl. destruct (a0 <=r a) eqn: H1. auto.
            constructor.
            { intro H2. assert ( H2a: a=a0 \/ In a l). eauto using putin_elim.
              destruct H2a. subst a. inversion H. eauto.  inversion Ha; contradiction. }
            apply IHl. inversion H. constructor; eauto.  } } Qed.

  Lemma putin_card (a:A)(l: list A): | putin a l | = S (|l|).
  Proof. { induction l.
         { simpl;auto. }
         { simpl. case (a <=r a0) eqn:H.
           simpl; auto. simpl; rewrite IHl; auto. } } Qed.
  
  
  Hint Resolve putin_intro putin_intro1 putin_elim putin_correct nodup_putin: core.


   Fixpoint sort (l: list A): list A:=
    match l with
    |nil => nil
    |a::l1 => putin a (sort l1)
    end.
  
  
  Lemma sort_intro (l: list A): forall x, In x l -> In x (sort l).
  Proof. { intros x H. induction l. eauto. simpl. destruct H. subst x.
         apply putin_intro1. eauto using putin_intro. } Qed.

  Lemma sort_elim (l: list A): forall x, In x (sort l) -> In x l.
  Proof. { intros x H. induction l. simpl in H. contradiction.
         simpl in H. apply putin_elim in H. destruct H. subst x;eauto. eauto. } Qed.

  Lemma sort_correct (H_trans: transitive lr)(H_comp: comparable2 lr):
    forall(l: list A), Sorted (sort l).
  Proof. induction l. simpl. constructor. simpl. eauto using putin_correct. Qed.

  Hint Resolve sort_elim sort_intro sort_correct: core.
  
  Lemma sort_equal (l: list A): Equal l (sort l).
  Proof. split;intro; eauto. Qed.

   Lemma sort_equal1 (l: list A): Equal (sort l) l.
  Proof. split;intro; eauto. Qed.

  Lemma sort_same_size (l: list A): |sort l| = |l|.
  Proof. { induction l.
         { simpl;auto. }
         { simpl. replace (|putin a (sort l)|) with (S(|sort l|)).
           rewrite IHl. auto. symmetry. apply putin_card. } } Qed.

  Lemma Sorted_equal (l l': list A): Equal l l' -> Equal l (sort l').
  Proof. intro. cut (Equal l' (sort l')). eauto.  apply sort_equal. Qed.
  Lemma Sorted_equal1(l l': list A): Equal l l' -> Equal (sort l) l'.
  Proof. intro. cut (Equal l (sort l)). eauto. apply sort_equal. Qed.

  Lemma nodup_sort (l: list A): NoDup l -> NoDup (sort l).
  Proof. { induction l. eauto.
         {  simpl. intro H.  cut (NoDup (a::sort l)). eauto.
            constructor.
            { intro H1. absurd (In a l). inversion H; auto. eapply  sort_equal;auto. }
            eauto. } } Qed.

  (*--upto this point only reflexive, transitive and comparable property of <=r is needed--- *)

 
  (* ---------------------head in Sorted lists l and l'-------------------------- *)

   Definition empty: list A:= nil.
  
  Lemma empty_equal_nil_l (l: list A): l [=] empty -> l = empty.
  Proof. { case l. auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.


  
   (*-------- antisymmetric requirement is only needed in the following lemma--------*)
  Lemma head_equal_l (a b: A)(l s: list A)(Href: reflexive lr)(Hanti: antisymmetric lr):
    Sorted (a::l)-> Sorted (b::s)-> Equal (a::l) (b::s)-> a=b.
  Proof. { intros H H1 H2. 
         assert(H3: In b (a::l)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H3A: a <=r b). eapply Sorted_elim2;eauto.
         assert(H4: In a (b::s)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H4A: b <=r a). eapply Sorted_elim2;eauto.
         eapply Hanti. split_;auto. } Qed.  
  Lemma sort_equal_nodup (l: list A)(Href: reflexive lr)(Hanti: antisymmetric lr):
    Sorted l-> NoDup l-> sort l = l.
  Proof. { induction l. auto. intros. simpl. rewrite IHl.
           eauto. eauto. case l eqn:Hl. simpl. auto. intros. simpl.
           destruct (a <=r a0) eqn:Ha. f_equal.
           apply Sorted_elim2 with (x:=a0) in H.
           assert(a=a0). apply Hanti. apply /andP.
           split. auto. rewrite H in Ha.
           auto. subst. assert(~In a0 ((a0 :: l0))).
           eauto. assert(In a0 (a0 :: l0)). auto.
           unfold not in H1. apply H1 in H2. 
           elim H2. apply Href. auto. } Qed. 
           

End Sorting. 


Hint Resolve Sorted_elim1 Sorted_elim2 Sorted_elim3 Sorted_elim4
     Sorted_single Sorted_intro last_in_Sorted : core.
Hint Resolve putin_intro putin_intro1 putin_elim putin_correct nodup_putin : core.
Hint Resolve sort_elim sort_intro sort_correct sort_same_size : core.
Hint Resolve sort_equal sort_equal1 Sorted_equal Sorted_equal1 nodup_sort: core.
Hint Resolve empty_equal_nil_l head_equal_l: core.
Hint Immediate sort_equal_nodup: core.




(*
 Definition l := 12::42::12::11::20::0::3::30::20::0::nil.
 Eval compute in (sort (fun x y => Nat.ltb y x) l).
 Eval compute in (sort (fun x y => ~~ (Nat.ltb x y)) l).
*)
 



(*########################## Next Part of the library ###############################*)





(* -------------------------Description--------------------------------------

   In this file we capture the notion of ordType. This type has
   elements with decidable equality. This is almost same and inspired by
   ssreflect library.  
   We also connect natural numbers and booleans to this type by creating
   canonical instances nat_eqType and bool_eqType. 
 

   Structure type: Type:=  Pack {
                             E: Type;
                             eqb: E-> E -> bool;
                             eqP: forall x y, reflect (eq x y)(eqb x y) }.

 
  Notation "x == y":= (@Decidable.eqb _ x y)(at level 70, no associativity).

 

  Some important results are:
  
  Lemma eqP  (T:ordType)(x y:T): reflect (x=y)(eqb  x y). 
  Lemma nat_eqP (x y:nat): reflect (x=y)(Nat.eqb x y).

  Canonical nat_eqType: eqType:=
                              {| Decidable.E:= nat; Decidable.eqb:= Nat.eqb;
                                  Decidable.eqP:= nat_eqP |}.

  Lemma bool_eqP (x y:bool): reflect (x=y)(Bool.eqb x y). 
  
  Canonical bool_eqType: eqType:= 
                             {| Decidable.E:= bool; Decidable.eqb:= Bool.eqb;
                                  Decidable.eqP:= bool_eqP |}.

  
   ------------------------------------------------------------------------- *)
(*
From Coq Require Export ssreflect  ssrbool. 
Require Export  GenReflect Lia.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Decidable.
  Structure type: Type:= Pack {
                             E: Type;
                             eqb: E-> E -> bool;
                             eqP: forall x y, reflect (eq x y)(eqb x y) }.
  Module Exports.
    Coercion E : type >-> Sortclass.
    Notation eqType:= type.
    End Exports.
End Decidable.
Export Decidable.Exports.

Notation "x == y":= (@Decidable.eqb _ x y)(at level 70, no associativity): bool_scope.



Lemma eqP  (T:eqType)(x y:T): reflect (x=y)(x == y). 
Proof. apply Decidable.eqP. Qed.


Hint Resolve eqP: core.

Lemma eq_to_eqb (T:eqType)(x y:T): (x=y)-> (x == y).
Proof.  intro; apply /eqP; auto. Qed.
Lemma eqb_to_eq (T:eqType) (x y:T): (x == y)-> (x=y).
Proof. intro;apply /eqP; auto. Qed.

Hint Immediate eq_to_eqb eqb_to_eq: core.

Lemma eq_refl (T: eqType)(x:T): x == x.
Proof. apply /eqP; auto. Qed.
Lemma eq_symm (T: eqType)(x y:T): (x == y)=(y == x).
Proof. { case (x== y) eqn:H1; case ( y== x) eqn:H2;  try(auto).
       { assert (H3: x=y). apply /eqP;auto.
         rewrite H3 in H2; rewrite eq_refl in H2; inversion H2. }
       { assert (H3: y= x). apply /eqP; auto.
         rewrite H3 in H1; rewrite eq_refl in H1; inversion H1.  } } Qed.

Hint Resolve eq_refl eq_symm: core.

(*--------- Natural numbers as an instance of eqType---------------------*)

Lemma nat_eqb_ref (x:nat): Nat.eqb x x = true.
Proof. induction x;simpl;auto. Qed.
Hint Resolve nat_eqb_ref:core.

Lemma nat_eqb_elim (x y:nat):  Nat.eqb x y -> x = y.
Proof. { revert y. induction x.
       { intro y. case y. tauto. simpl; intros n H; inversion H. }
       intro y. case y. simpl; intro H; inversion H. simpl. eauto. } Qed.
Hint Resolve nat_eqb_elim: core.

Lemma nat_eqb_intro (x y:nat): x=y -> Nat.eqb x y.
Proof. intro H. subst x. eauto. Qed.
Hint Resolve nat_eqb_intro: core.

Lemma nat_eqP (x y:nat): reflect (x=y)(Nat.eqb x y).
Proof. apply reflect_intro.  split; eauto. Defined. 
Hint Resolve nat_eqP: core.


Canonical nat_eqType: eqType:= {| Decidable.E:= nat; Decidable.eqb:= Nat.eqb;
                                  Decidable.eqP:= nat_eqP |}.

(*--------- Bool as an instance of eqType --------------------------------*)
Lemma bool_eqb_ref (x:bool): Bool.eqb x x = true.
Proof. destruct x; simpl; auto. Qed.
Hint Resolve bool_eqb_ref: core.

Lemma bool_eqb_elim (x y:bool): (Bool.eqb x y) -> x = y.
Proof. destruct x; destruct y; simpl; try (auto || tauto). Qed.

Lemma bool_eqb_intro (x y:bool): x = y -> (Bool.eqb x y).
Proof. intros; subst y; destruct x; simpl; auto. Qed.

Hint Immediate bool_eqb_elim bool_eqb_intro: core.

Lemma bool_eqP (x y:bool): reflect (x=y)(Bool.eqb x y).
Proof. apply reflect_intro.
       split. apply bool_eqb_intro. apply bool_eqb_elim. Qed.
Hint Resolve bool_eqP: core.

Canonical bool_eqType: eqType:= {| Decidable.E:= bool; Decidable.eqb:= Bool.eqb;
                                  Decidable.eqP:= bool_eqP |}.


Ltac conflict_eq :=
    match goal with
    | H:  (?x == ?x)= false  |- _
      => switch_in H; cut(False);[tauto |auto]
    | H: ~(is_true (?x == ?x)) |- _
      => cut(False);[tauto |auto]             
    | H: ~ (?x = ?x) |- _
      => cut(False);tauto
    | H: (?x == ?y) = true, H1: ?x <> ?y |- _
      => absurd (x = y);auto
    | H:  is_true (?x == ?y), H1: ?x <> ?y |- _
      => absurd (x = y);auto                     
    | H: (?x == ?y) = true, H1: ?y <> ?x |- _
      => absurd (y = x);[auto | (symmetry;auto)]
    | H: is_true (?x == ?y), H1: ?y <> ?x |- _
      => absurd (y = x);[auto | (symmetry;auto)]                     
    | H: (?x == ?y) = false, H1: ?x = ?y |- _
      => switch_in H; absurd (x=y); auto
    | H: (?x == ?y) = false, H1: ?y = ?x |- _
      => switch_in H; symmetry in H1; absurd (x=y); auto
    end.




(*########################## Next Part of the library ###############################*)






(* This file contains boolean functions corresponding to the different predicates
   commonly used in reasoning about sets. These boolean functions are connected to
   the corresponding predicates using the reflection lemmas (similar to ssreflect).
   The type of elements in the set (or lists) are from eqType.


  Following are the boolean functions and their corresponding predicated  
 
  Propositions                        Boolean functions      Connecting Lemma 
  In a l                       <->    memb a l                membP
  IN a b l                     <->    memb2 a b l             memb2p
  NoDup l                      <->    noDup l                nodupP
  Empty l                      <->    is_empty l             emptyP
  Subset s s'                  <->    subset s s'            subsetP
  Equal s s'                   <->    equal s s'             equalP
  Exists P l                   <->    existsb f l            ExistsP
  exists x, (In x l /\ P x)    <->    existsb f l            existsP
  exists x, (In x l /\ f x)    <->    existsb f l            existsbP
  Forall P l                   <->    forallb f l            ForallP
  forall x, (In x l -> P x)    <->    forallb f l            forallP
  forall x, (In x l -> f x)    <->    forallb f l            forallbP 

  We also define index function (idx a l), which returns the location of an element
  a in the list l. 

  forall_em_exists f: (forall x, In x l -> f x) \/ (exists x, In x l /\ ~ f x).  
  exists_em_forall f: (exists x, In x l /\ f x) \/ (forall x, In x l -> ~ f x).

  Definition forall_xyb g l := forallb (fun x => (forallb ( fun y=> g x y) l)) l.
  Definition forall_yxb g l := forallb (fun y => (forallb ( fun x=> g x y) l)) l.

  forall_xyP g l: reflect (forall x y, In x l-> In y l-> g x y) (forall_xyb g l).
  forall_yxP g l: reflect (forall x y, In x l-> In y l-> g x y) (forall_yxb g l).

   ------------*)


(*
From Coq Require Export ssreflect  ssrbool Lists.List.
Require Export SetSpecs GenReflect DecType.
*)

Set Implicit Arguments.


Section SetReflections.
Context { A:eqType }. (* to declare A as implicit for all functions in this section *)
Lemma decA: forall x y:A, {x=y}+{x<>y}.
Proof. eauto. Qed.

  (*--------- set_mem (boolean function)  and its specification ---------*)
  Fixpoint memb (a:A)(l: list A){struct l}: bool:=
    match l with
    | nil =>false
    | a1::l1 => (a== a1) ||  memb a l1
    end.
  
  (* fix In (a : A) (l : list A) {struct l} : Prop :=
  match l with
  | nil => False
  | b :: m => b = a \/ In a m
  end *)

  Lemma set_memb_correct1: forall (a:A)(l:list A), memb a l -> In a l.
  Proof. { intros a l. induction l.
         { simpl;auto. }
         { simpl.  move /orP. intro H; destruct H.
           move /eqP in H;symmetry in H; left;auto.
           right; auto.  } } Qed.
  Lemma set_memb_correct2: forall (a:A)(l:list A), In a l ->  memb a l.
  Proof. { intros a l. induction l.
         { simpl;auto. }
         { simpl.  intro H. apply /orP. destruct H.
           left; apply /eqP; symmetry; auto. 
           right; auto.  } } Qed. 
  
  Lemma membP a l: reflect (In a l) (memb  a l).
  Proof. apply reflect_intro. split.
         apply set_memb_correct2. apply set_memb_correct1. Qed.
  
  Hint Resolve membP : core.
  Hint Immediate set_memb_correct1 set_memb_correct2: core.

  Lemma memb_prop1 (a:A)(l s: list A): l [<=] s -> In a l -> memb a l = memb a s.
  Proof. intros H H1. assert (H2: In a s); auto. Qed.
  Lemma memb_prop2 (a:A)(l s: list A): l [<=] s -> ~ In a s -> memb a l = memb a s.
  Proof. intros H H1. assert (H2: ~ In a l); auto. Qed.
  Lemma memb_prop3 (a:A)(l s: list A): l [=] s -> memb a l = memb a s.
  Proof. { intro h. destruct h as [h1 h2]. cut (In a l \/ ~ In a l).
         intro h3.  destruct h3 as [h3 | h3].
         apply memb_prop1;auto. apply memb_prop2;auto.
         eapply reflect_EM;auto. } Qed.

  Hint Resolve memb_prop1 memb_prop2 memb_prop3: core.
  

Lemma In_EM: forall (a:A) (x: list A), In a x \/ ~ In a x.
Proof. eauto.  Qed.

Definition IN := fun (x:A)(y:A)(l:list A) => In x l /\ In y l.
Definition memb2 x y l := memb  x l && memb y l.

Lemma memb2P a b x : reflect (IN a b x) (memb2 a b x).
Proof. { apply reflect_intro. split.
       { unfold IN; unfold memb2. intro H; destruct H.
         apply /andP. split; apply /membP; auto. }
       { unfold IN; unfold memb2. move /andP.
         intro H; split; apply /membP; tauto. } } Qed.

Lemma memb2_comute (x y: A)(l: list A): memb2 x y l = memb2 y x l.
Proof. unfold memb2. case (memb  x l);case (memb y l); simpl;auto. Qed.

Hint Resolve memb2P: core.
Lemma IN_EM: forall (a b:A)(x:list A), IN a b x \/ ~ IN a b x.
Proof.  eauto. Qed.

Lemma memb_prop4 (x y: A)(l s: list A): l [=] s -> memb2 x y l = memb2 x y s.
Proof. intro h. assert (h1: s [=] l). auto. unfold memb2.
       replace (memb x s) with (memb x l). replace (memb y s) with (memb y l).
       auto. all: auto. Qed.
Lemma memb2_elim (x y: A)(l: list A): memb2 x y l = false -> (~ In x l \/ ~ In y l).
Proof. { intro h7. unfold memb2 in h7.
       destruct (memb x l) eqn:h7x; destruct (memb y l) eqn:h7y; simpl in h7;
           move /membP in h7x; move /membP in h7y.
       inversion h7. right;auto. all: left;auto. } Qed.



(*---------- noDup  (boolean function) and its specification ---------*)
Fixpoint noDup (x: list A): bool:=
  match x with
    |nil => true
    |h :: x1 => if memb h x1 then false else noDup x1
  end.
Lemma NoDup_iff_noDup l: NoDup l <-> noDup l. 
Proof. { split. 
       { induction l.  auto.
       intro H; inversion H;  simpl.
       replace (memb a l) with false; auto. } 
       { induction l. constructor.
       simpl. case (memb a l) eqn: H1. discriminate.  intro H2.
       constructor. move /membP.  rewrite H1.  auto. tauto. }  } Qed.
Lemma noDup_intro l: NoDup l -> noDup l.
Proof. apply NoDup_iff_noDup. Qed.
Lemma noDup_elim l: noDup l -> NoDup l.
Proof. apply NoDup_iff_noDup. Qed.

Hint Immediate noDup_elim noDup_intro: core.

Lemma nodupP l: reflect (NoDup l) (noDup l).
Proof. {cut (NoDup l <-> noDup l). eauto. apply NoDup_iff_noDup. } Qed.

Hint Resolve nodupP : core.

Lemma NoDup_EM: forall l:list A, NoDup l \/ ~ NoDup l.
Proof. eauto. Qed.
Lemma NoDup_dec: forall l:list A, {NoDup l} + { ~ NoDup l}.
Proof. eauto. Qed.

Lemma nodup_spec: forall l:list A, NoDup (nodup decA l).
Proof. intros. eapply NoDup_nodup. Qed.



Fixpoint uniq (x: list A):(list A):=
  match x with
    |nil => nil
    |h :: x1 => if memb h x1 then uniq x1 else (h::(uniq x1))
  end.

Lemma uniq_intro_elim (l: list A)(a:A): In a l <-> In a (uniq l).
Proof. { split. { intros. induction l. { inversion H. } { destruct H. { subst. simpl.
                destruct (memb a l) eqn: Ha. eauto. auto. } { apply IHl in H as H2. simpl.   
                destruct (memb a0 l) eqn: Ha. auto. simpl. right. auto. } } }
              { intros. induction l. { simpl in H. inversion H. } { simpl in H.  destruct (memb a0 l) eqn: Ha.
                eauto. simpl in H. destruct H. subst. auto. eauto. } }  } Qed. 

Lemma uniq_noDup (l: list A): noDup (uniq l).
Proof. { induction l. { simpl. auto. } simpl.
          destruct (memb a l) eqn: H1. 
          { apply IHl. }
          { simpl. assert((In a (uniq l))\/(~In a (uniq l))) as Hl.
            { eauto. }
            { destruct Hl.
              { apply uniq_intro_elim in H. move /membP in H. rewrite H1 in H. inversion H. }
              { destruct (memb a (uniq l)) eqn: Hau. move /membP in Hau. eauto. auto. }}}} Qed. 
 
Lemma uniq_NoDup (l: list A): NoDup (uniq l).
Proof. apply NoDup_iff_noDup. apply uniq_noDup. Qed.

Hint Immediate uniq_intro_elim: core.
Hint Resolve uniq_noDup uniq_NoDup : core.

(*---------- is_empty (boolean function) and its specification -----------------*)
Definition is_empty (x:list A) : bool := match x with
                                 | nil => true
                                 | _ => false
                                      end.


Lemma emptyP l : reflect (Empty l) (is_empty l).
Proof. { destruct l eqn:H. simpl.  constructor. unfold Empty; auto.
       simpl. constructor. unfold Empty.  intro H1. specialize (H1 e).
       apply H1. auto.  } Qed. 
Hint Resolve emptyP : core.
Lemma Empty_EM (l:list A): Empty l \/ ~ Empty l.
  Proof. solve_EM. Qed.  
Lemma Empty_dec (l: list A): {Empty l} + {~Empty l}.
Proof. solve_dec. Qed.
Lemma empty_intro l : Empty l -> is_empty l.
Proof. move /emptyP. auto. Qed.
Lemma empty_elim l: is_empty l -> Empty l.
Proof. move /emptyP. auto. Qed.

Hint Immediate empty_elim empty_intro: core.

(*----------- subset (boolean function) and its specification--------------------*)
Fixpoint subset (s s': list A): bool:=
  match s with
  |nil => true
  | a1 :: s1=> memb a1 s' && subset s1 s'
  end.

Lemma subsetP s s': reflect (Subset s s') (subset s s').
Proof. { induction s. simpl. constructor. intro. intros  H. absurd (In a nil); auto.
       apply reflect_intro. split.
       { intro H.  cut (In a s' /\ Subset s s'). 2:{ split; eauto. } simpl.
         intro H1; destruct H1 as [H1 H2].
         apply /andP. split. apply /membP;auto. apply /IHs;auto.  }
       { simpl.  move /andP. intro H; destruct H as [H1 H2]. unfold Subset.
         intros a0 H3. cut (a0= a \/ In a0 s). intro H4; destruct H4 as [H4 | H5].
         rewrite H4. apply /membP;auto. cut (Subset s s'). intro H6. auto. apply /IHs;auto.
         eauto.   }  } Qed.

Hint Resolve subsetP: core.
Lemma Subset_EM (s s': list A): Subset s s' \/ ~ Subset s s'.
Proof. solve_EM. Qed.
Lemma Subset_dec (s s': list A): {Subset s s'} + {~ Subset s s'}.
Proof. solve_dec. Qed.

Lemma subset_intro s s': Subset s s' -> subset s s'.
Proof. move /subsetP. auto. Qed.
Lemma subset_elim s s': subset s s' -> Subset s s'.
Proof. move /subsetP. auto. Qed.

Hint Immediate subset_intro subset_elim: core.

(*----------- equal (boolean function) and its specifications--------------------*)
Definition equal (s s':list A): bool:= subset s s' && subset s' s.
Lemma equalP s s': reflect (Equal s s') (equal s s').
Proof. { apply reflect_intro.  split.
       { intro H. cut (Subset s s'/\ Subset s' s).
       2:{ auto. } intro H1. unfold equal.
       apply /andP. split; apply /subsetP; tauto. }
       { unfold equal. move /andP. intro H. apply Equal_intro; apply /subsetP; tauto. }
       } Qed.

Hint Resolve equalP: core.
Lemma Equal_EM (s s': list A): Equal s s' \/ ~ Equal s s'.
Proof. solve_EM. Qed.
Lemma Equal_dec (s s': list A): {Equal s s'} + {~ Equal s s'}.
Proof. solve_dec. Qed.

Lemma equal_intro s s': Equal s s' -> equal s s'.
Proof. move /equalP. auto. Qed.
Lemma equal_elim s s': equal s s' -> Equal s s'.
Proof. move /equalP. auto. Qed.

Hint Immediate equal_elim equal_intro: core.


(*----------- existsb (boolean function) and its specifications-------------------*)
  
  (* fix existsb (l : list A) : bool :=
  match l with
  | nil => false
  | a :: l0 => f a || existsb l0
  end *)
  
  (* Inductive Exists (A : Type) (P : A -> Prop) : list A -> Prop :=
    Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l)
  | Exists_cons_tl : forall (x : A) (l : list A), Exists P l -> Exists P (x :: l) *)

  Lemma ExistsP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (Exists P l) (existsb f l).
  Proof.  { intro H. eapply reflect_intro.
         induction l. simpl. constructor; intro H1; inversion H1.
         split.
         { intro H1.  inversion H1. simpl. apply /orP; left; apply /H;auto.
           simpl. apply /orP; right; apply /IHl; auto. }
         { simpl. move /orP. intro H1; destruct H1 as [H1| H2]. constructor. apply /H; auto.
           eapply Exists_cons_tl. apply /IHl; auto.  } } Qed.
  
  Hint Resolve ExistsP: core.      
  
  (* Exists_dec
     : forall (A : Type) (P : A -> Prop) (l : list A),
       (forall x : A, {P x} + {~ P x}) -> {Exists P l} + {~ Exists P l} *)
  
   Lemma Exists_EM P l:(forall x:A, P x \/ ~ P x )-> Exists P l \/ ~ Exists P l.
  Proof. { intros H. induction l. right. intro H1.  inversion H1.
         cut( P a \/ ~ P a).  intro Ha. cut (Exists P l \/ ~ Exists P l). intro Hl.
         { destruct Ha as [Ha1 | Ha2]; destruct Hl as [Hl1 | Hl2].
           left. constructor;auto. left; constructor;auto.
           left.  apply Exists_cons_tl;auto.
           right. intro H1. inversion H1. all:contradiction. }
         all: auto.  } Qed.
  
  
  (* Exists_exists
     : forall (A : Type) (P : A -> Prop) (l : list A),
       Exists P l <-> (exists x : A, In x l /\ P x) *)
  
  Lemma existsP P f l: (forall x:A, reflect (P x)(f x))-> reflect (exists x, In x l /\ P x)(existsb f l).
  Proof. { intro H. eapply iffP with (P:= Exists P l). eapply ExistsP. apply H.
           all: apply Exists_exists. } Qed.
  Hint Resolve existsP: core.
  Lemma existsbP (f:A->bool) l: reflect (exists x, In x l /\ f x)(existsb f l).
  Proof. apply existsP. intros. apply idP. Qed.
  
  Lemma exists_dec P l:
    (forall x:A, {P x} + {~ P x})-> { (exists x, In x l /\ P x) } + { ~ exists x, In x l /\ P x}.
  Proof. { intros. cut({Exists P l}+{ ~ Exists P l}). intro H;destruct H as [Hl |Hr].
         left. apply Exists_exists;auto.
         right;intro H1; apply Hr; apply Exists_exists;auto.
         eapply Exists_dec;auto.  } Qed.
  
  Lemma exists_EM P l:
     (forall x:A, P x \/ ~ P x) ->  (exists x, In x l /\ P x) \/  ~ (exists x, In x l /\ P x) .
  Proof. { intro H. cut(Exists P l \/ ~ Exists P l).
         intro H1; destruct H1 as [H1l| H1r]. left. eapply Exists_exists;auto.
         right; intro H2;apply H1r; apply Exists_exists;auto. eapply Exists_EM;auto. } Qed. 
  
    
(*----------- forallb ( boolean function) and its specifications----------------- *)
 
 (* fix forallb (l : list A) : bool :=
    match l with
     | nil => true
     | a :: l0 => f a && forallb l0
    end *)
 
 (* Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
    Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l) *)

 Lemma ForallP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (Forall P l) (forallb f l).
 Proof.   { intro H. eapply reflect_intro.
         induction l. simpl. constructor; intro H1; inversion H1; auto.
         split.
         { intro H1.  inversion H1. simpl. apply /andP. split.  apply /H;auto.
           apply /IHl; auto. }
         { simpl. move /andP. intro H1; destruct H1 as [H1 H2]. constructor. apply /H; auto.
           apply /IHl; auto. } } Qed.
 
 Hint Resolve ForallP: core.
 Lemma Forall_EM P l:(forall x:A, P x \/ ~ P x ) -> Forall P l \/ ~ Forall P l.
 Proof.  { intros H. induction l. left. constructor. 
         cut( P a \/ ~ P a).  intro Ha. cut (Forall P l \/ ~ Forall P l). intro Hl.
         { destruct Ha as [Ha1 | Ha2]; destruct Hl as [Hl1 | Hl2].
           left. constructor;auto.
           right; intro H1;apply Hl2; inversion H1;auto.
           right; intro H1; apply Ha2; inversion H1; auto.
           right. intro H1. apply Ha2. inversion H1;auto.  }
         all: auto.  } Qed.
 Lemma forallP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (forall x, In x l -> P x) (forallb f l).
 Proof. { intro H. eapply iffP with (P:= Forall P l). eapply ForallP. apply H.
          all: apply Forall_forall. } Qed.

 Lemma forallbP (f: A->bool) (l: list A): reflect (forall x:A, In x l -> (f x)) (forallb f l).
 Proof. apply forallP. intros. apply idP. Qed.
 
 Lemma forall_dec P  l:
   (forall x:A, {P x} + { ~ P x}) -> { (forall x, In x l -> P x) } + { ~ forall x, In x l -> P x}.
 Proof. { intros. cut({Forall P l} + {~ Forall P l}).
          intro H;destruct H as [Hl |Hr].
          left. apply Forall_forall;auto.
          right;intro H1; apply Hr; apply Forall_forall;auto.
          eapply Forall_dec; auto.  } Qed.
 Lemma forall_EM P l:
   (forall x:A, P x \/ ~ P x )->  (forall x, In x l -> P x)  \/  ~ (forall x, In x l -> P x).
 Proof. { intros H. cut(Forall P l \/ ~ Forall P l).
          intro H1; destruct H1 as [H1l| H1r]. left. eapply Forall_forall;auto.
          right; intro H2;apply H1r; apply Forall_forall;auto. eapply Forall_EM;auto. } Qed. 
 
 Lemma forall_exists_EM P l:
   (forall x:A, P x \/ ~ P x) -> (forall x, In x l -> P x) \/ (exists x, In x l /\ ~ P x).
 Proof. { intros. cut(Forall P l \/ ~ Forall P l).  
        2:{ eapply Forall_EM. auto. }
        intro H1; destruct H1 as [Hl | Hr].
        left. apply Forall_forall. auto. right.
        cut(Exists (fun x : A => ~ P x) l). eapply Exists_exists.
        apply Exists_Forall_neg. all:auto. } Qed. 
 Lemma exists_forall_EM P l:
   (forall x:A, P x \/ ~ P x)-> (exists x, In x l /\ P x) \/ (forall x, In x l ->  ~ P x).
   Proof.  { intros. cut(Exists P l \/ ~ Exists P l).  
        2:{ eapply Exists_EM. auto. }
        intro H1; destruct H1 as [Hl | Hr].
        left. apply Exists_exists. auto. right.
        cut(Forall (fun x : A => ~ P x) l). eapply Forall_forall.
        apply Forall_Exists_neg. all:auto. } Qed.
   Lemma forall_em_exists (f: A-> bool) (l: list A): (forall x, In x l -> f x) \/ (exists x, In x l /\ ~ f x).
   Proof. apply forall_exists_EM; intro x;destruct (f x); auto. Qed.
   Lemma exists_em_forall (f: A-> bool) (l: list A): (exists x, In x l /\ f x) \/ (forall x, In x l ->  ~ f x).
   Proof. apply exists_forall_EM; intro x; destruct (f x); auto. Qed.
     
End SetReflections.



Hint Resolve membP memb2P nodupP emptyP subsetP equalP
     existsP existsbP ExistsP ForallP forallP forallbP memb2_comute: core.
Hint Resolve forall_exists_EM exists_forall_EM: core.
Hint Resolve forall_em_exists exists_em_forall: core.

Hint Immediate set_memb_correct1 set_memb_correct2  memb2_elim: core.
Hint Resolve memb_prop1 memb_prop2 memb_prop3 memb_prop4: core.
Hint Immediate noDup_elim noDup_intro: core.
Hint Immediate uniq_intro_elim: core.
Hint Resolve uniq_noDup uniq_NoDup : core.
Hint Immediate empty_elim empty_intro: core.
Hint Immediate subset_intro subset_elim: core.
Hint Immediate equal_elim equal_intro: core.




Section MoreReflection.
  Context { A:eqType }.

  Definition forall_xyb (g:A->A->bool)(l:list A):=  (forallb (fun x=> (forallb (fun y => g x y) l )) l).
  Definition forall_yxb (g:A->A->bool)(l:list A) :=  (forallb (fun y=> (forallb (fun x => g x y) l )) l).
  
  Lemma forall_xyP (g:A->A->bool) (l:list A):
    reflect (forall x y, In x l-> In y l-> g x y)  (forall_xyb g l).
  Proof. eapply iffP with (P:= (forall x, In x l -> (forall y, In y l -> g x y))).
         unfold forall_xyb; auto. all: auto. Qed.
  Lemma forall_yxP (g:A->A->bool) (l:list A):
    reflect (forall x y, In x l-> In y l-> g x y)  (forall_yxb g l).
  Proof. eapply iffP with (P:= (forall y, In y l -> (forall x, In x l -> g x y))).
         unfold forall_yxb; auto. all: auto. Qed.
  
End MoreReflection.

Hint Resolve forall_xyP forall_yxP: core.




(*########################## Next Part of the library ###############################*)






(*-------------- Description -----------------------------------------------------

 
 Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).


 Lemma list_del_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (del_all a l).
 Lemma list_del_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).   *)

(*
Require Export Lists.List.
Require Export GenReflect SetSpecs DecType.
Require Export SetReflect.
*)

Set Implicit Arguments.




Section DecLists.


  Context { A: eqType }.

(*  Definition empty: list A:= nil.*)
  
  Lemma empty_equal_nil (l: list A): l [=] empty -> l = empty.
  Proof. { case l.  auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.



 (* -------------- list_insert operation and its properties---------------------------  *)
  Fixpoint insert (a:A)(l: list A): list A :=
    match l with
    |nil => a::nil
    |a1::l1 => match a == a1 with
              |true => a1::l1
              |false => a1:: (insert a l1)
              end
    end.
  (* this function adds an element correctly even in an unsorted list *)
  Lemma insert_intro1 (a b: A)(l: list A): In a l -> In a ( insert b l).
  Proof. { intro H. induction l.  inversion H.
         destruct H.
         { subst a0. simpl.  destruct (b == a). all: auto. }
         { simpl. destruct (b == a0). all:auto. } } Qed.
  
  Lemma insert_intro2 (a b: A)(l: list A): a=b -> In a (insert b l).
  Proof. { intro. subst a. induction l.
         simpl. left;auto. simpl. destruct (b == a) eqn:H. move /eqP in H.
         subst b; auto. all: auto. } Qed.
  Lemma insert_intro (a b: A)(l: list A): (a=b \/ In a l) -> In a (insert b l).
  Proof. intro H. destruct H.  eapply insert_intro2;auto.  eapply insert_intro1;auto. Qed.
  Lemma insert_intro3 (a:A)(l: list A): In a (insert a l).
  Proof. { eapply insert_intro2. auto.  } Qed.
  Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: core.
  
  Lemma insert_not_empty (a: A)(l:list A): insert a l <> (empty).
  Proof. intro H. absurd (In a empty). simpl; auto. rewrite <- H.
         eauto.  Qed. 
    
  Lemma insert_elim (a b: A)(l: list A): In a (insert b l)-> ( a=b \/ In a l).
  Proof. { induction l.
         simpl. left. symmetry. tauto. intro H.
         simpl in H. destruct (b == a0) eqn: eqH.  
         right;auto. destruct H. right;subst a0;auto.
         cut (a=b \/ In a l). intro H1;destruct H1. left;auto. right; eauto.
         auto.  } Qed. 
  
  Lemma insert_elim1 (a b: A)(l: list A): In a (insert b l)-> ~ In a l -> a=b.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. auto. absurd (In a l);auto. } Qed.
  Lemma  insert_elim2 (a b: A)(l: list A): In a (insert b l)-> a<>b-> In a l.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. absurd (a=b); auto. auto. } Qed.
  
  Hint Resolve insert_elim insert_elim1 insert_elim2: core.
  Lemma insert_iff (a b:A)(l:list A): In a (insert b l) <-> (a=b \/ In a l).
  Proof. split; auto. Qed.

  
  Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).
  Proof. { induction l. simpl. constructor;auto.
         { intro H. simpl. destruct (a == a0) eqn: eqH.
           { auto. }
           { constructor. intro H1.
           assert (H2: a0 =a \/ In a0 l); eauto.
           destruct H2. subst a0. switch_in eqH. apply eqH. eauto. 
           absurd (In a0 l); auto. eauto. } } } Qed.
  
  Hint Resolve insert_nodup : core.

    
  (*------------ list remove operation on ordered list ----------------------------------- *)
   Fixpoint delete (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match a == a1 with
               |true => l1
               |false => a1:: delete a l1
               end
    end.
   (* This function deletes only the first occurence of 'a' from the list l *)
  
  Lemma delete_elim1 (a b:A)(l: list A): In a (delete b l)-> In a l.
  Proof. { induction l. simpl. auto.
         { simpl. destruct (b == a0) eqn: eqH.
           { right;auto. }
           { intro H1. destruct H1. left;auto. right;auto. } } } Qed.
  
  Lemma delete_elim0 (a: A)(l: list A): (delete a l) [<=] l.
  Proof. induction l. simpl. auto. destruct (a==a0) eqn: H1. simpl. 
  rewrite H1. auto. simpl. rewrite H1. eauto. Qed.
  
  Lemma delete_elim2 (a b:A)(l: list A): NoDup l -> In a (delete b l)-> (a<>b).
  Proof. { induction l. simpl. auto.
         { simpl. destruct  (b == a0) eqn: eqH.
           { intros H1 H2. move /eqP in eqH. subst b. intro H3. subst a.
             absurd (In a0 l); eauto. }
           { intros H1 H2. destruct H2. intro. subst a0; subst a.
             switch_in eqH. apply eqH. eauto. eauto. } } } Qed.
  
  Lemma delete_intro (a b: A)(l:list A): In a l -> a<>b -> In a (delete b l).
  Proof. { induction l. simpl.  auto.
         { simpl. destruct (b == a0) eqn: eqH.
           { intros H1 H2. destruct H1. move /eqP in eqH. subst a; subst b.
             absurd (a0=a0); auto. auto. }
           { intros H1 H2. simpl. destruct H1. left;auto. right;auto. } } } Qed.

   Lemma delete_intro1 (a: A)(l:list A): ~In a l -> l=(delete a l).
  Proof. { induction l. simpl.  auto.
         { simpl. intros. destruct (a == a0) eqn: eqH. 
           move /eqP in eqH. subst a. destruct H. left. auto. 
           cut (l = delete a l). intros. rewrite<- H0. auto.
           
           assert (Hl:(~(a0 = a) /\ ~(In a l))).
           auto. destruct Hl.  
           apply IHl in H1. exact. }} Qed.
  Lemma delete_intro2 (a:A)(l:list A): NoDup l -> ~In a (delete a l).
  Proof. { intro. intro.
         induction l as [|a0 l']. simpl in H0. exact. simpl in H0.
         destruct (a == a0) eqn:Haa0. move /eqP in Haa0.
         subst a. assert (Hl: ~In a0 l'). eauto. contradiction.
         destruct H0. move /eqP in Haa0. auto. apply IHl' in H0. exact.
          eauto. } Qed.
                    
  Hint Resolve delete_elim0 delete_elim1 delete_elim2 delete_intro: core.
  Lemma delete_iff (a b:A)(l: list A): NoDup l -> (In a (delete b l) <-> (In a l /\ a<>b)).
  Proof. intro H. split. eauto.
         intro H0. destruct H0 as [H0 H1]. eauto.  Qed. 
  
  
   Lemma delete_nodup (a:A)(l: list A): NoDup l -> NoDup (delete a l).
  Proof.  { induction l. simpl. constructor.
          { intro H. simpl. destruct (a == a0) eqn: eqH. 
            { eauto. }
            {  switch_in eqH. constructor. intro H1. absurd (In a0 l). all: eauto. } } } Qed.
     Lemma delete_exchange (a b:A)(l: list A): 
     (delete a (delete b l)) = (delete b (delete a l)).
  Proof.  { induction l. simpl. auto. simpl.
            destruct (b == a0) eqn: Hba0. 
            destruct (a == a0) eqn: Haa0.   
            { move /eqP in Hba0. move /eqP in Haa0.
            subst a. subst b. auto. }
            { simpl. rewrite Hba0. auto. }
            destruct (a == a0) eqn: Haa0.
            { simpl. rewrite Haa0. auto. }
            { simpl. rewrite Hba0. rewrite Haa0. 
              rewrite IHl. auto. }} Qed.
    Lemma delete_equal (a :A)(l1 l2: list A): 
     l1 =l2 -> (delete a l1) = (delete a l2).
  Proof.  { intros. rewrite H. auto. } Qed.
  
    Lemma list_head (l1 l2: list A)(x:A): x::l1=x::l2->l1=l2. 
  Proof. {intros. apply delete_equal with (a:=x) in H.
          simpl in H. assert(x==x=true).
          apply /eqP. auto. rewrite H0 in H. auto. } Qed. 
           
    Lemma delete_subset (a:A)(l s: list A): l [<=] s -> delete a l [<=] s.
    Proof. { intro. unfold "[<=]" in H. unfold "[<=]".
           intros. assert (H1: In a0 l). eauto. apply H in H1. exact. } Qed.
    Lemma delete_subset2 (a:A)(l s: list A): l [<=] s -> NoDup l-> 
    delete a l [<=] delete a s.
    Proof. { intro. unfold "[<=]" in H. unfold "[<=]".
           intros. destruct (a0==a) eqn:H2. move /eqP in H2. subst a0.
           apply delete_elim2 in H1. destruct H1. auto. exact.
           assert (H3: In a0 l). eauto. eauto. } Qed.
                 
  Hint Resolve delete_nodup: core.
  
  

(*--- Index (idx x l) function to locate the first position of the element x in list l ----- *)
Fixpoint idx (x:A)(l: list A):= match l with
                                |nil => 0
                                |a::l' => match (x==a) with
                                        | true => 1
                                        |false => match (memb x l') with
                                                 |true => S (idx x l')
                                                 |false => 0
                                                 end
                                         end
                                end.
Lemma absnt_idx_zero (x:A)(l:list A): ~ In x l -> (idx x l)=0.
Proof. { induction l.
       { simpl. auto. }
       { intro H. simpl.
         replace (x ==a ) with false. replace (memb x l) with false. auto.
         symmetry;switch; auto.
         symmetry;switch;move /eqP. intro H1. subst x. auto. } } Qed.

Lemma idx_zero_absnt (x:A)(l:list A): (idx x l)=0 -> ~ In x l.
Proof. { induction l.
         { simpl. auto. }
         { intros H1 H2. inversion H1.
           destruct (x==a) eqn:Hxa. inversion H0.
           destruct (memb x l) eqn: Hxl. move /membP in Hxl.
           inversion H0. assert (H3: x=a \/ In x l). auto.
           destruct H3. subst x. conflict_eq. switch_in Hxl. apply Hxl.
           apply /membP. auto. } } Qed.

Lemma idx_gt_zero (x:A)(l: list A): In x l -> (idx x l) > 0.
Proof. { intro H. assert (H1: idx x l = 0 \/ ~ idx x l =0). eauto.
       destruct H1.
       { absurd (In x l). apply idx_zero_absnt. auto. auto. }
       { lia. } } Qed.

Lemma idx_is_one (a:A)(l: list A): idx a (a::l) = 1.
Proof. simpl. replace (a==a) with true; auto. Qed.

Hint Immediate absnt_idx_zero idx_zero_absnt idx_gt_zero idx_is_one: core.

Lemma idx_successor (x a:A)(l: list A): In x (a::l)-> x<>a -> idx x (a::l) = S (idx x l).
Proof. { intros H H1. destruct H.
         { subst a. conflict_eq. }
         { simpl. replace (x==a) with false. replace (memb x l) with true. all: auto. } } Qed.

Lemma nodup_idx_successor(x a: A)(l: list A):In x (a::l)-> NoDup(a::l)-> idx x (a::l)= S(idx x l).
Proof. { intros H H1. destruct H.
         { subst x. simpl. replace (a==a) with true. replace (idx a l) with 0.
           auto. symmetry. apply absnt_idx_zero; auto. auto. }
         { apply idx_successor. auto. intro H2. subst x. absurd (In a l);auto. } } Qed. 

Lemma diff_index (x y:A)(l: list A): In x l -> In y l -> x<>y -> (idx x l <> idx y l).
Proof. { induction l.
       { simpl;auto. }
       { intros Hx Hy Hxy.
         assert (Hxa: x=a \/ x<>a); eauto.
         assert (Hya: y=a \/ y <> a); eauto.
         destruct Hxa;destruct Hya.
         {(* case x=a y=a *)
           subst x. subst y. contradiction. }
         { (* case x=a y<> a *) 
           subst x. replace (idx a (a::l)) with 1.
           destruct Hy. contradiction.
           assert (H1: idx y l > 0). auto.
           simpl. replace (y==a) with false. replace (memb y l) with true.
           intro H2. inversion H2. rewrite <- H4 in H1. inversion H1.
           auto. symmetry. switch. move /eqP. auto. symmetry;auto. }
         { (* case x<> a y = a *)
           subst y. replace (idx a (a::l)) with 1.
           destruct Hx. subst x. contradiction.
           assert (H1: idx x l > 0). auto.
           simpl. replace (x==a) with false. replace (memb x l) with true.
           intro H2. inversion H2. rewrite H4 in H1. inversion H1.
           auto. symmetry. switch. move /eqP. auto. symmetry;auto. }
         { (* case x<>a y <> a *)
           destruct Hx. symmetry in H1; contradiction.
           destruct Hy. symmetry in H2;contradiction.
           replace (idx x (a::l)) with (S (idx x l)).
           replace (idx y (a::l)) with (S (idx y l)).
           cut (idx x l <> idx y l). auto.
           apply IHl;auto. all: symmetry; apply idx_successor;auto. } } } Qed.

Lemma same_index (x y:A)(l: list A): In x l -> In y l -> (idx x l = idx y l) -> x=y.
Proof. { intros H H1 H2.
       assert (H3: x=y \/ x<>y). eapply reflect_EM;auto.
       destruct H3. auto.
       absurd(idx x l = idx y l); auto using diff_index. } Qed.

Hint Resolve idx_successor diff_index same_index: core.



(*----------------- Properties of list cardinality ------------------------------------*)

 Lemma delete_size1 (a:A)(l: list A): In a l -> |delete a l| = (|l| - 1).
   Proof. { induction l.
          { simpl; auto. }
          { intro H. simpl.
            destruct (a==a0) eqn: H1. lia.
            assert (H2: a<>a0). switch_in H1. auto.
            assert (H3: In a l). eauto.
            simpl. replace (|delete a l|) with (|l| - 1).
            cut (|l| > 0). lia. eauto.  symmetry;auto. } } Qed.

   
   Lemma delete_size1a  (a:A)(l: list A): In a l -> |l|= S(|delete a l|).
   Proof. intro h1. apply delete_size1 in h1 as h2. rewrite h2. simpl.
          destruct l. simpl. inversion h1. simpl. lia. Qed.
          
   Lemma delete_size1b (a:A)(l: list A): |delete a l| >= (|l| - 1).
   Proof. { induction l.
          { simpl; auto. }
          { simpl.
            destruct (a==a0) eqn: H1. lia.
            assert (H2: a<>a0). switch_in H1. auto.
            simpl. 
            cut (|l| >= 0). lia. lia. } } Qed.  
   
  Lemma delete_size2 (a:A)(l: list A): ~ In a l -> |delete a l| = |l|.
  Proof. { induction l.
         { simpl; auto. }
         { intros H.
           assert (H1: a<> a0).
           { intro H1; subst a. absurd (In a0 (a0::l)); auto. }
           assert (H2: ~ In a l). auto.
           simpl. replace (a==a0) with false.
           simpl. auto. auto. } } Qed.
  
  Lemma delete_size (a:A) (l:list A): |delete a l| <=|l|.
  Proof. { assert (H: In a l \/ ~ In a l). eauto.
         destruct H. replace (|delete a l|) with (|l| - 1). lia.
         symmetry;auto using delete_size1.
         replace (|delete a l|) with (|l|). auto.
         symmetry; auto using delete_size2. } Qed.

  Hint Immediate delete_size delete_size1 delete_size2: core.

   
  Lemma subset_cardinal_le (l s: list A): NoDup l -> l [<=] s -> |l| <= |s|.
  Proof. { revert s. induction l.
         { simpl. intros. lia. }
         { intros s H H1. assert (H2: NoDup l). eauto.
           assert (H3: ~ In a l). eauto. assert (Has: In a s). auto.
           assert (H4: l [<=] (delete a s)).
           { intros x H4. apply delete_intro.
             auto. intro H5. subst x. contradiction. }
           simpl. assert (H5: |l| <= | delete a s|).
           { apply IHl;auto. }
           replace (|delete a s|) with (|s| -1) in H5. revert H5.
           cut(|s| > 0). intros. lia. eauto.
           symmetry. auto using delete_size1. } } Qed.
           
  Lemma subset_cardinal_lt (l s: list A)(a: A):
    NoDup l -> l [<=] s->  In a s -> ~ In a l -> |l| < |s|.
  Proof. { intros H H1 H2 H3.
         assert (H4: l [<=] (delete a s)).
         { intros x H4. apply delete_intro. auto.
           intro H5. subst x. contradiction. }
         assert (H5: |l| <= | delete a s|).
         { auto using subset_cardinal_le. }
         replace (|delete a s|) with (|s| -1) in H5. revert H5.
         cut(|s| > 0). intros. lia. eauto.
         symmetry. auto using delete_size1. } Qed.

Lemma no_subset_existsA (l s: list A):
~subset l s -> exists a, In a l/\~In a s.
Proof. revert s. induction l. simpl. intros. destruct H. auto.
intros. simpl in H. destruct (memb a s) eqn: Hs. simpl in H.
apply IHl in H. destruct H.  exists x. split. simpl. right. 
apply H. apply H. simpl in H. simpl. exists a. split. auto. 
move /membP in Hs. auto. Qed. 

Lemma subset_elim1 (a:A)(l1:list A)(l2:list A) : l1 [<=]a::l2 -> a::l1 [<=]a::l2.
Proof. unfold "[<=]". intros. simpl in H0. destruct H0. subst a. auto. eapply H in H0. exact H0. Qed. 
Lemma subset_elim2 (a:A)(l1:list A)(l2:list A) : l1 [<=]l2 -> a::l1 [<=]a::l2.
Proof. unfold "[<=]". intros. simpl in H0. destruct H0.  subst a. auto. simpl. eapply H in H0. right. exact H0. Qed.

Lemma subset_elim3 (l1 l2:list A)(a1 a2:A)(ND:NoDup (a2::l2)):
a1::l1 [<=] a2 :: l2 -> a2 <> a1 -> ~In a2 l1 -> 
(a1::l1) [<=] l2.
Proof. unfold "[<=]". intros. specialize (H a). simpl in H. destruct H2. 
{ destruct H. left. auto. subst. elim H0. auto. auto. }
{ destruct H. right. auto. subst a. contradiction. exact. } Qed.

Lemma last_in_list (l:list A)(x:A)(d:A) : In x l -> In (last l d) l.
Proof. { revert x d. 
         induction l as [| a l'].
         { (*------ l = nil ------*) 
           simpl. auto. }
         { (*------ l = a::l'-----*)
           destruct l' as [| b l'']. 
           { (*----- l = [a]------*)
            simpl. intros; left;auto. }
           { (*------ l = a ::b::l'' --------*) 
             intros x d H0.
             assert (H1: last (a::b::l'') d = last (b::l'') d).
             { simpl. destruct l'';auto. }
             rewrite H1.
             cut(In (last (b :: l'') d) (b :: l'')). auto.
             eapply IHl' with (x:=b). auto. } } } Qed.

(*

Fixpoint nth (l: list A)(k:nat)(d:A):=
match (l,k) with 
|(nil, _) => d 
|(_, 0) => d 
|(hd::tail, 1) => hd 
|(hd::tail, S k) => (nth tail k d)
end.
*)
  Hint Resolve subset_cardinal_le subset_cardinal_lt subset_elim1 subset_elim2: core.

End DecLists.



 Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: core.
 Hint Resolve insert_elim insert_elim1 insert_elim2: core.
 Hint Resolve insert_nodup :core.

 Hint Resolve delete_elim0 delete_elim1 delete_elim2 delete_intro delete_intro1 delete_intro2 delete_size: core.
 Hint Resolve delete_size1a delete_size1 delete_size1b delete_size2: core.
 Hint Resolve delete_nodup list_head: core.
 
Hint Immediate absnt_idx_zero idx_zero_absnt idx_gt_zero idx_is_one: core.
Hint Resolve idx_successor diff_index same_index: core.


 Hint Resolve subset_cardinal_le subset_cardinal_lt subset_elim1 subset_elim2: core.
  


(*########################## Next Part of the library ###############################*)






(*Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecSort MinMax.
Require Export DecType SetReflect.
Require Export DecList.*)



Set Implicit Arguments.



Section MoreDecList.

Context { A: eqType}.
(*------------------ Uniform list -----------------------------------------------------*)
  
Inductive uniform : list A -> Prop:=
| Nil_uni: uniform nil
|Sing_uni(a:A): uniform (a::nil)
|Ind_uni(a b:A)(l:list A): a=b -> uniform (b::l)-> uniform (a::b::l).

Lemma uniform_elim (a:A)(l: list A): uniform (a::l)-> (forall x, In x l -> x=a).
Proof. { revert l. induction l. 
       { simpl. intros H0 fA f. destruct f. }
       { simpl. intros H fA. inversion H. intro H5.  destruct H5 as [H5| H6].
        subst fA. symmetry. exact. apply IHl in H6. exact. subst a. exact. } } Qed. 


Lemma uniform_elim1 (a:A)(l: list A): uniform (a::l)-> (forall x, In x (a::l)-> x=a).
Proof. { induction l. 
        { simpl. intros. destruct H0. auto. inversion H0. }
        { intros. inversion H. subst a0.  simpl in H0. destruct H0. 
        auto. apply IHl. exact. simpl. exact. } } Qed.

Lemma uniform_elim2 (a:A) (l: list A): uniform (a::l)-> uniform l.
Proof. intro H. inversion H. constructor. exact. Qed.

Lemma uniform_elim4 (a1 a2:A) (l: list A) : uniform l -> In a1 l -> In a2 l -> a1=a2.
Proof. { induction l.
         { simpl. intros H1 H2. destruct H2. }
         { intros H1 H2 H3.
           assert (H0:(forall x, In x (a::l)-> x=a)).
           apply uniform_elim1. exact. specialize (H0 a1) as Ha1.
           apply Ha1 in H2. specialize (H0 a2) as Ha2.
           apply Ha2 in H3. subst a1. subst a2. auto. }} Qed.
      

Lemma uniform_elim3 (a:A) (l:list A): uniform l -> uniform (delete a l).
Proof. { revert a. 
         induction l. 
         { simpl. auto. }
         { intros.  
           case l eqn:H0. 
           { simpl. destruct (a0==a) eqn: Ha. constructor. constructor. }
           { simpl. destruct (a0==a) eqn: Ha. eapply uniform_elim2.
             exact H.
           { apply uniform_elim2 in H as H1.  specialize (IHl a0) as Hl.
             apply Hl in H1. 
             destruct (a0 == e) eqn:Hae.
             {  move /eqP in Ha.  move /eqP in Hae.  assert (H2: a<> e).
                intro. subst a0. auto. 
                apply uniform_elim4 with (a1:=a) (a2:=e) in H. subst a. 
                destruct H2. all:auto. }
             {  apply uniform_elim4 with (a1:=a) (a2:=e) in H.
                subst a. constructor. auto. simpl in H1. 
                rewrite Hae in H1. all:auto.  }}}}} Qed.

Lemma uniform_intro (a:A)(l: list A): (forall x, In x l -> x=a) -> uniform (a::l).
Proof. { intros. induction l. 
         { simpl. intros. constructor. }
         { simpl. intros.  assert (H1: (forall x : A, In x l -> x = a)).
           auto. specialize (H a0) as Ha0. assert (H2: In a0 (a0 :: l)).
           auto. apply Ha0 in H2. subst a0. apply IHl in H1.
           constructor. auto. exact. }} Qed.
Lemma uniform_subset (l1 l2: list A): 
l1 [<=] l2 -> uniform (l2) -> uniform l1.
Proof. { revert l2. induction l1. 
         { simpl. intros. constructor. }
         { simpl. intros. 
           assert(In a l2). eauto.
           assert (Ha: (forall x : A, In x l2 -> x = a)).
           intros. eapply uniform_elim4. eauto. auto. auto.
           apply uniform_intro.
           intros. assert(In x l2).
           eauto. apply Ha with (x:=x) in H3. auto. } }
 Qed.


(* ----------------- delete_all operation ---------------------------------------------  *)

Fixpoint del_all (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match  (a == a1) with
               |true => del_all a l1
               |false => a1 :: del_all a l1
               end
    end.

(* This function deletes all occurences of a in the list l *)

  Lemma del_all_elim1 (a b:A)(l: list A): In a (del_all b l)-> In a l.
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. destruct (a==a0) eqn:H0. intros. left. move /eqP in H0.
            auto. destruct (b==a0) eqn:H1. intros. right. apply IHl in H.
            exact. simpl. intros H2. destruct H2. left. exact.
            right. apply IHl in H. exact. } } Qed.
  
  Lemma del_all_elim2 (a b:A)(l: list A): In a (del_all b l)-> (a<>b).
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. destruct (b==a0) eqn:H0. exact. simpl. intros H1.
            destruct H1.  move /eqP in H0. subst a0. auto. 
            apply IHl in H. exact. } } Qed.

  Lemma del_all_intro (a b: A)(l:list A): In a l -> a<>b -> In a (del_all b l).
  Proof. { induction l. 
          { simpl. auto. } 
          { simpl. intros H1 H2. destruct H1. destruct (b==a0) eqn: H3.
            move /eqP in H3. subst a0. subst b. apply IHl in H2. exact. tauto.
            simpl. left. auto. destruct (b==a0) eqn: H4. apply IHl in H2.
            exact. exact. simpl. right. apply IHl in H2. exact. exact. }} Qed.
  
  
  Lemma del_all_iff (a b:A)(l: list A): (In a (del_all b l) <-> (In a l /\ a<>b)).
  Proof. { induction l. 
          { simpl. split. auto.  intros H. destruct H. auto. }
          { simpl. destruct (b==a0) eqn: H0. split. intros. split. right.
           apply IHl in H. destruct H. exact. apply IHl in H. destruct H.
           auto. intros H. destruct H. destruct H. move /eqP in H0. subst
           a0. subst b. tauto. apply IHl. split. exact. exact. simpl. split.
           intros H. destruct  H. split. left. auto. move /eqP in H0. 
           subst a0. auto. split. apply IHl in H. destruct H. right. exact.
           apply IHl in H. destruct H. exact. simpl. intros. destruct H.
           destruct H. left. exact.  assert (H2: (In a l) /\ (a<>b)). split.
           exact. exact.  apply IHl in H2. right. exact. } } Qed. 


  Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
  
  Lemma del_all_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. intros H. destruct (a==a0) eqn: H1. move /eqP in H1.
            subst a0. eauto. assert (H0:NoDup l). eauto. apply IHl in H0.
            assert (H2: ~(In a0 l)). eauto. 
            assert (H3: ~(In a0 (del_all a l))). eauto. eauto. } } Qed.

  Hint Resolve del_all_nodup: core.

 (* ------- count of an element a in the list l ----------------------------------------*)

 Fixpoint count (a:A) (l:list A) : nat:= match l with
                          | nil => 0
                          |a1::l1 => match a == a1 with
                                    |true => S (count a l1)
                                    |false => count a l1
                                    end
                                        end.
  Lemma countP1 (a:A) (l:list A): In a l -> (count a l >= 1).
  Proof. { induction l. 
          { intros H. inversion H. }
          { intros H. simpl in H. destruct H. subst a0. simpl. 
           destruct (a==a) eqn:H0. lia. move /eqP in H0. absurd (a=a).
           exact. exact. apply IHl in H. simpl. destruct (a==a0) eqn:H0.
           lia. exact. } } Qed.
  Lemma countP1b (a:A) (l:list A): (count a l >= 1) -> In a l.
  Proof. { induction l. 
          { intros H. inversion H. }
          { intros H. simpl in H.
           simpl. 
           destruct (a==a) eqn:H0. 
           destruct (a == a0) eqn: Ha.  
           left. move /eqP in Ha. auto. right.
           apply IHl in H. exact.
           destruct (a == a0) eqn: Ha. 
           left. move /eqP in Ha. auto. right. 
           apply IHl in H. exact. } } Qed.  
  
  Lemma countP2 (a:A)(l: list A): ~ In a l -> (count a l = 0).
  Proof. { intros. induction l. 
          { simpl. auto. }
          { simpl. destruct (a==a0) eqn: H0. move /eqP in H0. subst a0. 
           simpl in H. destruct H. left. exact. move /eqP in H0. 
           assert (H1: ~(In a l)). eauto. apply IHl in H1. exact. } } Qed. 
  
  Lemma countP3 (a:A)(l: list A): (count a l = 0) -> ~ In a l.
  Proof. { induction l. 
          { simpl. auto. } 
          { simpl. destruct (a==a0) eqn:H0. intros. lia. intros. 
            apply IHl in H. move /eqP in H0. intro.  destruct H1. auto.
            eauto. } } Qed. 
  
  Lemma countP4 (a:A)(l: list A): count a (a::l) = S (count a l).
  Proof. simpl. destruct (a==a) eqn:H. exact. move /eqP in H. auto. Qed.
  
  Lemma countP5 (a b:A)(l: list A): (count a l) <= count a (b::l).
  Proof. { induction l. 
         { simpl. lia. } 
         { simpl. destruct (a==a0) eqn:H0. destruct (a==b) eqn:H1. lia.
           lia. destruct (a==b) eqn: H1. lia. lia. } } Qed.
 
  Lemma countP6 (a: A)(l: list A): count a l <= |l|.
  Proof. { induction l. simpl. lia. simpl. destruct (a==a0) eqn:H0.
  lia. lia. } Qed.
  
  Lemma countP7 (a:A) (l:list A): In a l -> count a l = S(count a (delete a l)).
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. intro H. destruct H as [H1 | H2]. destruct (a==a0) eqn: H0.
            exact. move /eqP in H0. auto. destruct (a==a0) eqn: H0. exact.
            apply IHl in H2. move /eqP in H0. simpl. destruct (a==a0) eqn: H1.
            move /eqP in H1. auto. exact. } } Qed.
 
  Lemma countP8 (a:A) (l:list A): forall x, x<>a-> count x (a::l) = count x l.
  Proof. { induction l. 
          { simpl. intros. destruct (x==a) eqn: H0. move /eqP in H0. auto. 
           exact. } 
          { intros. simpl. destruct (x==a) eqn:H0. move /eqP in H0. auto.
            destruct (x==a0) eqn: H1. exact. exact. }} Qed.
  
  
  Lemma countP9 (a:A) (l:list A): forall x, x<>a -> count x l = count x (delete a l).
  Proof. { induction l. 
          { simpl. intros;auto. }
          { intros. simpl. destruct (x==a0) eqn: H0. destruct (a==a0) eqn:H1.
            move /eqP in H0. move /eqP in H1. subst a0. auto. simpl. 
            destruct (x==a0) eqn: H2. auto. auto. destruct (a==a0) eqn:H2. 
            exact. simpl. destruct (x==a0) eqn: H3. inversion H0. auto. }}  Qed.
  
  Lemma countP10 (a:A)(l s:list A): count a l <= count a s -> count a (a::l) <= count a (a::s).
  Proof. { induction l. 
          { simpl. intros. destruct (a==a) eqn: H1. lia. lia. }
          { simpl. intros. destruct (a==a0) eqn:H1. destruct (a==a) eqn:H2.
            lia. lia. destruct (a==a) eqn: H2. lia. lia. } } Qed. 
  
  Lemma countP11 (a:A)(l s: list A): count a l = count a s -> count a (a::l) = count a (a::s).
  Proof. { induction l. 
          { simpl. intros. destruct (a==a) eqn: H1. auto. exact. }
           { simpl. destruct (a==a0) eqn:H1. intros. destruct (a==a) eqn:H2.
            lia. lia. destruct (a==a) eqn: H2. intros. lia. lia. }} Qed.
  
  Lemma countP12 (a:A)(l s: list A): count a l < count a s -> count a (a::l) < count a (a::s).
  Proof. {  induction l. 
          { simpl. intros. destruct (a==a) eqn: H1. lia. exact. }
          { simpl. destruct (a==a0) eqn: H2. destruct (a==a) eqn: H1. intros.
            lia. intros. lia. destruct (a==a) eqn: H1. intros. lia.
            intros. lia. }} Qed.
    Hint Immediate countP1 countP2 countP3: core.
  Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9: core.

  Lemma count_nodup (l:list A): (forall x, In x l -> count x l <=1)-> NoDup l.
  Proof. { intros H.
         induction l. 
         { auto. }
         { cut (NoDup l). cut (~In a l). auto. intros H1.
          specialize (H a) as H2. 
          assert (H3:  count a (a :: l) <= 1). apply H2. auto.
          simpl in H3. replace (a==a) with true in H3.
          inversion H3. absurd (In a l). apply countP3. auto.
          exact. inversion H4. auto.
          apply IHl. intros x H1.
          cut ( count x l <= count x (a::l)).
          intros H2.
          assert (H3: count x (a :: l) <= 1).
          { apply H. auto. }
          lia. apply countP5. }} Qed.
           
  Lemma nodup_count (l:list A) (x:A): NoDup l -> count x l <=1.
  Proof. { intros H1.
           induction l. simpl. auto. 
           simpl. destruct(x == a) eqn: Ha. 
           move /eqP in Ha. subst x.
           assert(~In a l). eauto.
           assert (count a l = 0).
           eauto. lia. apply IHl. eauto. } Qed.
  Lemma uniq_count (l: list A) (a:A): In a l -> count a (uniq l) = 1.
  Proof. intros. apply uniq_intro_elim in H as H1. assert (NoDup (uniq l)) as H2.
         eauto. apply nodup_count with (x:=a) in H2. assert (count a (uniq l) >= 1). 
         eauto. lia.  Qed.
  
  Hint Immediate count_nodup nodup_count: core.
 
End MoreDecList.

 Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
 Hint Resolve del_all_nodup: core.

 Hint Immediate countP1 countP1b countP2 countP3: core.
 Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9:  core.
 Hint Resolve countP10 countP11 countP12 uniq_count: core.
 Hint Immediate count_nodup nodup_count: core.

Section Permutation.

  Context { A: eqType }.
  
   Lemma EM:forall x y : A, x=y \/ x<>y.
   Proof. eauto. Qed.
   
(*   Definition empty: list A:= nil.*)

   Lemma count_in_putin1 (a: A)(l: list A)(lr: A-> A-> bool):
     count a (putin lr a l)= S (count a l).
   Proof. { induction l. simpl. destruct (a==a) eqn:H. auto. conflict_eq. 
           { simpl. case (lr a a0) eqn: H0.
             { destruct (a==a0) eqn:H1. move /eqP in H1.
               subst a0. assert (H: count a (a::a::l)=S(count a (a::l))). eauto.
               rewrite H. eauto.
               assert (H: count a (a :: a0 :: l) = S (count a (a0::l))).
               eauto.  move /eqP in H1. rewrite H. eauto. }
             { simpl. destruct (a==a0) eqn:H1. lia. auto. } } } Qed.
   
   Lemma count_in_putin2 (a b: A)(l: list A)(lr: A-> A-> bool):
     a<>b -> count a l = count a (putin lr b l).
   Proof. { induction l.
            { simpl; destruct (a==b) eqn:H. intros;conflict_eq. auto. }
            { intros.  simpl. case (lr b a0) eqn: H0.
              { destruct (a==a0) eqn:H1.
                move /eqP in H1. subst a0.
                replace (count a (b :: a :: l)) with (count a (a :: l)).
                eauto. symmetry; auto. move /eqP in H1.
                replace (count a (b :: a0 :: l)) with (count a (a0 :: l)).
                all: symmetry;eauto. }
              { destruct (a==a0) eqn: H1.
                move /eqP in H1. subst a0.
                replace (count a (a :: putin lr b l)) with (S(count a (putin lr b l))).
                 eauto. symmetry. auto. 
                replace (count a (a0 :: putin lr b l)) with (count a (putin lr b l)).
                auto. move /eqP in H1. symmetry;auto. }  } } Qed.
   
  Lemma count_in_sorted (a: A)(l: list A)(lr: A-> A-> bool): count a l = count a (sort lr l). 
  Proof. { induction l. simpl; auto.
           simpl. destruct  (a == a0) eqn:H0.
           move /eqP in H0. subst a.
           rewrite IHl. symmetry; apply count_in_putin1.
           move /eqP in H0. rewrite IHl.  apply count_in_putin2. auto. }  Qed.


  Hint Resolve count_in_putin1 count_in_putin2 count_in_sorted: core.
  
  (* ---------------  sublist of a list (subsequence)------------------------------------ *)

  Fixpoint sublist (l s: list A): bool := match (l, s) with
                                              |(nil , _) => true
                                              |(a::l1, nil) => false
                                              |(a::l1, b::s1) => match (a == b) with
                                                          |true => sublist l1 s1
                                                          |false => sublist l s1
                                                          end
                                       end.
  
  Lemma sublist_intro (l: list A): sublist nil l.
  Proof.   destruct l;simpl;auto. Qed.
  Lemma sublist_reflex (l: list A): sublist l l.
  Proof. induction l;simpl.
         auto. destruct (a==a) eqn:H; [auto | conflict_eq].  Qed.

 
  Lemma sublist_elim1 (l: list A): sublist l nil -> l=nil.
  Proof. destruct l; [auto | simpl; intro H; inversion H]. Qed.

  Lemma sublist_elim2 (a:A)(l s: list A): sublist (a::l) s -> In a s.
  Proof. induction s.  simpl; auto. simpl. destruct (a==a0) eqn:H. move /eqP in H.
         subst a0; auto. intro;right;auto. Qed.
  
  Lemma sublist_elim3 (a: A)(l s: list A): sublist (a::l) s -> sublist l s.
  Proof. { revert l; revert a. induction s.
         { auto. }
         { intros a0 l. 
           simpl. destruct (a0 == a) eqn:H.
           { destruct l. auto.  destruct (e == a) eqn:H1.
             apply IHs. auto.  }
           { destruct l. auto.  destruct (e == a) eqn:H1.
             { intro H2. assert (H2a: sublist (e::l) s). eapply IHs;exact H2.
               eapply IHs; exact H2a. }
             { apply IHs. }
         } } } Qed.
  
  Lemma sublist_elim3a (a e: A)(l s: list A): sublist (a::l)(e::s)-> sublist l s.
  Proof. simpl. destruct (a==e) eqn:H. auto.   eauto using sublist_elim3. Qed.
  
   Lemma sublist_intro1 (a:A)(l s: list A): sublist l s -> sublist l (a::s).
   Proof.  { revert s;revert a. induction l.
           { auto. }
           { intros a0 s.
             simpl. destruct (a == a0) eqn:H. apply sublist_elim3. auto. } } Qed.

   Lemma sublist_Subset (l s: list A): sublist l s -> Subset l s.
   Proof. { revert s. induction l.  eauto.
           intros s H. eauto. unfold "[<=]". intros x H1.
           destruct H1. subst x. eauto using  sublist_elim2. apply sublist_elim3 in H.
           apply IHl in H. eauto. } Qed.

  Lemma uniq_sublist (l: list A): sublist (uniq l) l.
  Proof. { induction l. 
           { simpl. auto. }
           { simpl. destruct (memb a l) eqn: Hal.
              { destruct (uniq l) eqn: Hul.
                { auto. }
                { destruct (e == a) eqn: Hea.
                  { apply sublist_elim3 in IHl. auto. }
                  { auto. }
                } }
              { destruct (a == a) eqn: Haa. auto. move /eqP in Haa. destruct Haa. auto. } }} Qed.
              

   Lemma sublist_elim4 (l s: list A): sublist l s -> (forall a, count a l <= count a s).
   Proof. { revert l. induction s as [| e s'].
          { intro l. intro H. assert (H1: l=nil); auto using sublist_elim1.
            subst l; auto.  }
          { intros l H x. destruct l as [|a l'].
            simpl. lia. destruct (x==a) eqn:Hxa.
            { move /eqP in Hxa. subst x.
              simpl in H. destruct (a == e) eqn: Hae. move /eqP in Hae.
              subst e.
              cut (count a l' <= count a s'); auto.
              assert (H1: count a (a :: l') <= count a  s'). eauto.
              cut (count a s' <= count a (e::s')). lia. auto. }
            { assert (H1: count x (a::l')<= count x s').
              { simpl. rewrite Hxa. eauto using sublist_elim3a. }
              cut (count x s' <= count x (e::s')). lia. auto. } } } Qed.
   
   (*

  Hint Extern 0 (is_true ( sublist ?x ?z) ) =>
  match goal with
  | H: is_true (sublist x  ?y) |- _ => apply (@sublist_trans  x y z)
  | H: is_true (sublist ?y  z) |- _ => apply (@sublist_trans  x y z) 
  end.
*)
    
 
  Hint Resolve sublist_intro sublist_intro1 sublist_reflex sublist_Subset sublist_elim1: core.
  Hint Resolve sublist_elim2 sublist_elim3 sublist_elim4: core.


  (* -------------- list inclusion (subset in multiset) ----------------------------------*)

  Fixpoint included (l s: list A): bool := match l with
                                        |nil => true
                                        | a::l1 => match (memb a s) with
                                                  |true => included l1 (delete a s)
                                                  |false => false
                                                  end
                                        end.
  Lemma included_intro1 (l: list A): included nil l.
  Proof.  auto. Qed. 
  
   Lemma included_refl (l: list A): included l l.
  Proof. { induction l. auto. simpl. destruct (a==a) eqn:H0. auto. move /eqP in H0. auto. } Qed.
  
  Lemma included_intro2 (a:A)(l s: list A): In a s -> included l (delete a s)-> included (a::l) s.
  Proof. { induction s. 
          { simpl. auto. } 
          { simpl. intros H1 H2. destruct H1. destruct (a==a0) eqn: H3. auto.
            move /eqP in H3. auto. destruct (a==a0) eqn: H3. simpl. exact.
            simpl.  assert (H4: memb a s). eauto. case (memb a s) eqn:H5.
            exact. auto. } } Qed.
   
   

  Lemma included_intro (l s: list A): (forall a, count a l <= count a s)-> included l s.
  Proof. { revert s. induction l. intros;apply included_intro1;auto.
           { intros s H. simpl.  case (memb a s) eqn:Has;move /membP in Has.
             apply IHl. intro x. destruct (EM x a).
             2:{  replace (count x l) with (count x (a::l)).
             replace (count x (delete a s)) with (count x s).
             all: eauto. } subst x. 
             replace (count a l) with ((count a (a::l)) -1). 
             replace (count a (delete a s)) with ((count a s)-1).
             specialize (H a).  lia.
             replace (count a s) with (S (count a (delete a s))). lia.
             symmetry; eauto.
             replace (count a (a :: l)) with (S (count a l)). lia.
             symmetry; eauto.
             specialize (H a). rewrite countP4 in H.
             replace (count a s) with 0 in H. inversion H. symmetry; eauto. } } Qed. 


    Lemma included_intro3 (l s: list A): sublist l s -> included l s.
  Proof.  intro H. assert (H2: (forall a, count a l <= count a s)). eapply sublist_elim4. exact. eapply included_intro in H2. exact. Qed.
  
  Lemma included_elim1 (l: list A): included l nil -> l=nil.
  Proof. induction l. auto. intros. inversion H. Qed. 
  
  Lemma included_elim2 (a:A)(l s: list A): included (a::l) s -> In a s.
  
  Proof. { induction l. 
          {simpl. destruct (memb a s) eqn:H. auto. intro. inversion H0. }
          { simpl. destruct (memb a s) eqn:H. auto. intro. inversion H0. }}Qed.
 
  
  Lemma included_elim3 (a:A)(l s: list A): included (a::l) s -> included l (delete a s).
  Proof. { induction s.  
          { simpl. auto. }
          { simpl. destruct (a==a0) eqn:H0. simpl. auto. simpl. intros H. 
            destruct (memb a s) eqn:H1. auto. auto. } } Qed. 

  Lemma included_elim (l s: list A): included l s-> (forall a, count a l <= count a s).
  Proof. { revert s. induction l. simpl. intros;lia. 
           intros s H x. apply included_elim2 in H as H1. apply included_elim3 in H as H2.
           assert (H3: count a l <= count a (delete a s)).  eapply IHl with (s:= (delete a s)).
           auto.  destruct (EM x a).
           subst x. replace (count a (a::l)) with (S(count a l)).
           replace (count a s) with (S( count a (delete a s))).
           lia. symmetry; eauto.  eauto.  
           replace (count x (a::l)) with (count x l).
           replace (count x s) with  (count x (delete a s)).
           eauto. all: symmetry;eauto. } Qed. 

  Lemma included_elim4 (a:A)(l s: list A): included (a::l) s -> included l s.
  Proof. { intro H. assert (H1: (forall a0, count a0 (a::l) <= count a0 s)).
           eapply included_elim. exact. eapply included_intro. 
           assert (H2:forall a0 : A, (count a0 l)<=(count a0 (a :: l))). eauto.
           intros. specialize (H1 a0). specialize (H2 a0). lia. } Qed.
  

Lemma included_elim4b (a:A) (l s: list A) : included l s -> included (a::l) (a::s).
Proof. { intro H. apply included_intro. intro x. simpl.
         destruct (x==a) eqn: H1. cut ((count x l)<= (count x s)).
        lia. all:apply included_elim;exact. } Qed.

Lemma included_elim4a (a:A) (l: list A) : included (delete a l) l.
Proof. { induction l. simpl. auto. simpl. destruct (a == a0) eqn: H0. 
assert (H1: (forall a1, count a1 l <= count a1 (a0::l))). intros.
 eapply countP5. apply included_intro in H1. exact. 
  assert (H3:(included (delete a l) l)-> (included (a0 :: delete a l) (a0 :: l))). 
  eapply included_elim4b. eapply H3 in IHl. exact. } Qed.
  
  Lemma included_elim3a (a:A)(l s: list A): included l s -> included (delete a l) (delete a s).
  Proof. intros. apply included_intro. intros. apply included_elim with (a:=a0) in H.
         assert(a0=a\/a0<>a). eauto. destruct H0. 
      { subst a0.
         assert(In a l\/~In a l). eauto.
         assert(In a s\/~In a s). eauto.
         destruct H0;destruct H1.
         { apply countP7 in H0. apply countP7 in H1. lia. }
         { apply countP7 in H0. apply countP2 in H1. lia. }
         { assert(delete a l = l). symmetry;eauto. 
           rewrite H2.  apply countP7 in H1. apply countP2 in H0. lia. }
         { assert(delete a l = l). symmetry;eauto. 
           assert(delete a s = s). symmetry;eauto.
           rewrite H2. rewrite H3. lia. } }
       { apply countP9 with (l0:=l) in H0 as H1.
         apply countP9 with (l0:=s) in H0 as H2.
         lia. } Qed.   

  Lemma included_elim3b (a:A)(l s: list A): included l (a::s) -> 
  ~In a l -> included l s.
  Proof. intros. apply included_intro. intros. apply included_elim with (a:=a0) in H.
         simpl in H.
         assert(a0=a\/a0<>a). eauto. destruct H1. 
      { subst a0.
         assert(In a l\/~In a l). eauto.
         assert(In a s\/~In a s). eauto.
         destruct H1;destruct H2. eauto. eauto.
         { simpl in H. replace (a==a) with true in H. apply countP7 in H2.
           assert(delete a l = l). symmetry;eauto.   apply countP2 in H0. lia.
           eauto. }
         { apply countP2 in H0. apply countP2 in H2. lia. } } 
       { apply countP9 with (l0:=l) in H1 as H2.
         destruct (a0 == a) eqn:Ha. move /eqP in Ha. subst a. elim H1.  auto.
         auto. } Qed.
         
  Lemma included_elim3c (a:A)(l s: list A): included (l) (a::s) -> 
  included (delete a l) s.
  Proof. intros. eapply included_elim3a with (a:=a) in H.
         simpl in H. replace (a==a) with true in H. auto. eauto. Qed.
  
  
  Lemma included_elim3d (a:A)(l s: list A): included l s -> 
  included l (a::s).
  Proof. intros. apply included_intro. intros. apply included_elim with (a:=a0) in H.
         simpl in H. simpl. destruct (a0 == a). lia. auto. Qed.

   Lemma included_elim5 (l s: list A): included l s -> Subset l s.
  Proof. { unfold "[<=]". 
          induction l.
          { simpl. intros. destruct H0. }
          { intros.  destruct H0. eapply included_elim2 in H as H2.
           subst a0. exact. apply IHl. eapply included_elim4 in H as H3. 
           exact. exact. } } Qed.

           
    Lemma included_elim6 (l s: list A)(a b: A)(lr: A->A-> bool)(Hanti: antisymmetric lr): Sorted lr (a::l) -> Sorted lr (b::s) ->
     included (a::l) (b::s)-> a<>b -> included (a::l) s. 
    Proof. { intros H1 H2 H3 H4. 
           assert (H5: forall x, count x (a::l) <= count x (b::s)).
           { eapply included_elim;auto. }
           eapply included_intro.
           intros x. simpl.
           destruct (x == a) eqn: Hxa.
           { (*-----x=a----*)
            specialize (H5 a) as H6. simpl in H6. replace (a==b) with false in H6.
            replace (a==a) with true in H6. move /eqP in Hxa. subst x. exact.
            auto. auto. }
            { (*-----x<>a-----*)
              destruct (x==b) eqn:Hxb.
              {  (*----x=b---*) 
               move /eqP in Hxb. subst x. replace (count b l) with 0. lia.
               symmetry. cut (~In b l). eauto. intro H6. 
               assert (H7: lr a b). eauto.
               assert (H8: lr b a). 
               { (*---lr b a ---*)
                cut (In a (b::s)). eauto. eapply included_elim2. exact H3.
                }
               absurd (a=b). auto. apply Hanti. split_;auto. }
              { (*--- x<>b----*) 
                 specialize (H5 x) as Hx.
                 simpl in Hx. rewrite Hxa in Hx. rewrite Hxb in Hx. exact. } } } Qed.
              
                 
                   
   
   
  Lemma included_trans (l1 l2 l3: list A): 
  included l1 l2-> included l2 l3 -> included l1 l3.
  Proof. { intros H1 H2. 
          assert (H1a:forall a0 : A, (count a0 l1)<=(count a0 l2)).
          eapply included_elim. exact.
          assert (H2a:forall a0 : A, (count a0 l2)<=(count a0 l3)).
          eapply included_elim. exact.
          eapply included_intro. intros a.
          specialize (H1a a). specialize (H2a a). lia. } Qed.

   Hint Extern 0 (is_true ( included ?x ?z) ) =>
  match goal with
  | H: is_true (included x  ?y) |- _ => apply (@included_trans  x y z)
  | H: is_true (included ?y  z) |- _ => apply (@included_trans  x y z) 
  end : core.

 
  Hint Resolve included_intro1 included_intro2 included_intro3: core.
  Hint Resolve included_refl included_intro: core.
  Hint Resolve included_elim1 included_elim2 included_elim3: core.
  Hint Resolve included_elim4 (* included_elim4a *) included_elim5 included_elim: core.

  (* ----- Some Misc Lemmas on nodup, sorted, sublist, subset and included ---------------- *)

  Lemma nodup_subset_included (l s: list A): NoDup l -> l [<=] s -> included l s.
  Proof. { intros H1 H2. eapply included_intro. intro a. assert (H: In a l -> In a s). eauto. assert (H3: forall x, In x l -> count x l <=1). eauto.
  specialize (H3 a) as H4. assert (H5:In a s -> count a s >=1). eauto.
  assert (H6:(In a l)\/( ~In a l)). eauto. destruct H6. apply H in H0 as H7.
  apply H5 in H7. apply H4 in H0. lia. assert (H6: count a l =0).
  eauto. replace (count a l) with 0. lia. } Qed.
  
  Lemma count_delete_uniq (l: list A) (a: A): count a l <= 1 <-> ~In a (uniq (delete a l)).
  Proof. split. { intros. induction l. { simpl. auto. }
                    { simpl in H. simpl. 
                      destruct (a == a0) eqn: Haa0.
                      { intro. assert ((count a l) = 0). lia. assert(~In a l).
                        eauto. assert(In a l). apply uniq_intro_elim. auto. auto. }
                      { simpl. destruct (memb a0 (delete a l)) eqn: Ha0.
                        { auto. }
                        { intro. simpl in H0. destruct H0. 
                          move /eqP in Haa0. auto. apply IHl in H. auto. } }} }
               { intros. assert ((In a (delete a l))\/~(In a (delete a l))). 
                 { eauto. }
                 { destruct H0. eapply uniq_intro_elim in H0. destruct H. auto.
                   eauto. apply countP2 in H0 as H1. assert (In a l\/~In a l).
                   eauto. destruct H2. apply countP7 in H2 as H3. lia. 
                   assert (count a l = 0). eauto. lia. }} Qed.

  Lemma sublist_is_sorted (lr: A-> A-> bool)(l s: list A):  Sorted lr s -> sublist l s -> Sorted lr l. 
  Proof. { revert l.
           induction s as [|b s1].
           { intros l H1 H2. assert (H3:l=nil).
             eauto.  subst l. auto. }
           { intros l H1 H2.  
             destruct l as [|a l1].
             {  eapply Sorted_elim3. apply Sorted_single. Unshelve. exact. }
             { simpl in H2.
               destruct (a == b) eqn: Hab.
               { (*----a=b----*)
                 move /eqP in Hab. constructor. 
                 { apply IHs1. eauto. exact. }
                 { intros x H3. 
                   assert (H4: lr b x). 
                   { cut (In x s1). apply Sorted_elim4. exact.
                   assert (H5: l1 [<=] s1). auto. auto. }
                 subst a;auto. } }
               { (*---a<>b---*)
                 apply IHs1.  eauto. exact.  } } } } Qed.     
             
  
  
  Lemma sorted_included_sublist (l s: list A)(lr: A->A-> bool)(Hanti: antisymmetric lr):
    Sorted lr l-> Sorted lr s-> included l s-> sublist l s.
  Proof. { revert l.
           induction s as [|b s1]. 
           { intros l H1 H2 H3. destruct l;simpl in H3. simpl;auto.
            inversion H3. }
           { intros l H1 H2 H3. 
             destruct l as [|a l1] eqn: H4. 
             { simpl;auto. }
             { (*----sublist (a :: l1) (b :: s1)-----*)
               simpl. destruct (a==b) eqn: Hab. 
               { (*----- a = b --------*)
               apply IHs1. eauto. eauto. move /eqP in Hab. subst b.
               cut (forall x, count x l1 <= count x s1). eauto.
               intros x. 
               assert (H5: forall y, count y (a :: l1) <= count y (a :: s1)).            
               eapply included_elim. exact. specialize (H5 x) as H6. simpl in H6. 
               destruct (x == a);lia. }
               { (*------ a <> b--------*) 
                assert (H5: included (a::l1) s1). eapply included_elim6. 
                exact Hanti. auto. exact H2. exact H3. move /eqP in Hab.  exact.
                eapply IHs1. exact. eauto. exact. } } } } Qed.
  
  Lemma first_in_ordered_sublists (a e:A)(l s: list A)(lr: A->A-> bool)(Hrefl: reflexive lr):
    Sorted lr (a::l)-> Sorted lr (e::s)-> sublist (a::l)(e::s)-> lr e a.
  Proof. { intros H1 H2 H3. simpl in H3. destruct (a == e) eqn: H4.
         move /eqP in H4. subst a. auto.
         assert (H5: (forall x, In x l -> lr a x)). eapply Sorted_elim4. exact.
         assert (H6: (forall x, In x s -> lr e x)). eapply Sorted_elim4. exact.
         eauto. } Qed.

 Lemma nodup_included_nodup (l s: list A) :
 NoDup s -> included l s -> NoDup l.
 Proof. { intros. assert (H1:(forall a, count a l <= count a s)).
        apply included_elim. exact. apply count_nodup. intros.
        specialize (H1 x) as H3. assert (H4: count x s <=1).
        apply nodup_count. exact. eauto. lia. } Qed.
 
 Lemma subset_nodup_subset (a:A) (l s: list A) :
 l[<=]a::s-> NoDup l -> ~In a l -> l[<=]s.
 Proof. { intros. unfold Subset in H. unfold Subset. intros.
       specialize (H a0) as H3. apply H3 in H2 as H4. simpl in H4.
       destruct H4. subst a. absurd (In a0 l). exact. exact. exact. } Qed.
       
   Lemma subset_nodup_delete_subset (a:A) (l s: list A) :
    l[<=]s-> NoDup l -> NoDup s -> (delete a l) [<=] (delete a s).
    Proof. unfold "[<=]". intros. assert(In a0 l). eauto.
           apply H in H3. assert(a0=a\/a0<>a). eauto.
           destruct H4. subst a0. eauto. eauto. Qed.

       
  Hint Resolve nodup_subset_included: core.
  Hint Immediate sorted_included_sublist first_in_ordered_sublists
  nodup_included_nodup :core.
  

  (* --------------------  permuted lists (permutation) -------------------------------------*)

  Definition perm (l s: list A): bool:= included l s && included s l. 

  Lemma perm_intro  (l s: list A): (forall a, count a l = count a s)-> perm l s.
  Proof.  { intro H; split_; apply included_intro; intro a; specialize (H a); lia. } Qed.

  Lemma perm_intro0a (l: list A)(lr: A-> A-> bool): perm l (sort lr l).
  Proof. apply perm_intro. eauto. Qed.
  
  Lemma perm_intro0b (l: list A)(lr: A-> A-> bool): perm (sort lr l) l.
  Proof. apply perm_intro; eauto. Qed.
 
  Lemma perm_nil: perm nil nil.
  Proof. split_; eauto.  Qed.
  
  Lemma perm_refl (l: list A): perm l l.
  Proof. split_; eauto.  Qed.

  Lemma perm_intro3 (l s: list A): sublist l s -> sublist s l -> perm l s.
  Proof. intros; split_; eauto.  Qed.

  Lemma perm_elim   (l s: list A): perm l s -> (forall a, count a l = count a s).
  Proof.  { intros H a. move /andP in H. destruct H as [H1 H2].
          cut (count a l <= count a s). cut (count a s <= count a l). lia.
          all: eauto. } Qed.

  Lemma perm_elim1 (l: list A): perm l nil -> l = nil.
  Proof. intro H; move /andP in H; destruct H as [H1 H2]; eauto. Qed.
  Lemma perm_elim2 (l s: list A): perm l s -> l [=] s.
  Proof. move /andP;intro H; destruct H; split; eauto. Qed.
  Lemma perm_sym (l s: list A): perm l s -> perm s l.
  Proof. move /andP;intro H; apply /andP; tauto. Qed.

  Lemma perm_trans (x y z: list A): perm x y -> perm y z -> perm x z.
  Proof. intros H H1; move /andP in H; move /andP in H1; apply /andP.
         split;destruct H; destruct H1. all: auto. Qed.

  Hint Extern 0 (is_true ( perm ?x ?z) ) =>
  match goal with
  | H: is_true (perm x  ?y) |- _ => apply (@perm_trans x y z)
  | H: is_true (perm ?y  z) |- _ => apply (@perm_trans x y z) 
  end : core.

  Hint Resolve  perm_intro0a  perm_intro0b perm_refl perm_nil perm_elim1 : core.
  Hint Immediate perm_elim perm_intro perm_sym: core.
  
  Lemma perm_sort1 (l s: list A)(lr: A-> A-> bool): perm l s -> perm  l (sort lr s).
  Proof.  eauto. Qed.

   Lemma perm_sort2 (l s: list A)(lr: A-> A-> bool): perm l s -> perm  (sort lr l) s.
   Proof. eauto.  Qed.

   Lemma perm_sort3 (l s: list A)(lr: A-> A-> bool): perm l s -> perm (sort lr l)(sort lr s).
   Proof. eauto using perm_sort1. Qed.
   
   Lemma countP1a (l:list A) (x:A): count x l >=1 -> In x l.
   Proof. { induction l. simpl. intros H. lia. simpl.  intros H. 
          destruct (x == a) eqn: H1. left. move /eqP in H1. symmetry;exact.
          right. eapply IHl in H. exact. } Qed.
   
   Lemma perm_nodup (l s: list A): perm l s -> NoDup l -> NoDup s.
   Proof. { intros. apply count_nodup. intros.
          assert (H2: forall x, In x l -> count x l <= 1). 
          eauto. assert (H3: forall a, count a l = count a s).
          eauto. specialize (H2 x) as H4. specialize (H3 x) as H5.
          assert (H6: count x s >=1). eauto.
          assert (H7: count x l>=1). lia.  
          assert (H8:In x l). apply countP1a. exact. apply H4 in H8. lia. } Qed.

   Lemma perm_subset (l1 l2 s1 s2: list A): perm l1 l2 -> perm s1 s2 -> l1 [<=] s1 -> l2 [<=] s2.
   Proof. intros. unfold perm in H. unfold perm in H0. move /andP in H.
   move /andP in H0. destruct H. destruct H0. eapply included_elim5 in H2.
   eapply included_elim5 in H0. eauto. Qed.
   

   Lemma perm_elim3 (l s: list A)(a: A): perm l s -> perm (a::l) (a::s).
   Proof.  unfold perm. intros. move /andP in H. destruct H. apply /andP.
   split. eapply included_elim4b. exact. eapply included_elim4b. exact. Qed.
   
   
   

   Hint Resolve perm_sort1 perm_sort2 perm_sort3 perm_nodup perm_subset: core.
   
 End Permutation. 


  Hint Resolve uniform_subset: core.

  Hint Resolve count_in_putin1 count_in_putin2 count_in_sorted: core.


  Hint Resolve sublist_intro sublist_intro1 sublist_reflex sublist_Subset sublist_elim1 subset_nodup_delete_subset: core.
  Hint Resolve sublist_elim2 sublist_elim3 sublist_elim3a sublist_elim4 uniq_sublist: core.
(*
  Hint Extern 0 (is_true ( sublist ?x ?z) ) =>
  match goal with
  | H: is_true (sublist x  ?y) |- _ => apply (@sublist_trans _ x y z)
  | H: is_true (sublist ?y  z) |- _ => apply (@sublist_trans _ x y z) 
  end.

*)
  Hint Resolve included_intro1 included_intro2 included_intro3: core.
  Hint Resolve included_refl included_intro: core.
  Hint Resolve included_elim1 included_elim2  included_elim3: core.
  Hint Resolve included_elim4 (*included_elim4a*) included_elim5 included_elim: core.
  
  Hint Extern 0 (is_true ( included ?x ?z) ) =>
  match goal with
  | H: is_true (included x  ?y) |- _ => apply (@included_trans _ x y z)
  | H: is_true (included ?y  z) |- _ => apply (@included_trans _ x y z) 
  end : core.

  Hint Resolve nodup_subset_included: core.
  Hint Immediate sorted_included_sublist first_in_ordered_sublists
  nodup_included_nodup count_delete_uniq:core.
  Hint Resolve  perm_intro0a  perm_intro0b perm_refl perm_nil perm_elim1 : core.
  Hint Immediate perm_elim perm_intro perm_sym: core.
  Hint Resolve perm_elim1 perm_elim2 perm_elim3: core.

  Hint Extern 0 (is_true ( perm ?x ?z) ) =>
  match goal with
  | H: is_true (perm x  ?y) |- _ => apply (@perm_trans _ x y z)
  | H: is_true (perm ?y  z) |- _ => apply (@perm_trans _ x y z) 
  end : core.

  Hint Resolve perm_sort1 perm_sort2 perm_sort3 perm_nodup perm_subset: core.
