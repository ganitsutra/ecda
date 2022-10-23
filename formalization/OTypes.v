Require Export Coq.MSets.MSetInterface.
From Coq Require Import OrderedType.
Require Export MSetGenTree.
Require Export RBT.
Require Export Programs.
Require Export Definitions.
Require Export Properties.



Require Import Coq.Logic.Eqdep_dec Coq.Arith.Compare_dec Coq.Arith.PeanoNat.

Definition bcompetitive (b b':order):= (Nat.lt (oprice b') (oprice b)) \/
((Nat.eq (oprice b') (oprice b)) /\ (Nat.le (otime b) (otime b') )).

Definition acompetitive (a a':order):= (Nat.lt (oprice a) (oprice a')) \/
((Nat.eq (oprice a) (oprice a')) /\ (Nat.le (otime a) (otime a') )).

Definition eqcompetitive (a a':order):= ((Nat.eqb (oprice a) (oprice a')) /\ (Nat.eqb (otime a) (otime a') )).


Module OrderedA <: Orders.OrderedType.

Definition t := order.
Definition eq (x y: t) := eqcompetitive x y.

Definition lt (x y: t):= acompetitive y x/\~eqcompetitive x y.

 Lemma eq_refl : forall x : t, eq x x.
Proof. intros. unfold eq. unfold eqcompetitive. auto. Defined.

 Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. unfold eq. unfold eqcompetitive. intros. destruct H.
move /eqP in H.  move /eqP in H0. split. auto. auto.
Defined.

 Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. unfold eq. unfold eqcompetitive. intros. 
destruct H. move /eqP in H.  move /eqP in H1.
destruct H0. move /eqP in H0.  move /eqP in H2.
split. apply /eqP. lia. apply /eqP. lia. Defined.

Definition eq_equiv: Equivalence eq.
Proof. intros. constructor. unfold Reflexive. apply eq_refl.
unfold Symmetric. apply eq_sym. unfold Transitive. 
apply eq_trans.
Defined.

 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 unfold lt. unfold eq. intros. destruct H. auto. Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.  { unfold lt. unfold acompetitive. unfold eqcompetitive.
            intros.  destruct H0 as [H0 Hn1]. 
            destruct H as [H Hn2]. split.
         { destruct H0;destruct H. 
            { left.   lia.  }
            { destruct H. left. lia. }  
            { destruct H0. left. lia. }
            { destruct H0;destruct H. lia. } 
          }
          { intro. destruct H1. 
             move /eqP in H1.
             move /eqP in H2. 
             rewrite H1 in H. rewrite H1 in Hn2. 
             rewrite H2 in H. rewrite H2 in Hn2.
             destruct H0;destruct H. 
             { lia. }
             { destruct H. lia. }
             { destruct H0. lia. }
             { destruct H;destruct H0. destruct Hn1. 
                split. apply /eqP. lia. apply /eqP. lia. }
          } } Defined.
 
Definition lt_strorder: StrictOrder lt.
Proof. constructor. unfold Irreflexive. unfold Reflexive. unfold complement.
intros. apply lt_not_eq in H. destruct H. apply eq_refl.
unfold Transitive. apply lt_trans. Defined.

Definition lt_compat: Proper (eq ==> eq ==> iff) lt.
Proof. unfold Proper. intro. intros. intro. intros. unfold eq in H.
unfold eq in H0. unfold eqcompetitive in H.
unfold eqcompetitive in H0. unfold lt.
unfold acompetitive. unfold eqcompetitive.
destruct H;destruct H0. move /eqP in H.
move /eqP in H0. move /eqP in H1.
move /eqP in H2. rewrite H.
rewrite H0. rewrite H1. rewrite H2. split.
auto. auto. Defined.

 Definition compare (x y:t):= if (Nat.eqb (oprice x) (oprice y) &&(Nat.eqb (otime x) (otime y))) then Eq else (if (Nat.ltb (oprice y) (oprice x) || Nat.eqb (oprice x) (oprice y)&&(Nat.ltb (otime y) (otime x))) then Lt else Gt).

Definition compare_spec :
     forall x y : t,
     CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
 Proof. intros. unfold eq. unfold lt. unfold compare. 
          unfold eqcompetitive. unfold acompetitive.
     unfold Nat.lt. unfold Nat.eq. unfold Nat.le.  
     destruct ((oprice x =? oprice y) && (otime x =? otime y)) eqn:Heq.
     { constructor. move /andP in Heq. auto. }
     { destruct ((oprice y <? oprice x) || 
        (oprice x =? oprice y) && (otime y <? otime x)) eqn:Hlt.
        constructor. split. move /orP in Hlt. destruct Hlt.
        left. move /ltP in H. auto. right. move /andP in H.
        destruct H. split. move /eqP in H;lia. move /ltP in H0;lia.
        intro. move /andP in H.  move /eqP in H. rewrite Heq in H.
        move /eqP in H. inversion H. constructor.
        apply nat_tr in Heq. case ((oprice y <? oprice x)) eqn:Hp.
        simpl in Hlt. inversion Hlt. simpl in Hlt.
        case (oprice x =? oprice y) eqn:Hp2.
        simpl in Hlt. destruct Heq. move /eqP in Hp2. lia.
        move /eqP in Hp2. split. right. split. auto. move /ltP in Hlt. lia.
        intro. destruct H0. move /eqP in H1. lia. split.
        left. move /eqP in Hp2. move /ltP in Hp. lia.
        intro. destruct H. move /eqP in H.  move /eqP in Hp2. lia.
      } Qed. 


Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
intros. unfold eq. auto. destruct (eqP (oprice x) (oprice y));destruct (eqP (otime x) (otime y)). 
{ left. unfold eqcompetitive.
split. auto. auto. } 
{ right. unfold eqcompetitive. intro.
destruct H.  move /eqP in H0. auto. }
{ right. unfold eqcompetitive. intro.
destruct H.  move /eqP in H. auto. }
{ right. unfold eqcompetitive. intro.
destruct H.  move /eqP in H0. auto. } Qed.


End OrderedA.



Module Ordered_id <: Orders.OrderedType.

Definition t := order.

Definition eq (x y: t) := Nat.eq (id x) (id y).

Definition lt (x y: t):= Nat.lt (id x) (id y).


 Lemma eq_refl : forall x : t, eq x x.
 intros. unfold eq. unfold Nat.eq. auto. Qed.

 Lemma eq_sym : forall x y : t, eq x y -> eq y x.
unfold eq. intros. unfold Nat.eq. auto.
Qed.

 Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
 unfold eq. unfold Nat.eq. intros. lia. Qed.

Definition eq_equiv: Equivalence eq.
Proof. intros. constructor. unfold Reflexive. apply eq_refl.
unfold Symmetric. apply eq_sym. unfold Transitive. 
apply eq_trans.
Defined.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.  { unfold lt. unfold Nat.lt. intros. lia. } Qed.
          
 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 unfold lt. unfold eq. unfold Nat.lt. unfold Nat.eq. intros. lia. Qed.
 
Definition lt_strorder: StrictOrder lt.
Proof. constructor. unfold Irreflexive. unfold Reflexive. unfold complement.
intros. apply lt_not_eq in H. destruct H. apply eq_refl.
unfold Transitive. apply lt_trans. Defined.

Definition lt_compat: Proper (eq ==> eq ==> iff) lt.
Proof. unfold Proper. intro. intros. intro. intros. unfold eq in H.
unfold eq in H0. unfold Nat.eq in H.
unfold Nat.eq in H0. unfold lt.
unfold Nat.lt. lia. Defined.


 Definition compare (x y:t):= if (Nat.eqb (id x) (id y)) then Eq else
  (if (Nat.ltb (id x) (id y)) then Lt else Gt).

Definition compare_spec :
     forall x y : t,
     CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
     intros. unfold eq. unfold lt. unfold compare.
     unfold Nat.lt. unfold Nat.eq. destruct (id x =? id y) eqn:H.
     move /eqP in H. auto. move /eqP in H. 
     case (id x <? id y) eqn:H1. move /ltP in H1. auto.
     move /ltP in H1.  case ((id y <? id x)) eqn:H2.
     move /ltP in H2. auto. move /ltP in H2. lia. Defined.

 Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
 intros. unfold eq. unfold Nat.eq. apply Nat.eq_dec. Qed.

End Ordered_id.




Module OrderedB <: Orders.OrderedType.

Definition t := order.
Definition eq (x y: t) :=  eqcompetitive x y.

Definition lt (x y: t):= bcompetitive y x/\~eqcompetitive x y.


 Lemma eq_refl : forall x : t, eq x x.
Proof. intros. unfold eq. unfold eqcompetitive. auto. Defined.

 Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. unfold eq. unfold eqcompetitive. intros. destruct H.
move /eqP in H.  move /eqP in H0. split. auto. auto.
Defined.

 Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. unfold eq. unfold eqcompetitive. intros. 
destruct H. move /eqP in H.  move /eqP in H1.
destruct H0. move /eqP in H0.  move /eqP in H2.
split. apply /eqP. lia. apply /eqP. lia. Defined.

Definition eq_equiv: Equivalence eq.
Proof. intros. constructor. unfold Reflexive. apply eq_refl.
unfold Symmetric. apply eq_sym. unfold Transitive. 
apply eq_trans.
Defined.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.  { unfold lt. unfold bcompetitive. unfold eqcompetitive.
            intros.  destruct H0 as [H0 Hn1]. 
            destruct H as [H Hn2]. split.
         { destruct H0;destruct H. 
            { left.   lia.  }
            { destruct H. left. lia. }  
            { destruct H0. left. lia. }
            { destruct H0;destruct H. lia. } 
          }
          { intro. destruct H1. 
             move /eqP in H1.
             move /eqP in H2. 
             rewrite H1 in H. rewrite H1 in Hn2. 
             rewrite H2 in H. rewrite H2 in Hn2.
             destruct H0;destruct H. 
             { lia. }
             { destruct H. lia. }
             { destruct H0. lia. }
             { destruct H;destruct H0. destruct Hn1. 
                split. apply /eqP. lia. apply /eqP. lia. }
          } } Qed.
          
 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Proof. unfold lt. intros x y H. destruct H. unfold eq. auto. Qed.
 
Definition lt_strorder: StrictOrder lt.
Proof. constructor. unfold Irreflexive. unfold Reflexive. unfold complement.
intros x H. apply lt_not_eq in H. destruct H. apply eq_refl.
unfold Transitive. apply lt_trans. Qed.

Definition lt_compat: Proper (eq ==> eq ==> iff) lt.
Proof. unfold Proper. intro. intros. intro. intros. unfold eq in H.
unfold eq in H0. unfold eqcompetitive in H.
unfold eqcompetitive in H0. unfold lt.
unfold bcompetitive. unfold eqcompetitive.
destruct H;destruct H0. move /eqP in H.
move /eqP in H0. move /eqP in H1.
move /eqP in H2. rewrite H.
rewrite H0. rewrite H1. rewrite H2. split.
auto. auto. Defined.


 Definition compare (x y:t):= if (Nat.eqb (oprice x) (oprice y) &&(Nat.eqb (otime x) (otime y))) then Eq else (if (Nat.ltb (oprice x) (oprice y) || Nat.eqb (oprice x) (oprice y)&&(Nat.ltb (otime y) (otime x))) then Lt else Gt).

Definition compare_spec :
     forall x y : t,
     CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
 Proof. intros. unfold eq. unfold lt. unfold compare. 
          unfold eqcompetitive. unfold bcompetitive.
     unfold Nat.lt. unfold Nat.eq. unfold Nat.le.  
     destruct ((oprice x =? oprice y) && (otime x =? otime y)) eqn:Heq.
     { constructor. move /andP in Heq. auto. }
     { destruct ((oprice x <? oprice y) || 
        (oprice x =? oprice y) && (otime y <? otime x)) eqn:Hlt.
        constructor. split. move /orP in Hlt. destruct Hlt.
        left. move /ltP in H. auto. right. move /andP in H.
        destruct H. split. move /eqP in H;lia. move /leP in H0. move /eqP in H. lia.
        intro. move /andP in H.  move /eqP in H. rewrite Heq in H.
        move /eqP in H. inversion H. constructor.
        apply nat_tr in Heq. case ((oprice x <? oprice y)) eqn:Hp.
        simpl in Hlt. inversion Hlt. simpl in Hlt.
        case (oprice x =? oprice y) eqn:Hp2.
        simpl in Hlt. destruct Heq. move /eqP in Hp2. lia.
        move /eqP in Hp2. split. right. split. auto. move /ltP in Hlt. lia.
        intro. destruct H0. move /eqP in H1. lia. split.
        left. move /eqP in Hp2. move /ltP in Hp. lia.
        intro. destruct H. move /eqP in H.  move /eqP in Hp2. lia.
      } Qed. 


Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
intros. unfold eq. auto. destruct (eqP (oprice x) (oprice y));destruct (eqP (otime x) (otime y)). 
{ left. unfold eqcompetitive.
split. auto. auto. } 
{ right. unfold eqcompetitive. intro.
destruct H.  move /eqP in H0. auto. }
{ right. unfold eqcompetitive. intro.
destruct H.  move /eqP in H. auto. }
{ right. unfold eqcompetitive. intro.
destruct H.  move /eqP in H0. auto. } Qed.

End OrderedB.


