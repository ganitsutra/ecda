(* -----------------Description------------------------------------------------------

This file mainly contains definitions of Orders, Transaction, Qty, Bids, Asks, Matching, Cannonical form, Multiset relations and terms related to them. These data types are also attached with eqType (i.e, domain with decidable Equality).

----------------------------------------------------------------------------------- *)

Require Import ssreflect ssrbool.
Require Export NSS2021_lib.
Require Import Coq.Logic.Eqdep_dec Coq.Arith.Compare_dec Coq.Arith.PeanoNat.

Module BoolDecidableSet <: DecidableSet.
Definition U := bool.
Definition eq_dec := Bool.bool_dec.
End BoolDecidableSet.

Module BoolDecidableEqDepSet := DecidableEqDepSet BoolDecidableSet.  
Set Implicit Arguments.

Section some_nat.
Lemma not1 : Nat.eqb 1 0 = false.
Proof. apply /eqP. lia. Qed.

Lemma nat_tr (x0 x1 y0 y1:nat): (x0 =? x1) && (y0 =? y1) = false -> x0 <> x1 \/ y0 <> y1.
Proof. intro. assert (x0=x1\/x0<>x1). eauto. destruct H0. right.
subst x0. assert((x1 =? x1) = true).
apply /eqP. auto. rewrite H0 in  H. simpl in H.
apply PeanoNat.Nat.eqb_neq in H. exact. auto. Qed.

End some_nat.

Section Order.
Record order:Type:= Mk_order{
                        id: nat;
                        otime: nat;
                        oquantity: nat;
                        oprice: nat;
                        oquantity_cond: Nat.ltb oquantity 1 = false }.

Definition w0:={|id := 0;otime:=0;oquantity:=1;oprice:=0;oquantity_cond:=not1|}.

Definition ord_eqb (x y:order): bool:= (id x == id y)&& (otime x == otime y) &&(oquantity x == oquantity y) && ( oprice x == oprice y).

(*----------------  Attaching an Order to the EqType ----------------------------*)

Lemma ord_eqb_ref (x:order): ord_eqb x x = true.
Proof. unfold ord_eqb. split_. split_. split_. all:apply /eqP;auto.  Qed.

Lemma ord_eqb_elim (x y:order):  ord_eqb x y -> x = y.
Proof. { unfold ord_eqb. move /andP. intro H. destruct H as [H1 H2].
         move /andP in H1. destruct H1 as [H1 H3]. move /andP in H1. 
         destruct H1 as [H1 H4]. destruct x; destruct y. move /eqP 
         in H1. simpl in H1. simpl in H3. simpl in H2. simpl in H4.
         move /eqP in H2. move /eqP in H3. move /eqP in H4. subst. 
         f_equal. apply eq_proofs_unicity. eauto. } Qed.

Lemma ord_eqb_intro (x y:order): x=y -> ord_eqb x y = true.
Proof. { unfold ord_eqb. intros H. split_. split_. split_. 
         all:apply /eqP;subst x;auto. } Qed.  

Lemma ord_eqP (x y:order): reflect (x=y)(ord_eqb x y). 
Proof. apply reflect_intro. split. apply ord_eqb_intro. apply 
       ord_eqb_elim. Defined.

Canonical bid_eqType: eqType:= {| Decidable.E:= order; Decidable.eqb:= ord_eqb; Decidable.eqP:= ord_eqP |}.

End Order.

Section Orders_map.
(* ##########Definition: Ids of a list of orders ###########*)

Fixpoint ids (B:list order):(list nat):=
match B with
|nil => nil
|b::B' => (id b)::ids B'
end.

Lemma ids_intro (B:list order)(b :order): In b B -> In (id b) (ids B).
Proof. induction B. intros H. inversion H. intros H. destruct H. 
subst a. simpl;auto. simpl;right;auto. Qed.

Lemma ids_elim (B:list order)(i :nat): In i (ids B) -> 
exists b, (In b B)/\(id b = i).
Proof. induction B as [|a B IHB ]. intros H. inversion H. intros H. destruct H. 
exists a. auto. apply IHB in H. destruct H as [b H]. exists b. 
split. simpl;right;apply H. apply H. Qed.

Lemma ids_Subset  (B1 B2:list order):
Subset B1 B2 -> Subset (ids B1) (ids B2).
Proof. unfold Subset. intro. intros i H0. apply ids_elim in H0.
       destruct H0 as [b H0]. destruct H0. apply H in H0. apply 
       ids_intro in H0. subst i. auto. Qed.
 
Lemma nodup_ids_uniq_order (B:list order)(b1 b2 :order): 
NoDup (ids B) -> In b1 B ->In b2 B-> id b1 = id b2 -> b1 = b2.
Proof. revert b1 b2. induction B as [|b B0 IHB0]. simpl. intros b1 b2 H H0 H1 H2.
        inversion H1. intros. destruct H0;destruct H1. { subst.  auto. } { subst. apply 
        ids_intro in H1.  simpl in H. rewrite H2 in H. assert(~In (id b2) 
        (ids B0)). eauto. destruct (H0 H1). } { subst. apply ids_intro in H0.
        simpl in H. rewrite H2 in H0. assert(~In (id b2) (ids B0)). eauto.
        destruct (H1 H0). } { apply IHB0.  all: auto.  eauto. } Qed.

Lemma ndp_orders (B:list order) : NoDup (ids B) -> NoDup (ids (uniq B)).
Proof. induction B as [|a B IHB]. 
        simpl. auto. intros H. simpl. destruct(memb a B) eqn:HB.
       move /membP in HB. apply ids_intro in HB. simpl in H. assert(H0:~In (id a)
       (ids B)). eauto. destruct (H0 HB). simpl. constructor. move /membP in HB.
       intro. apply ids_elim in H0. destruct H0. destruct H0. apply uniq_intro_elim
       in H0. apply ids_intro in H0. rewrite H1 in H0. assert(~In (id a) (ids B)).
       eauto. destruct (H2 H0). apply IHB. eauto. Qed. 

Lemma count_in_deleted_ids (b: order)(B: list order):
  In b B -> count (id b) (ids B) = S (count (id b) (ids (delete b B))).
Proof. { induction B as [|a B IHB].
       { simpl. auto. }
       { intro h1. destruct h1 as [H | H]. 
         { subst a. simpl.  destruct ((id b) =? (id b)) eqn: h2.
           { destruct (ord_eqb b b) eqn:h2a.
             {  auto. }
             { move /eqP in h2a. destruct h2a. auto. }
           }
           { move /eqP in h2. destruct h2. auto. }
         }
         { simpl. destruct ( (id b) =? (id a)) eqn: h2.
           { destruct(ord_eqb b a) eqn:Ha.
             { auto. } 
             { simpl. rewrite h2.  apply IHB in H. lia. }
           }
           { simpl. destruct(ord_eqb b a) eqn:Ha.
              { move /eqP in Ha. subst b. move /eqP in h2. destruct h2. auto. }
              {  simpl. rewrite h2. apply IHB. auto. } 
           }
         }
      } 
      } Qed.

Lemma included_ids (B1 B2: list order): 
included B1 B2 -> included (ids B1) (ids B2).
Proof. { revert B2. induction B1 as [| b1 B1 IHB1].
       { simpl. auto. }
       { intros B2 h1.
         assert (h2: In b1 B2). eauto.
         assert (h3: included B1 (delete b1 B2)). eauto.
         assert (h3a: included (ids B1) (ids (delete b1 B2))).
         { auto. }
         assert(h4:count (id b1)(ids B2)= 
         S (count (id b1) (ids (delete b1 B2)))).
         { eauto using count_in_deleted_ids. }
         eapply included_intro.
         intro x.  simpl. destruct (x =? (id b1)) eqn: C1.
         { move /eqP in C1. subst x.
           rewrite h4.
           eapply included_elim in h3a  as h3b. instantiate (1 := id b1) in h3b.
           lia. }
         { assert (h3b: included B1 B2). eapply included_elim4; apply h1. 
           apply IHB1 in h3b as h3c. auto. } } } Qed.

Lemma ids_perm  (B1 B2:list order):
perm B1 B2 -> perm (ids B1) (ids B2).
Proof. unfold perm. intros. move /andP in H. destruct H as [H H0].
       apply included_ids in H0. 
       apply included_ids in H. apply /andP. auto.  Qed.

Lemma ids_uniq1 (B:list order)(i :nat): In i (ids (uniq B)) <-> In i (ids B).
Proof. split. intros H. induction B as [|a B IHB]. simpl  in H. inversion H. simpl in H.
       destruct (memb a B) eqn: H0. simpl. right. apply IHB. auto. simpl in H.
       destruct H as [H | H]. simpl. subst i. auto. simpl. right. apply IHB. auto.
       induction B. simpl. auto. simpl. intros H. 
       destruct H as [H | H]. subst. destruct (memb a B ) eqn:H0. apply IHB.
       move /membP in H0. apply ids_intro in H0. auto. simpl. auto.
       destruct (memb a B ) eqn:H0. apply IHB. auto. simpl. right.
        auto. Qed.

Lemma ids_delete_not_In (B:list order)(a a0:order):
In (id a0) (ids (delete a B)) -> In (id a0) (ids B).
Proof. induction B as [| a1 B IHB]. simpl. auto. simpl. destruct(ord_eqb a a1) eqn:Ha.
intros H. auto. simpl. move /eqP in Ha. subst. auto. simpl. intros H.
destruct H as [H | H]. auto. right. apply IHB. auto. Qed.

Lemma nodup_ids_delete (B:list order)(a :order):
NoDup (ids B) -> NoDup (ids (delete a B)).
Proof. induction B as [| a0 B IHB]. simpl. auto. simpl. destruct (ord_eqb a a0) eqn:Ha.
intros H. eauto. intros. simpl. constructor. assert(H0:~In (id a0) (ids B)).
eauto. intro H1. apply  ids_delete_not_In in H1. destruct (H0 H1). apply IHB.
eauto. Qed.  

Fixpoint timesof (Omega:list order) :(list nat):=
match Omega with
|nil => nil
|w::Omega' => (otime w)::timesof Omega'
end.

Lemma timesof_elim  (Omega:list order)(b:order):
In b Omega -> In (otime b) (timesof Omega).
Proof. induction Omega as [|a Omega IHOmega]. simpl.
intros H. inversion H. simpl. intros H. destruct H.
subst a. auto. right. apply IHOmega. auto. Qed.

Lemma timesof_intro  (Omega:list order)(i:nat):
In i (timesof Omega) -> exists b, In b Omega/\i=(otime b).
Proof. induction Omega as [|a Omega IHOmega]. simpl. intros H. inversion H. simpl. intros H. destruct H.
subst i. exists a. auto. apply IHOmega in H. destruct H as [x H]. exists x.
split. right. apply H. apply H. Qed.

Lemma count_in_deleted_timesof (b: order)(B: list order):
  In b B -> count (otime b) (timesof B) = S (count (otime b) (timesof (delete b B))).
Proof. { induction B as [| a B IHB].
       { simpl. auto. }
       { intro h1. destruct h1. 
         { subst a. simpl.  destruct (Nat.eqb (otime b) (otime b)) eqn: h2.
           { destruct (ord_eqb b b) eqn:h2a.
             {  auto. }
             { move /eqP in h2a. destruct h2a. auto. }
           }
           { move /eqP in h2. destruct h2. auto. }
         }
         { simpl. destruct (Nat.eqb (otime b) (otime a)) eqn: h2.
           { destruct(ord_eqb b a) eqn:Ha.
             { auto. } 
             { simpl. rewrite h2.  apply IHB in H. lia. }
           }
           { simpl. destruct(ord_eqb b a) eqn:Ha.
              { move /eqP in Ha. subst b. move /eqP in h2. destruct h2. auto. }
              {  simpl. rewrite h2. apply IHB. auto. } 
           }
         }
      } 
      } Qed.

Lemma included_timesof (B1 B2: list order): 
included B1 B2 -> included (timesof B1) (timesof B2).
Proof. { revert B2. induction B1 as [| b1 B1 IHB1].
       { simpl. auto. }
       { intros B2 h1.
         assert (h2: In b1 B2). eauto.
         assert (h3: included B1 (delete b1 B2)). eauto.
         assert (h3a: included (timesof B1) (timesof (delete b1 B2))).
         { auto. }
         assert(h4:count (otime b1)(timesof B2)= 
         S (count (otime b1) (timesof (delete b1 B2)))).
         { eauto using count_in_deleted_timesof. }
         eapply included_intro.
         intro x.  simpl. destruct (Nat.eqb x (otime b1)) eqn: C1.
         { move /eqP in C1. subst x.
           rewrite h4.
           eapply included_elim in h3a  as h3b. instantiate (1 := otime b1) in h3b.
           lia. }
         { assert (h3b: included B1 B2). eapply included_elim4; apply h1. 
           apply IHB1 in h3b as h3c. auto. } } } Qed.

Lemma timesof_perm  (B1 B2:list order):
perm B1 B2 -> perm (timesof B1) (timesof B2).
Proof. unfold perm. intros. move /andP in H. destruct H as [H H0].
       apply included_timesof in H0. 
       apply included_timesof in H. apply /andP. auto.  Qed.

Lemma timesof_Subset  (B1 B2:list order):
Subset B1 B2 -> Subset (timesof B1) (timesof B2).
Proof. unfold Subset. intro H. intros i H0. apply timesof_intro in H0.
       destruct H0 as [b H0]. destruct H0. apply H in H0.
       apply timesof_elim in H0. subst i. auto. Qed.

(*-------------price of a given id in list of orders-------------*)

(*Only used when In i (ids B)*)
Fixpoint price (B: list order)(i:nat):=
  match B with  
  |nil => 0
  |b::B' => if (id b) == i then oprice b else price B' i
end.

Lemma price_elim1 (B: list order) (b:order): In b B/\NoDup (ids B) -> price B (id b) = oprice b.
Proof. intros H. induction  B as [|a B IHB]. simpl in  H. inversion H. inversion H0.
simpl in H. destruct H as [H H0]. destruct H. subst. simpl. assert(id b =? id b = true).
apply /eqP. auto. rewrite H. auto. simpl. assert(H1:id a =? id b = false). apply /eqP.
assert(In (id b) (ids B)). apply ids_intro. auto. assert(H2:id a = id b\/id a <> id b).
eauto. destruct H2. rewrite H2 in H0. apply nodup_elim2 in H0. destruct (H0 H1). eauto. auto. rewrite H1. apply IHB. split. auto. eauto. Qed.

Lemma price_delete (B: list order) (b:order)(i:nat):
id b <> i -> price (delete b B) i = price B i.
Proof. revert b. induction B as [|a B IHB]. simpl. auto. simpl. intros b H. 
destruct(ord_eqb b a ) eqn:Ha. destruct (id a =? i) eqn:hi.
move /eqP in hi. subst i. move /eqP in Ha. destruct H. subst. auto.
auto. simpl. destruct (id a =? i) eqn:hi. auto. apply IHB. auto. Qed.

(*-------------timestamp of a given id in list of orders-------------*)

(*Only used when In i (ids B)*)
Fixpoint timestamp (B: list order)(i:nat):=
  match B with  
  |nil => 0
  |b::B' => if (id b) == i then otime b else timestamp B' i
end.

Lemma timestamp_elim1 (B: list order) (b:order): In b B/\NoDup (ids B) -> timestamp B (id b) = otime b.
Proof. intros H. induction B as [|a B IHB]. simpl in  H. inversion H. inversion H0.
simpl in H. destruct H. destruct H. subst. simpl. assert(id b =? id b = true).
apply /eqP. auto. rewrite H. auto. simpl. assert(H1:id a =? id b = false). apply /eqP.
assert(In (id b) (ids B)). apply ids_intro. auto. assert(H2:id a = id b\/id a <> id b).
eauto. destruct H2. rewrite H2 in H0. apply nodup_elim2 in H0. destruct (H0 H1). eauto. auto. rewrite H1. apply IHB. split. auto. eauto. Qed.

Lemma timestamp_delete (B: list order) (b:order)(i:nat):
id b <> i -> timestamp (delete b B) i = timestamp B i.
Proof. revert b. induction B as [|a B IHB]. simpl. auto. simpl. intros b H. 
destruct(ord_eqb b a ) eqn:Ha. destruct (id a =? i) eqn:hi.
move /eqP in hi. subst i. move /eqP in Ha. destruct H. subst. auto.
auto. simpl. destruct (id a =? i) eqn:hi. auto. apply IHB. auto. Qed.

(*-------------quantity of a given id in list of orders-------------*)
(*Only used when In i (ids B)*)
Fixpoint quant (B: list order)(i:nat):=
  match B with  
  |nil => 0
  |b::B' => if (id b) == i then oquantity b else quant B' i
end.

Lemma quant_elim (B: list order) (i:nat): ~In i (ids B) -> quant B i = 0. 
Proof. induction B as [|a B IHB]. simpl. auto. simpl. assert(H:~ In i ((id a) :: (ids B)) 
       -> ~ In i (ids B) /\ i <> (id a)). apply in_inv4. intro H0. apply H in 
       H0. destruct H0. destruct (id a =? i) eqn:H2. move /eqP in H2. subst i.
       destruct H1. auto. apply IHB. auto. Qed.  

Lemma quant_elim1 (B: list order) (b:order): In b B/\NoDup (ids B) -> 
      quant B (id b) = oquantity b.
Proof. intros H. induction  B as [|a B IHB]. 
       simpl in  H. inversion H. inversion H0. simpl in
       H. destruct H as [H H0]. destruct H. subst. simpl. assert(H:id b =? id b = true).
       apply /eqP. auto. rewrite H. auto. simpl. assert(H1:id a =? id b = false).
       apply /eqP. assert(H1:In (id b) (ids B)). apply ids_intro. auto. 
       assert(H2:id a = id b\/id a <> id b). eauto. destruct H2. rewrite H2 in H0.
       apply nodup_elim2 in H0. eauto. auto. rewrite H1. apply IHB. split. auto.
       eauto. Qed.

Lemma quant_uniq (B:list order)(i:nat): NoDup (ids B) -> quant B i = quant (uniq B) i.
Proof. induction B as [|a B IHB]. simpl. auto. simpl. intros H. 
destruct(id a =? i) eqn:H1.
{ destruct (memb a B) eqn:Ha.  move /eqP in H1. move /membP in Ha. assert(H0:In (id a) (ids B)).
  apply ids_intro. auto. apply nodup_elim2 in H.  destruct (H H0). simpl.
  rewrite H1. auto.
}
{ destruct (memb a B) eqn:Ha.  apply IHB. eauto. simpl. 
  rewrite H1. apply IHB. eauto.
} Qed.

(*-----------------Deleting an order with given id and it's properties--------------*)
(*Only used when NoDup (ids B)*)
Fixpoint delete_order (B: list order)(i:nat):(list order):=
  match B with  
  |nil => nil
  |b::B' => if (id b) == i then (delete_order B' i) else b::(delete_order B' i)
end.

Lemma delete_order_ids_elim (B: list order)(b: order):
      ~ In (id b) (ids (delete_order B (id b))). 
Proof. induction B as [|a B IHB]. 
       simpl. auto. intro H. simpl in H. destruct (id a =? id b)
       eqn:Ha. destruct (IHB H). simpl in H. destruct H. move /eqP in Ha. lia.
       destruct (IHB H). Qed.

Lemma delete_order_intro (B: list order)(b: order)(i : nat):
In b (delete_order B i) -> In b B.
Proof. induction B as [|a B IHB].  simpl. auto.  simpl. destruct (id a =? i).
auto. simpl. intros H. destruct H. left;auto. right;apply IHB;auto. Qed.

Lemma delete_order_ids_nodup (B: list order)(b: order):
NoDup (ids B) -> NoDup (ids (delete_order B (id b))).
Proof. induction B as [|a B IHB].  simpl. auto.  simpl. destruct (id a =? id b).
intros H.  apply IHB. eauto. 
intros H. simpl.  constructor.
intro H0. apply ids_elim in H0. destruct H0 as [x H0]. destruct H0 as [H0 H1].
apply delete_order_intro in H0. apply ids_intro in H0.
rewrite H1 in H0. assert(~In (id a) (ids B)). eauto.
destruct (H2 H0). apply IHB. eauto. Qed.

Lemma delete_order_timesof_nodup (B: list order)(b: order):
NoDup (timesof B) -> NoDup (timesof (delete_order B (id b))).
Proof. induction B as [|a B IHB].  simpl. auto.  simpl. destruct (id a =? id b).
intros H.  apply IHB. eauto. 
intros H. simpl. constructor.
intro H0. apply timesof_intro in H0. destruct H0 as [x H0]. destruct H0 as [H0 H1].
apply delete_order_intro in H0. apply timesof_elim in H0.
rewrite <- H1 in H0. assert(H2:~In (otime a) (timesof B)). eauto.
destruct (H2 H0). apply IHB. eauto. Qed.

Lemma delete_order_count_eq (B: list order)(b: order):
count b (delete_order B (id b)) = 0.
Proof. induction B as [|a B IHB].  simpl. auto.  simpl.
       destruct (id a =? id b) eqn:Hb. auto. simpl.
       destruct (ord_eqb b a) eqn:Hab. move /eqP in Hab. move /eqP in Hb.
       destruct Hb. subst b. auto. auto. Qed.
       
Lemma delete_order_count_neq (B: list order)(b: order)(i:nat):
i <> id b -> count b (delete_order B i) = count b B.
Proof. induction B as [|a B IHB]. 
        simpl. auto. intros H. simpl. destruct (id a =? i ) eqn:Ha.
       destruct (ord_eqb b a) eqn:Hba. move /eqP in Hba. move /eqP in Ha.
       subst a. lia. auto. 
       destruct (ord_eqb b a) eqn:Hba. simpl. rewrite Hba.
       move /eqP in Hba. apply IHB in H. lia. simpl. rewrite Hba.
       apply IHB. auto. Qed.

Lemma delete_order_count_nIn (B: list order)(b: order)(i:nat):
~ In b B -> count b (delete_order B i) = 0.
Proof. induction B as [|a B IHB]. simpl. auto. intros H. 
       apply in_inv4 in H. destruct H. 
       simpl. destruct (id a =? i ) eqn:Ha. eauto. simpl. destruct 
       (ord_eqb b a) eqn:Hba. move /eqP in Hba. subst b. destruct H0. 
       auto. move /eqP in Ha. apply IHB in H. auto. Qed.

Lemma delete_order_perm (B1 B2: list order)(i : nat):
perm B2 B1 -> perm (delete_order B2 i) (delete_order B1 i).
Proof. intros H. apply perm_intro. intros a. 
        assert(Hp1:= H). apply perm_elim with (a0:=a) in H.
       assert(H0:In a B2\/~In a B2). eauto. destruct H0.
       { assert(H1:In a B1). unfold perm in Hp1. 
         move /andP in Hp1. destruct Hp1. eauto.
         assert(H2:i = (id a) \/ i<> (id a)). eauto.
         destruct H2. subst i. rewrite delete_order_count_eq.
         rewrite delete_order_count_eq. auto.
         apply delete_order_count_neq with (B:=B1) in H2 as H5.
         apply delete_order_count_neq with (B:=B2) in H2 as H6.
         lia.
       }
       { assert(H1:~In a B1). unfold perm in Hp1. 
         move /andP in Hp1. destruct Hp1 as [H1 H2]. intro H3. 
         assert(H4:In a B2). eauto. destruct (H0 H4).
         apply delete_order_count_nIn with(i:=i) in H0.
         apply delete_order_count_nIn with(i:=i) in H1.
         lia.
       } Qed.

Lemma delete_order_included (B1 B2: list order)(i : nat):
included B1 (delete_order B2 i) -> included B1 B2.
Proof. intros H. apply included_intro. intros a. assert(Hp1:= H). 
       apply included_elim with (a0:=a) in H. assert(H0:count a 
       (delete_order B2 i) <= count a B2). assert(H0:i = 
       (id a) \/i<>(id a)). eauto. destruct H0. { subst i. rewrite
       delete_order_count_eq. lia. }
       { apply delete_order_count_neq with (B:= B2) in H0.
         lia. } lia. Qed.

Lemma timeprice_perm (B1 B2: list order)(i:nat):
perm B1 B2 -> NoDup (ids B1) -> NoDup (ids B2) ->
timestamp B1 i = timestamp B2 i /\ price B1 i = price B2 i.
Proof. revert B2. induction B1 as [|a B1 IHB1]. simpl. intros B2 H H0 H1. 
assert(H2:B2 = nil). eauto. subst B2. simpl. auto.
simpl. intros B2 H H0 H1. destruct(id a =? i) eqn:Hi. move /eqP in Hi.
subst i. rewrite <- timestamp_elim1 with (B:=B2).
rewrite <- price_elim1 with (B:=B2). auto. split.
unfold perm in H. move /andP in H. destruct H as [H H2]. eauto.
eauto. split. unfold perm in H. move /andP in H. destruct H as [H H2]. eauto.
eauto. assert(H2:perm B1 (delete a B2)). unfold perm in H. 
move /andP in H. destruct H as [H H2]. apply included_elim3a with (a0:=a) in H.
simpl in H. apply included_elim3a with (a0:=a) in H2.
simpl in H2. destruct (ord_eqb a a) eqn: Ha. unfold perm. 
apply /andP. auto. move /eqP in Ha. destruct Ha. auto.
apply IHB1 in H2. move /eqP in Hi. assert(H3:timestamp (delete a B2)
i = timestamp B2 i). apply timestamp_delete. auto. rewrite H3 in H2.
assert(H4:price (delete a B2) i = price B2 i). apply price_delete.
auto. rewrite H4 in H2. auto. eauto.  apply nodup_ids_delete. auto.
 Qed.

Lemma quant_perm (B1 B2: list order)(i:nat):
perm B1 B2 -> NoDup (ids B1) -> NoDup (ids B2) ->
quant B1 i = quant B2 i.
Proof. intros H H0 H1. assert(H2:In i (ids B1)\/~In i (ids B1)). eauto.
destruct H2. assert(H3:In i (ids B2)). apply ids_perm in H.
unfold perm in H. 
move /andP in H. destruct H as [H H3]. eauto. apply ids_elim in H2.
destruct H2 as [x H2]. destruct H2 as [H2 H4]. subst i. apply ids_elim in H3. 
destruct H3 as [x0 H3]. destruct H3 as [H3 H4]. 
rewrite quant_elim1. auto.
rewrite quant_elim1. split.  unfold perm in H. 
move /andP in H. destruct H as [H H5]. eauto. auto. auto.
assert(H3:~ In i (ids B2)). intro H3. destruct H2.
apply ids_perm in H. unfold perm in H. 
move /andP in H. destruct H as [H H2]. eauto.
apply quant_elim in H2. apply quant_elim in H3. lia. Qed.
 
End Orders_map.

(*Following section contains definition of transaction type and it's decidability*)

Section Transaction.
(* ------------definition of  transaction as record---------------------------- *)

Record transaction:Type:=  Mk_transaction {
                             idb: nat;
                             ida: nat;
                             tquantity: nat;
                             tquantity_cond: Nat.ltb tquantity 1 = false 
                              }. 

Definition t_eqb (x y: transaction): bool:= (idb x == idb y) && 
(ida x ==  ida y) &&  (tquantity x == tquantity y).

(*------------------ Attaching transaction to eqType ------------------------------ *)

Lemma t_eqb_ref (x: transaction): t_eqb x x = true.
Proof. unfold t_eqb. apply /andP. split. apply /andP. split. all: apply /eqP; auto. Qed.

Lemma t_eqb_elim (x y: transaction):  t_eqb x y -> x = y.
Proof. { unfold t_eqb. destruct x. destruct y. simpl. intros H. move /andP in H.
         destruct H as [H H0].
          move /andP in H. destruct H as [H H1]. move /eqP in H. move /eqP in H1.
         move /eqP in H0. subst. f_equal. rewrite (BoolDecidableEqDepSet.UIP _ _ 
         tquantity_cond0 tquantity_cond1).  auto. } Qed.

Lemma t_eqb_intro (x y: transaction): x=y -> t_eqb x y = true.
Proof. { unfold t_eqb. intros H. apply /andP. split. apply /andP. 
         split. apply /eqP. subst x. exact. apply /eqP. subst x. exact. apply /eqP. 
         subst x. exact. } Qed.  

Lemma t_eqP (x y: transaction): reflect (x=y)(t_eqb x y).
Proof. apply reflect_intro. split. apply t_eqb_intro. apply 
t_eqb_elim. Defined. 

Canonical transact_eqType: eqType:= {| Decidable.E:= transaction; Decidable.eqb:= t_eqb; Decidable.eqP:= t_eqP |}.

End Transaction.

Section BAM.
(*-----------Definition Blist Alist and Mlist and perm-notation-------------*)

Definition Blist (p: (list order)*(list order)*(list transaction)) := 
match p with (x, y,z) => x end.
Definition Alist (p: (list order)*(list order)*(list transaction)) := 
match p with (x, y,z) => y end.
Definition Mlist (p: (list order)*(list order)*(list transaction)) := 
match p with (x, y,z) => z end.

(*--------------------End:Definition Blist Alist and Mlist----------------*)
End BAM.

(*-------------------Some ltac used for routine task ------------------*)
Ltac setxy :=
  match goal with
    | [ |- context[?X::nil = ?Y::nil]] => set(x:=X); set(y:=Y)
    | [ |- ?X = ?Y ] => set(x:=X); set(y:=Y)
  end.
Ltac crushxyorder1 := match goal with
| [ x:= _, y:= _ |- ?P ?x = ?P ?y ] => subst x;subst y;simpl;lia
| [ Hxyi: _, Hxyp: _, Hxyt: _, Hxyq: _ |- ?x = ?y ] =>
        destruct x as [ix tx qx px blx], y as [iy ty qy py bly]; simpl in Hxyq;
        simpl in Hxyi; simpl in Hxyt; simpl in Hxyp;
        revert blx bly; rewrite Hxyi; rewrite Hxyq; rewrite Hxyp; rewrite Hxyt;
        intros; f_equal; rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto
end.

Ltac eq1 :=
match goal with |[ |- context[(if ?x =? ?x then _ else _)] ] => assert (x =? x = true) as Heq;apply /eqP;auto;rewrite Heq;auto end.

Ltac eq2 :=
match goal with |[ |- context[(if ?x =? ?y then _ else _)] ] => assert (x =? y = true) as Heq;apply /eqP;auto;rewrite Heq;auto end.

Ltac dlt1 := match goal with
| [ |- context[ match ?X with _ => _ end]  ]=> destruct X eqn:Hlt end.

Ltac ltq1:= match goal with
| [ m : transaction, H: ?X < 1 |- _] => destruct m eqn:Hm1;simpl in H;
      match goal with | [ H0: (?t <? 1) = false |- _] => assert(Hm2:=H0);
      move /ltP in Hm2;lia end end.

Ltac ltqo:= match goal with | [ a : order, H: ?X < 1 |- _] => 
           destruct a eqn:Hm1;simpl in H;  match goal with | 
           [ H0: (PeanoNat.Nat.ltb ?t 1 = false) |- _] => assert(Hm2:=H0);
           move /ltP in Hm2;lia end end.

Ltac ltqt:= match goal with
| [ m : transaction, H: ?X < 1 |- _] => destruct m eqn:Hm1;simpl in H;
      match goal with | [ H0: (PeanoNat.Nat.ltb ?t 1 = false) |- _] =>
      assert(Hm2:=H0); move /ltP in Hm2;lia end end.

(*------------------------------End of ltac--------------*)

Section Qty.
(*This section contains some functions about sum of quantities of list of transactions------------*)

Fixpoint Qty_bid (T: list transaction) (i:nat): (nat):=
  match T with
  |nil => 0
  |t::T' => if (idb t)==i then tquantity t + (Qty_bid T' i) else (Qty_bid T' i)
  end.

Lemma Qty_bid1 (T: list transaction)(t: transaction):
In t T -> Qty_bid T (idb t) >= tquantity t.
Proof. induction T as [|a T IHT]. simpl. intro H. inversion H.
simpl. destruct (idb a =? idb t) eqn: Ht. intros H. destruct H.
subst. lia. apply IHT in H. lia. intros H.
 destruct H. subst. move /eqP in Ht. destruct Ht. auto.
 auto. Qed. 

Lemma Qty_bid_elim (T: list transaction) (i:nat): 
Qty_bid T i >0 -> exists t, In t T/\(idb t = i).
Proof. induction T as [|a T IHT]. simpl. lia. simpl. intros H. 
       destruct (idb a =? i) eqn:Hi.
       exists a. split;auto. apply IHT in H. destruct H as [x H]. exists x.
       split. right;apply H. apply H. Qed.

Fixpoint Qty_ask (T: list transaction) (i:nat): (nat):=
  match T with
  |nil => 0
  |t::T' => if (ida t)==i then tquantity t + (Qty_ask T' i) else (Qty_ask T' i)
  end.

Lemma Qty_ask_elim (T: list transaction) (i:nat): 
Qty_ask T i >0 -> exists t, In t T/\(ida t = i).
Proof. induction T as [|a T IHT]. simpl. lia. simpl. intros H. 
       destruct (ida a =? i) eqn:Hi.
       exists a. split;auto. apply IHT in H. destruct H as [x H]. exists x.
       split. right;apply H. apply H. Qed.

Lemma Qty_ask1 (T: list transaction)(t: transaction):
In t T -> Qty_ask T (ida t) >= tquantity t.
Proof. induction T as [|a T IHT]. simpl. intro H. inversion H.
simpl. destruct (ida a =? ida t) eqn: Ht. intros H. destruct H.
subst. lia. apply IHT in H. lia. intros.
 destruct H. subst. move /eqP in Ht. destruct Ht. auto.
 auto. Qed. 
 

Fixpoint Qty (T: list transaction) (i1 i2:nat):(nat):=
  match T with
  |nil => 0
  |t::T' => if ((idb t)==i1) && ((ida t) == i2) then 
  tquantity t + (Qty T' i1 i2) else (Qty T' i1 i2)   end.

Lemma Qty_elim (T: list transaction) (i j:nat): 
Qty T i j >0 -> exists t, In t T/\(ida t = j)/\(idb t = i). 
Proof. induction T as [|a T IHT]. simpl. lia. simpl. intros H. 
       destruct ((idb a =? i) && (ida a =? j)) eqn:Hi. exists a. 
       move /andP in Hi. destruct Hi as [H0 H1].
       move /eqP in H0. move /eqP in H1. subst. auto. apply IHT in H. 
       destruct H as [x H]. exists x. split. right;apply H. apply H. Qed.

Lemma Qty_Qty_ask (T: list transaction)(b:order):
(forall t, In t T -> idb t = id b) -> 
(forall j, Qty_ask T j = Qty T (id b) j).
Proof. intros H j. induction T as [|a T IHT]. simpl. auto.
      simpl. destruct ((idb a =? id b)) eqn:Hi.
      simpl. destruct (ida a =? j) eqn: Hj.  cut(Qty_ask T j = Qty T (id b) j).
      lia. apply IHT. intros t H0. apply H. auto. 
      apply IHT. intros t0 H0. apply H. auto. simpl.
      destruct (ida a =? j) eqn: Hj. specialize (H a).
      move /eqP in Hi. replace (idb a) with (id b) in Hi.
      destruct Hi. auto. symmetry. apply H. auto. 
      apply IHT. intros t H0. apply H. auto. Qed.

Lemma Qty_Qty_bid (T: list transaction)(b:order):
(forall t, In t T -> ida t = id b) -> 
(forall j, Qty_bid T j = Qty T  j (id b)).
Proof. intros H j. induction T as [|a T IHT]. simpl. auto.
      simpl. destruct ((idb a =? j)) eqn:Hi.
      simpl. destruct (ida a =? (id b)) eqn: Hj. auto. 
      specialize (H a).
      move /eqP in Hj. assert(ida a = id b).
      apply H. auto. lia. destruct (ida a =? (id b)) eqn: Hj. 
      simpl. apply IHT. intros t H0. apply H. auto. simpl. 
      apply IHT. intros t H0. apply H. auto.  Qed.

Lemma Qty_ask_M1_M2 (M1 M2: list transaction)(w:order)(i j:nat):
(forall t : transaction, In t M1 -> idb t = id w) ->
(forall t : transaction, In t M2 -> idb t = id w ) ->
Qty M1 (id w) j = Qty M2 (id w) j -> Qty M1 i j = Qty M2 i j.
Proof. intros H H0 H1. assert(H2:Qty M1 i j = Qty M2 i j\/Qty M1 i j > Qty M2 i j\/Qty M1 i j < Qty M2 i j).
lia. destruct H2. auto. destruct H2. assert(H3:Qty M1 i j >0). lia. apply Qty_elim in H3. destruct H3 as [x H3]. destruct H3 as [H3 H4]. destruct H4 as [H4 H5]. apply H in H3. subst. rewrite H3. auto.
assert(H3:Qty M2 i j >0). lia. apply Qty_elim in H3.
destruct H3 as [x H3]. destruct H3 as [H3 H4]. destruct H4 as [H4 H5]. apply H0 in H3. subst. rewrite H3. auto. Qed.


Lemma Qty_ask_delete1 (M: list transaction)(m:transaction)(i:nat):
ida m <> i -> Qty_ask (delete m M) i = Qty_ask M i.
Proof. revert m. induction M as [|a M IHM]. simpl. auto. simpl. intros m H. 
destruct(t_eqb m a ) eqn:Ha. destruct (ida a =? i) eqn:hi.
move /eqP in hi. subst i. move /eqP in Ha. subst m.
 destruct H.  auto.
auto. simpl. 
destruct (ida a =? i) eqn:hi. auto. apply IHM. auto. Qed.

Lemma Qty_ask_delete2 (M: list transaction)(m:transaction):
In m M -> tquantity m + Qty_ask (delete m M) (ida m) = Qty_ask M (ida m).
Proof. revert m. induction M as [|a M IHM]. simpl. intros m H. inversion H.
intros m H. simpl in H. destruct H. subst a. simpl. 
destruct (t_eqb m m) eqn:Hm1. destruct (ida m =? ida m) eqn:Hm2.
auto. move /eqP in Hm2. destruct Hm2. auto. simpl.
destruct (ida m =? ida m) eqn:Hm2.
move /eqP in Hm1. destruct Hm1. auto. 
move /eqP in Hm1. destruct Hm1. auto. 
simpl. apply IHM in H. destruct (t_eqb m a) eqn:Ha.
destruct (ida a =? ida m) eqn:Ha1. auto.
move /eqP in Ha. move /eqP in Ha1. subst. auto.
move /eqP in Ha. move /eqP in Ha1. subst.  destruct Ha1.
auto. simpl. destruct (ida a =? ida m) eqn:Ha1. lia. auto. Qed.

Lemma perm_Qty_ask (M1 M2: list transaction)(i:nat):
perm M1 M2 -> Qty_ask M1 i = Qty_ask M2 i.
Proof. revert M2. induction M1 as [|a M1 IHM1]. simpl. intros M2 H. 
assert(M2=nil). eauto. subst. simpl. auto.
intros M2 H. simpl. destruct(ida a =? i) eqn:Hi. move /eqP in Hi.
subst. assert(H0:perm M1 (delete a M2)). unfold perm in H. 
move /andP in H. destruct H as [H H0]. apply included_elim3a with (a0:=a) in H.
simpl in H. apply included_elim3a with (a0:=a) in H0. 
simpl in H0. destruct (t_eqb a a) eqn: Ha. unfold perm. 
apply /andP. auto. move /eqP in Ha. destruct Ha. auto.
apply IHM1 in H0. rewrite H0. apply Qty_ask_delete2.
unfold perm in H. move /andP in H. destruct H as [H H1]. eauto.
assert(H0:perm M1 (delete a M2)). unfold perm in H. 
move /andP in H. destruct H as [H H0]. apply included_elim3a with (a0:=a) in H.
simpl in H. apply included_elim3a with (a0:=a) in H0. 
simpl in H0. destruct (t_eqb a a) eqn: Ha. unfold perm. 
apply /andP. auto. move /eqP in Ha. destruct Ha. auto.
apply IHM1 in H0. rewrite H0. move /eqP in Hi.
apply Qty_ask_delete1. auto. Qed.

Lemma Qty_bid_delete1 (M: list transaction)(m:transaction)(i:nat):
idb m <> i -> Qty_bid (delete m M) i = Qty_bid M i.
Proof. revert m. induction M as [|a M IHM]. simpl. auto. simpl. intros m H. 
destruct(t_eqb m a ) eqn:Ha. destruct (idb a =? i) eqn:hi.
move /eqP in hi. subst i. move /eqP in Ha. subst m.
 destruct H.  auto.
auto. simpl. 
destruct (idb a =? i) eqn:hi. auto. apply IHM. auto. Qed.

Lemma Qty_bid_delete2 (M: list transaction)(m:transaction):
In m M -> tquantity m + Qty_bid (delete m M) (idb m) = Qty_bid M (idb m).
Proof. revert m. induction M as [|a M IHM]. simpl. intros m H. inversion H.
intros. simpl in H. destruct H. subst a. simpl. 
destruct (t_eqb m m) eqn:Hm1. destruct (idb m =? idb m) eqn:Hm2.
auto. move /eqP in Hm2. destruct Hm2. auto. simpl.
destruct (idb m =? idb m) eqn:Hm2.
move /eqP in Hm1. destruct Hm1. auto. 
move /eqP in Hm1. destruct Hm1. auto. 
simpl. apply IHM in H. destruct (t_eqb m a) eqn:Ha.
destruct (idb a =? idb m) eqn:Ha1. auto.
move /eqP in Ha. move /eqP in Ha1. subst. auto.
move /eqP in Ha. move /eqP in Ha1. subst.  destruct Ha1.
auto. simpl. destruct (idb a =? idb m) eqn:Ha1. lia. auto. Qed.

Lemma perm_Qty_bid (M1 M2: list transaction)(i:nat):
perm M1 M2 -> Qty_bid M1 i = Qty_bid M2 i.
Proof. revert M2. induction M1 as [|a M1 IHM1]. simpl. intros M2 H. 
assert(M2=nil). eauto. subst. simpl. auto.
intros M2 H. simpl. destruct(idb a =? i) eqn:Hi. move /eqP in Hi.
subst. assert(H0:perm M1 (delete a M2)). unfold perm in H. 
move /andP in H. destruct H as [H H0]. apply included_elim3a with (a0:=a) in H.
simpl in H. apply included_elim3a with (a0:=a) in H0. 
simpl in H0. destruct (t_eqb a a) eqn: Ha. unfold perm. 
apply /andP. auto. move /eqP in Ha. destruct Ha. auto.
apply IHM1 in H0. rewrite H0. apply Qty_bid_delete2.
unfold perm in H. move /andP in H. destruct H as [H H1]. eauto.
assert(H0:perm M1 (delete a M2)). unfold perm in H. 
move /andP in H. destruct H as [H H0]. apply included_elim3a with (a0:=a) in H.
simpl in H. apply included_elim3a with (a0:=a) in H0. 
simpl in H0. destruct (t_eqb a a) eqn: Ha. unfold perm. 
apply /andP. auto. move /eqP in Ha. destruct Ha. auto.
apply IHM1 in H0. rewrite H0. move /eqP in Hi.
apply Qty_bid_delete1. auto. Qed.

Lemma Qty_bid_M1_M2 (M1 M2: list transaction)(w:order)(i j:nat):
(forall t : transaction, In t M1 -> ida t = id w) ->
(forall t : transaction, In t M2 -> ida t = id w ) ->
Qty M1 j (id w) = Qty M2 j (id w)-> Qty M1 j i= Qty M2 j i.
Proof. intros H H0 H1. assert(H2:Qty M1 j i= Qty M2 j i\/Qty M1 j i > 
       Qty M2 j i\/Qty M1 j i < Qty M2 j i). lia. destruct H2. auto. 
       destruct H2. assert(H3:Qty M1 j i >0). lia. apply Qty_elim in H3.
       destruct H3 as [x H3]. destruct H3 as [H3 H4]. 
       destruct H4 as [H4 H5]. apply H in H3. subst. 
       rewrite H3. auto. assert(H3:Qty M2 j i>0). lia. apply Qty_elim in H3.
       destruct H3 as [x H3]. destruct H3 as [H3 H4]. 
       destruct H4 as [H4 H5]. apply H0 in H3. subst. 
       rewrite H3. auto. Qed.

Fixpoint Vol (T: list transaction):(nat):=
  match T with
  |nil => 0
  |t::T' => tquantity t + (Vol T')
  end.

Lemma Q_vs_Qty_bid (T: list transaction) (i:nat): Vol T >= Qty_bid T i.
Proof. induction T as [|a T IHT]. simpl. lia. simpl. destruct (idb a =? i). lia. lia. Qed.

Lemma Q_vs_Qty_ask (T: list transaction) (i:nat): Vol T >= Qty_ask T i.
Proof. induction T as [|a T IHT]. simpl. lia. simpl. destruct (ida a =? i). lia. lia. Qed.

Fixpoint ids_bid_aux (T: list transaction):(list nat):=
  match T with  
  |nil => nil
  |t1::T' => (idb t1)::(ids_bid_aux T')
end.

Lemma ids_bid_intro0 (T: list transaction) (i:nat) :
In i (ids_bid_aux T) -> Qty_bid T i>0.
Proof. intros H. induction T as [|a T IHT]. 
        simpl in H. inversion H. simpl. simpl in H. 
       destruct H. subst i. assert (H:idb a =? idb a = true). apply /eqP. 
       auto. destruct a. simpl in IHT. simpl in H. simpl. assert 
       (H0:idb0 =? idb0 = true). apply /eqP. auto. rewrite H. move 
       /ltP in tquantity_cond0. lia. apply IHT in H. destruct 
       (idb a =? i). lia. lia. Qed.

Lemma ids_bid_aux_intro1 (T: list transaction) (i:nat) :
In i (ids_bid_aux T) -> exists t, In t T/\(idb t = i).
Proof. intros H. induction T as [|a T IHT]. simpl in H. inversion H.
simpl. simpl in H. destruct H. exists a. split. auto. auto.
apply IHT in H. destruct H as [x H]. destruct H as [H H0].
exists x. split. auto. auto. Qed.

Lemma Qty_bid_t_zero (T: list transaction) (i:nat) :
~ In (i) (ids_bid_aux T) ->
Qty_bid T (i) = 0.
Proof. induction T as [|t T']. simpl.  auto.
       simpl. intros. apply in_inv4 in H. destruct H.
       destruct (idb t =? i) eqn:Hi.  move /eqP in Hi.
       subst i. destruct H0. auto. apply IHT'. auto. Qed.

End Qty.

Definition ids_bid (I:list nat)(T:list transaction):= 
(forall i, In i I ->(exists t, (In t T)/\(idb t = i)))
/\(forall t, In t T -> (exists i, (In i I)/\(idb t = i))) /\(NoDup I).

Definition fun_ids_bid (T:list transaction) := (uniq (ids_bid_aux T)).

Lemma ids_bid_correct (T:list transaction): ids_bid (fun_ids_bid T) T.
Proof. unfold ids_bid. split. 
      { intros. induction T as [| t T']. simpl in H. inversion H.
        apply uniq_intro_elim in H. simpl in H. destruct H.  exists t.
        split.  auto.  auto.  apply uniq_intro_elim in H. apply IHT' in H.
        destruct H as [ x H]. exists x. destruct H. split. eauto. auto. 
      } split.
      { intros. induction T as [|t0 T']. inversion H. destruct H.
        subst. exists (idb t). split. unfold fun_ids_bid. 
        cut(In (idb t) ((ids_bid_aux (t :: T')))). apply uniq_intro_elim.
        simpl. auto. auto. apply IHT' in H. destruct H as [i H0]. exists i.
        split. unfold fun_ids_bid. cut(In i ((ids_bid_aux (t0 :: T')))). 
        apply uniq_intro_elim. simpl. right. apply uniq_intro_elim. apply H0.
        apply H0.
      }
      { apply uniq_NoDup. } Qed.  


Lemma ids_bid_intro1 (T: list transaction) (t: transaction): In t T -> In (idb t) (fun_ids_bid T).
Proof. intros. assert(ids_bid (fun_ids_bid T) T). apply ids_bid_correct.
       destruct H0. apply H1 in H. destruct H. destruct H. subst. auto. Qed.

(***Start: Bellow is for ids_ask which is mirror image of above part*****)
Definition ids_ask (I:list nat)(T:list transaction):= 
           (forall i, In i I -> (exists t, (In t T)/\(ida t = i)))/\
           (forall t, In t T -> (exists i, (In i I)/\(ida t = i))) /\(NoDup I).

Fixpoint ids_ask_aux (T: list transaction):(list nat):=
  match T with  
  |nil => nil
  |t1::T' => (ida t1)::(ids_ask_aux T')
  end.

Lemma ids_ask_intro0 (T: list transaction) (i:nat) :
In i (ids_ask_aux T) -> Qty_ask T i>0.
Proof. intros. induction T. simpl in H. inversion H.
simpl. simpl in H. destruct H.
subst i. assert (ida a =? ida a = true). apply /eqP. auto.
destruct a. simpl in IHT. simpl in H. simpl.
 assert (ida0 =? ida0 = true).
apply /eqP. auto. rewrite H. 
move /ltP in tquantity_cond0. lia. apply IHT in H. 
destruct (ida a =? i). lia. lia. Qed.

Lemma ids_ask_aux_intro1 (T: list transaction) (i:nat) :
In i (ids_ask_aux T) -> exists t, In t T/\(ida t = i).
Proof. intros. induction T. simpl in H. inversion H.
simpl. simpl in H. destruct H. exists a. split. auto. auto.
apply IHT in H. destruct H. destruct H.
exists x. split. auto. auto. Qed.

Lemma Qty_ask_t_zero (T: list transaction) (i:nat) :
~ In (i) (ids_ask_aux T) ->
Qty_ask T (i) = 0.
Proof. induction T as [|t T']. simpl.  auto.
       simpl. intros. apply in_inv4 in H. destruct H.
       destruct (ida t =? i) eqn:Hi.  move /eqP in Hi.
       subst i. destruct H0. auto. apply IHT'. auto. Qed.

Definition fun_ids_ask (T:list transaction) := (uniq (ids_ask_aux T)).

Lemma ids_ask_correct (T:list transaction): ids_ask (fun_ids_ask T) T.
Proof. unfold ids_ask. split. 
      { intros. induction T as [| t T']. simpl in H. inversion H.
        apply uniq_intro_elim in H. simpl in H. destruct H.  exists t.
        split.  auto.  auto.  apply uniq_intro_elim in H. apply IHT' in H.
        destruct H as [x H]. exists x. destruct H. split. eauto. auto. 
      } split.
      { intros. induction T as [|t0 T']. inversion H. destruct H.
        subst. exists (ida t). split. unfold fun_ids_ask. 
        cut(In (ida t) ((ids_ask_aux (t :: T')))). apply uniq_intro_elim.
        simpl. auto. auto. apply IHT' in H. destruct H as [i H0]. exists i.
        split. unfold fun_ids_ask. cut(In i ((ids_ask_aux (t0 :: T')))). 
        apply uniq_intro_elim. simpl. right. apply uniq_intro_elim. apply H0.
        apply H0.
      }
      { apply uniq_NoDup. } Qed.  

Lemma ids_ask_intro1 (T: list transaction) (t: transaction): In t T -> In (ida t) (fun_ids_ask T).
Proof. intros. assert(ids_ask (fun_ids_ask T) T). apply ids_ask_correct.
       destruct H0. apply H1 in H. destruct H. destruct H. subst. auto. Qed.

Section Qty_asks.

Fixpoint Q_by_asks_aux (T: list transaction) (I:list nat):nat:=
match I with
|nil => 0
|i::I' => (Qty_ask T i) + (Q_by_asks_aux T I')
end.

Lemma Q_by_asks_aux_T1_T2 (T1 T2: list transaction) (I:list nat):
Q_by_asks_aux T1 I > Q_by_asks_aux T2 I-> 
exists i, In i I/\ (Qty_ask T1 i) >(Qty_ask T2 i).
Proof.  revert T1 T2. induction I as [|i I']. simpl. intros T1 T2 H0. lia.
        intros T1 T2 H1. simpl in H1. simpl. 
        assert(Qty_ask T1 i > Qty_ask T2 i\/Qty_ask T1 i <= Qty_ask T2 i). lia.
        destruct H. exists i. split. auto. auto.
        assert(Q_by_asks_aux T1 I' >  Q_by_asks_aux T2 I'). lia. apply IHI' in H0.
        destruct H0. exists x. destruct H0. split. auto. auto. Qed.

Lemma Q_by_asks_aux_T_t0 (T: list transaction) (I:list nat)(t:transaction):
      ~In (ida t) I -> Q_by_asks_aux T I = Q_by_asks_aux (t :: T) I.
      Proof.  revert T t. induction I as [|i I']. simpl. auto.
               intros T t H. simpl. destruct (ida t =? i) eqn: Hi.
               destruct H. simpl. left. move /eqP in Hi;auto.
               apply in_inv4 in H. destruct H. apply IHI' with (T:=T) in H.
               lia. Qed.

 Lemma Q_by_asks_aux_T_t (T: list transaction) (I:list nat)(t:transaction): 
NoDup I-> In (ida t) I -> tquantity t +  Q_by_asks_aux T I = Q_by_asks_aux (t :: T) I.
 Proof. revert T t. induction I as [|i I']. intros T t ND H. inversion H.
       intros T t ND H. simpl. destruct H.
       assert (ida t =? i) as Hi. apply /eqP. auto.
       rewrite Hi. assert(~In i I'). eauto. 
       cut(Q_by_asks_aux T I' = Q_by_asks_aux (t :: T) I'). lia.
       apply Q_by_asks_aux_T_t0. subst i;auto. destruct (ida t =? i) eqn:Hi.
       move /eqP in Hi. subst i. assert(~In (ida t) I'). eauto.
       eauto. apply IHI' with (T:=T) in H. lia. eauto. Qed.

Lemma Q_by_asks_aux_T (T: list transaction) (I:list nat)(t:transaction):
subset I (ids_ask_aux T) -> ~In (ida t) (ids_ask_aux T)-> Q_by_asks_aux T I = Qty_ask T (ida t) + Q_by_asks_aux (t :: T) I.
Proof. revert T t. induction I as [|i I']. intros T t H H0. simpl.
       apply Qty_ask_t_zero in H0. lia. intros T t H H0. simpl. simpl in H. move /andP in H.
       destruct H. move /membP in H.  destruct (ida t =? i) eqn: Hi.
       move /eqP in Hi. subst i. eauto.
       apply IHI' with (T:=T) in H0 as H2. lia. auto. Qed.

Lemma  Q_by_asks_aux_T_i_In_I (T: list transaction) (I:list nat)(i:nat):
In i I -> Q_by_asks_aux T I = Q_by_asks_aux T (delete i I) + Qty_ask T i.
Proof.  revert T i. induction I as [|i I']. intros T i H. simpl in H. inversion H.
        simpl. intros. destruct H. assert(i0 =? i = true). apply /eqP. auto.
        rewrite H0. subst i. lia. destruct (i0 =? i) eqn:Hi. move /eqP in Hi.
        subst i. lia. simpl. cut (Q_by_asks_aux T I' = Q_by_asks_aux T (delete i0 I') + Qty_ask T i0).
        lia. apply IHI'. auto. Qed.

Definition Q_by_asks (T: list transaction) := Q_by_asks_aux T (fun_ids_ask T).

Lemma Q_Qty_ask (T: list transaction) : (Vol T) = (Q_by_asks T).
Proof. unfold Q_by_asks. unfold fun_ids_ask. induction T as [|t T']. simpl. auto.
       simpl. destruct (memb (ida t) (ids_ask_aux T')) eqn: H1.
       { 
       move /membP in H1. apply uniq_intro_elim in H1.
       apply Q_by_asks_aux_T_t with (T:=T') in H1. lia. eauto. }
       { simpl.   
       match goal with |[ |- context [if ?x =? ?y then _ else _] ] => assert(x =? y = true) as H;
       apply /eqP;auto;rewrite
        H; apply /eqP end.
       cut(Vol T' = Qty_ask T' (ida t) + Q_by_asks_aux (t :: T') (uniq (ids_ask_aux T'))).
       
       lia. rewrite IHT'. apply Q_by_asks_aux_T. 
       assert(sublist (uniq (ids_ask_aux T')) (ids_ask_aux T')). 
       eauto. apply sublist_Subset in H0. auto. move /membP in H1. auto. }
       Qed.

Lemma Q_by_asks_aux_subset_I1_I2 (T1 : list transaction) (I1 I2:list nat):
NoDup I1 -> NoDup I2 ->
Subset I1 I2 -> Q_by_asks_aux T1 I2 >= Q_by_asks_aux T1 I1.
Proof. revert T1 I1. induction I2. simpl. intros. assert(I1 = nil).
       eauto. subst. simpl. auto.
       intros. assert(In a I1\/~In a I1). eauto. destruct H2.
       replace (Q_by_asks_aux T1 I1) with (Qty_ask T1 a + Q_by_asks_aux T1 (delete a I1)).
       simpl. cut(Q_by_asks_aux T1 I2 >=Q_by_asks_aux T1 (delete a I1)).  lia.
       apply IHI2. eauto. eauto. cut(delete a I1 [<=] delete a (a::I2)). simpl.
       assert(a =? a = true). apply /eqP. auto. rewrite H3. auto. eauto.
       apply Q_by_asks_aux_T_i_In_I with (i:=a)(T:=T1) in H2. lia. 
       assert(I1 [<=] I2). eauto. eapply IHI2 with (T1:=T1) in H3. simpl. lia.
       eauto. eauto. Qed.

End Qty_asks.

Section Qty_bids.

Fixpoint Q_by_bids_aux (T: list transaction) (I:list nat):nat:=
match I with
|nil => 0
|i::I' => (Qty_bid T i) + (Q_by_bids_aux T I')
end.

Lemma Q_by_bids_aux_T1_T2 (T1 T2: list transaction) (I:list nat):
Q_by_bids_aux T1 I > Q_by_bids_aux T2 I-> 
exists i, In i I/\ (Qty_bid T1 i) >(Qty_bid T2 i).
Proof.  revert T1 T2. induction I as [|i I']. simpl. intros T1 T2 H0. lia.
        intros T1 T2 H1. simpl in H1. simpl. 
        assert(Qty_bid T1 i > Qty_bid T2 i\/Qty_bid T1 i <= Qty_bid T2 i). lia.
        destruct H. exists i. split. auto. auto.
        assert(Q_by_bids_aux T1 I' >  Q_by_bids_aux T2 I'). lia. apply IHI' in H0.
        destruct H0. exists x. destruct H0. split. auto. auto. Qed.

Lemma Q_by_bids_aux_T_t0 (T: list transaction) (I:list nat)(t:transaction):
      ~In (idb t) I -> Q_by_bids_aux T I = Q_by_bids_aux (t :: T) I.
      Proof.  revert T t. induction I as [|i I']. simpl. auto.
               intros T t H. simpl. destruct (idb t =? i) eqn: Hi.
               destruct H. simpl. left. move /eqP in Hi;auto.
               apply in_inv4 in H. destruct H. apply IHI' with (T:=T) in H.
               lia. Qed.

 Lemma Q_by_bids_aux_T_t (T: list transaction) (I:list nat)(t:transaction): 
NoDup I-> In (idb t) I -> tquantity t +  Q_by_bids_aux T I = Q_by_bids_aux (t :: T) I.
 Proof. revert T t. induction I as [|i I']. intros T t ND H. inversion H.
       intros T t ND H. simpl. destruct H.
       assert (idb t =? i) as Hi. apply /eqP. auto.
       rewrite Hi. assert(~In i I'). eauto. 
       cut(Q_by_bids_aux T I' = Q_by_bids_aux (t :: T) I'). lia.
       apply Q_by_bids_aux_T_t0. subst i;auto. destruct (idb t =? i) eqn:Hi.
       move /eqP in Hi. subst i. assert(~In (idb t) I'). eauto.
       eauto. apply IHI' with (T:=T) in H. lia. eauto. Qed.

Lemma Q_by_bids_aux_T (T: list transaction) (I:list nat)(t:transaction):
subset I (ids_bid_aux T) -> ~In (idb t) (ids_bid_aux T)-> Q_by_bids_aux T I = Qty_bid T (idb t) + Q_by_bids_aux (t :: T) I.
Proof. revert T t. induction I as [|i I']. intros T t H H0. simpl.
       apply Qty_bid_t_zero in H0. lia. intros T t H H0. simpl. simpl in H. move /andP in H.
       destruct H. move /membP in H.  destruct (idb t =? i) eqn: Hi.
       move /eqP in Hi. subst i. eauto.
       apply IHI' with (T:=T) in H0 as H2. lia. auto. Qed.

Lemma  Q_by_bids_aux_T_i_In_I (T: list transaction) (I:list nat)(i:nat):
In i I -> Q_by_bids_aux T I = Q_by_bids_aux T (delete i I) + Qty_bid T i.
Proof.  revert T i. induction I as [|i I']. intros T i H. simpl in H. inversion H.
        simpl. intros. destruct H. assert(i0 =? i = true). apply /eqP. auto.
        rewrite H0. subst i. lia. destruct (i0 =? i) eqn:Hi. move /eqP in Hi.
        subst i. lia. simpl. cut (Q_by_bids_aux T I' = Q_by_bids_aux T (delete i0 I') + Qty_bid T i0).
        lia. apply IHI'. auto. Qed.

Definition Q_by_bids (T: list transaction) := Q_by_bids_aux T (fun_ids_bid T).

Lemma Q_Qty_bid (T: list transaction) : (Vol T) = (Q_by_bids T).
Proof. unfold Q_by_bids. unfold fun_ids_bid. induction T as [|t T']. simpl. auto.
       simpl. destruct (memb (idb t) (ids_bid_aux T')) eqn: H1.
       { 
       move /membP in H1. apply uniq_intro_elim in H1.
       apply Q_by_bids_aux_T_t with (T:=T') in H1. lia. eauto. }
       { simpl.   
       match goal with |[ |- context [if ?x =? ?y then _ else _] ] => assert(x =? y = true) as H;
       apply /eqP;auto;rewrite
        H; apply /eqP end.
       cut(Vol T' = Qty_bid T' (idb t) + Q_by_bids_aux (t :: T') (uniq (ids_bid_aux T'))).
       lia. rewrite IHT'. apply Q_by_bids_aux_T. 
       assert(sublist (uniq (ids_bid_aux T')) (ids_bid_aux T')). 
       eauto. apply sublist_Subset in H0. auto. move /membP in H1. auto. }
       Qed.

Lemma Q_by_bids_aux_subset_I1_I2 (T1 : list transaction) (I1 I2:list nat):
NoDup I1 -> NoDup I2 ->
Subset I1 I2 -> Q_by_bids_aux T1 I2 >= Q_by_bids_aux T1 I1.

Proof. revert T1 I1. induction I2. simpl. intros. assert(I1 = nil).
       eauto. subst. simpl. auto.
       intros. assert(In a I1\/~In a I1). eauto. destruct H2.
       replace (Q_by_bids_aux T1 I1) with (Qty_bid T1 a + Q_by_bids_aux T1 (delete a I1)).
       simpl. cut(Q_by_bids_aux T1 I2 >=Q_by_bids_aux T1 (delete a I1)).  lia.
       apply IHI2. eauto. eauto. cut(delete a I1 [<=] delete a (a::I2)). simpl.
       assert(a =? a = true). apply /eqP. auto. rewrite H3. auto. eauto.
       apply Q_by_bids_aux_T_i_In_I with (i:=a)(T:=T1) in H2. lia. 
       assert(I1 [<=] I2). eauto. eapply IHI2 with (T1:=T1) in H3. simpl. lia.
       eauto. eauto. Qed.
End Qty_bids.

Section Bids.
(*  B = Bids(T, B') *)
Definition Bids (B:list order)(T: list transaction)(B': list order):=
subset (ids_bid_aux T) (ids B') -> (forall b, In b B -> (exists t, (In t T)/\(idb t = id b)/\(oquantity b = Qty_bid T (id b))/\
(exists b', (In b' B')/\(id b = id b')/\(otime b = otime b')/\(oprice b = oprice b'))))
/\(subset (ids_bid_aux T) (ids B))/\(NoDup B).

Fixpoint bids_aux (T: list transaction)(B:list order)(Bi :list nat):(list order).
refine ( match Bi with
    |nil => nil
    |i::Bi' => match (Compare_dec.lt_dec (Qty_bid T i) 1) with
        |left _ => bids_aux T B Bi'
        |right _ => (Mk_order i (timestamp B i) (Qty_bid T i ) (price B i) _ ):: (bids_aux T B Bi')
 end
 end). rewrite PeanoNat.Nat.ltb_nlt. auto.
 Defined.


Lemma In_ids_bids_in_Bi (T: list transaction)(B:list order)(Bi :list nat)(j:nat):
In j (ids (bids_aux T B Bi)) -> In j Bi.
Proof. revert T B j. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B b H. simpl in H.  destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr.
  simpl. right. 
  apply IHBi' in H. auto. simpl in H. destruct H. simpl. left. auto.
  apply IHBi' in H. auto. }
Qed.

Lemma In_ids_bids_in_ida_T (T: list transaction)(B:list order)(Bi :list nat)(j:nat):
In j (ids (bids_aux T B Bi)) -> In j (ids_bid_aux T).
Proof. revert T B j. induction Bi as [|i Bi']. 
{ intros T B b H. simpl in H. inversion H. }
{ intros T B b H. simpl in H. destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr.
  apply IHBi' in H. auto. simpl in H. destruct H. 
  assert(In b (ids_bid_aux T)\/~In b (ids_bid_aux T)). eauto.
  destruct H0. auto. apply Qty_bid_t_zero in H0. subst i. lia.
  apply IHBi' in H. auto. }
Qed.

Lemma In_b_bids_in_idb_Bi (T: list transaction)(B:list order)(Bi :list nat)(b:order):
In b (bids_aux T B Bi) -> In (id b) Bi.
Proof. revert T B b. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B b H. simpl in H.  destruct (lt_dec (Qty_bid T i ) 1) eqn:Hlr.
  simpl. right. 
  apply IHBi' in H. auto. simpl in H. destruct H. subst b. simpl. left. auto.
  apply IHBi' in H. auto. }
Qed.

Lemma bids_aux_elim (T: list transaction)(B:list order)(Bi :list nat) (b:order):
~ In (id b) (ids (bids_aux T (b :: B) Bi)) ->
bids_aux T B Bi = bids_aux T (b :: B) Bi.
Proof. revert T B b. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B b H. simpl.  destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr.
  apply IHBi'. simpl in H. rewrite Hlr in H. auto. simpl in H.
  rewrite Hlr in  H. simpl in H. destruct (id b =? i) eqn:Hi.
  destruct H.  left. move /eqP in Hi. auto. f_equal. 
  simpl in H. apply in_inv4 in H. destruct H. apply IHBi'. auto. }
Qed.

Lemma bids_aux_nil (B:list order)(Bi :list nat): bids_aux nil B Bi = nil. 
Proof.
induction Bi as [|b B']. simpl. auto.
simpl. auto.
Qed.

Lemma bids_aux_elim2 (T: list transaction)(B:list order)(Bi :list nat) (m:transaction):
~ In (idb m) Bi ->
bids_aux (m::T) B Bi = bids_aux T B Bi.
Proof. revert T B m. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B m H. simpl. 
  match goal with |[ |- context[if ?X then _ else _ ]] => destruct X eqn: HX end.
  simpl in H. destruct H. left. move /eqP in HX. auto. dlt1.
  apply IHBi'. intro. destruct H. simpl. auto. 
  replace (bids_aux (m :: T) B Bi') with (bids_aux T B Bi'). f_equal.
  symmetry. apply IHBi'. intro. destruct H. simpl. auto. } Qed.

Lemma Qty_bid_zero_implies_not_in (T: list transaction)(B:list order)(Bi :list nat)(j:nat):
(Qty_bid T j) = 0 -> ~In j (ids (bids_aux T B Bi)).
Proof. revert T B j. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B b H. simpl.  destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr.
  apply IHBi'. auto. simpl. intro.
  destruct H0. subst i. lia. apply IHBi' with (B:=B) in H. eauto. }
Qed.

Lemma nodup_Bi_nodup_ids_bids_aux (T: list transaction)(B:list order)(Bi :list nat):
NoDup Bi -> NoDup (ids (bids_aux T B Bi)).
Proof.  revert T B. induction Bi as [|i Bi']. 
{ intros T B H. simpl. auto. }
{ intros T B H. simpl.  destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr.
  apply IHBi'. eauto. simpl. constructor. assert(~In i Bi'). eauto. intro.
  destruct H0. apply In_ids_bids_in_Bi in H1. auto. apply IHBi'. eauto. }
Qed.

Lemma quant_bids_independent_B (T: list transaction)(B1 B2:list order)(Bi :list nat) (j:nat):
quant (bids_aux T B1 Bi) j = quant (bids_aux T B2 Bi) j.
Proof. revert T B1 B2 j. induction Bi as [|i Bi']. 
{ intros T B1 B2 j. simpl. auto. }
{ intros T B1 B2 j. simpl.  destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr.
  apply IHBi'. simpl. destruct (i =? j). auto. auto. }
 Qed.

Definition bids (T: list transaction)(B:list order):= uniq (bids_aux T B (ids B)).

Lemma bids_nil (B:list order): bids nil B = nil. 
Proof.
unfold bids. induction B as [|b B']. simpl. auto.
simpl. replace ((bids_aux nil (b :: B') (ids B'))) with (bids_aux nil B' (ids B')).
auto. apply bids_aux_elim. apply Qty_bid_zero_implies_not_in. simpl. auto.
Qed.

Lemma nodup_ids_bids (T: list transaction)(B:list order):
NoDup (ids B) -> NoDup (ids (bids T B)).
Proof.  unfold bids. intro. assert(NoDup (ids (bids_aux T B (ids B)))).
apply nodup_Bi_nodup_ids_bids_aux. auto. apply ndp_orders. auto. Qed.

Lemma id_In_ids_bids2 (T: list transaction)(B:list order)(j:nat):
In j (ids (bids T B)) -> In j (ids_bid_aux T).
Proof. unfold bids. intros. 
apply In_ids_bids_in_ida_T with (T:=T)(Bi:=(ids B))(B:=B). 
 apply ids_uniq1. auto. Qed.

Lemma bids_id_quant (T: list transaction)(B:list order) (i : nat):
NoDup (ids B) -> In i (ids B)->quant (bids T B) i = Qty_bid T i.
Proof. revert T i. unfold bids. induction B as [|b B']. simpl. 
intros. inversion H0. intros T i NDB. intros. simpl in H. destruct H. 
{
replace (quant (uniq (bids_aux T (b :: B') (ids (b :: B')))) i) with
(quant (bids_aux T (b :: B') (ids (b :: B'))) i). simpl. 
destruct (lt_dec (Qty_bid T (id b)) 1) eqn:Hlr. 
assert(~In i (ids (bids_aux T (b :: B') (ids B')))). 
apply Qty_bid_zero_implies_not_in. rewrite <- H. lia.
apply quant_elim in H0. subst i. lia.
simpl. assert (id b =? i = true). apply /eqP. auto. rewrite H0.
subst i. auto. 
apply quant_uniq.  apply nodup_Bi_nodup_ids_bids_aux. auto.
}
{
replace (quant (uniq (bids_aux T (b :: B') (ids (b :: B')))) i) with
(quant (bids_aux T (b :: B') (ids (b :: B'))) i). simpl. 
destruct (lt_dec (Qty_bid T (id b)) 1) eqn:Hlr.
replace ((bids_aux T (b :: B') (ids B'))) with
((bids_aux T B' (ids B'))).
replace (quant (bids_aux T B' (ids (B'))) i) with 
(quant (uniq (bids_aux T B' (ids (B')))) i). apply IHB'. eauto.
auto. symmetry. apply quant_uniq.  apply nodup_Bi_nodup_ids_bids_aux. eauto.
assert(~In (id b) (ids (bids_aux T (b :: B') (ids B')))).
apply Qty_bid_zero_implies_not_in. lia. apply bids_aux_elim. auto.
simpl.  destruct (id b =? i ) eqn:Hb.
move /eqP in Hb. subst i. auto.
replace (quant (bids_aux T (b :: B') (ids B')) i) with
(quant (bids_aux T B' (ids B')) i). 
replace (quant (bids_aux T B' (ids B')) i) with
(quant (uniq (bids_aux T B' (ids B'))) i). apply IHB'. eauto.
 auto. symmetry. apply quant_uniq. apply nodup_Bi_nodup_ids_bids_aux. eauto.
 apply quant_bids_independent_B. apply quant_uniq. apply nodup_Bi_nodup_ids_bids_aux. eauto.
} Qed.

Lemma bids_simplify (M: list transaction)(B:list order)(m:transaction)(b:order):
NoDup (ids (b::B)) -> 
id b = idb m -> oquantity b = tquantity m -> Subset (ids_bid_aux M) (ids B) ->
(uniq  (bids_aux (m :: M) (b :: B) (ids (b :: B)))) = b::(uniq  (bids_aux M B (ids B))).
Proof. intros. simpl. 
destruct (idb m =? id b) eqn: Hmb.
2:{ move /eqP in Hmb. destruct Hmb. auto. }
{ destruct (id b =? id b) eqn: Hb.
  2: { move /eqP in Hb. destruct Hb. auto. }
  { dlt1. { ltq1. }
    { replace (bids_aux (m :: M) (b :: B) (ids B)) with (bids_aux M (b::B) (ids B)).
      2:{ symmetry. apply bids_aux_elim2. intro. rewrite <- H0 in H3.
          assert(~In (id b) (ids B)). eauto. destruct (H4 H3). }
      replace (bids_aux M (b :: B) (ids B)) with (bids_aux M B (ids B)).
      2:{ apply bids_aux_elim.  intro. apply In_ids_bids_in_Bi in H3. simpl in H.
          assert(~In (id b) (ids B)). eauto. destruct (H4 H3). }
      simpl. match goal with |[ |- context[if ?X then _ else _ ]] => 
      destruct X eqn: HX end.
      move /membP in HX. apply In_b_bids_in_idb_Bi in HX. simpl in HX.
      simpl in H. assert(~In (id b) (ids B)). eauto. destruct (H3 HX).
      f_equal. clear HX. setxy.
      assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl.
      replace (Qty_bid M (id b)) with 0. lia. symmetry. apply Qty_bid_t_zero.
      intro. apply H2 in H3. simpl in H. assert(~In (id b) (ids B)). 
      eauto. destruct (H4 H3).
      assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
      assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
      assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.         
      crushxyorder1. 
   }
 }
} Qed.

Lemma bids_aux_elim0 (T: list transaction)(B:list order)(Bi: list nat)(b:order):
Qty_bid T (id b) = oquantity b -> timestamp B (id b) = otime b -> 
price B (id b) = oprice b -> In (id b) Bi -> In b (bids_aux T B Bi).
Proof. revert b T B. induction Bi as [|i Bi']. simpl. intros. inversion H2.
simpl. intros. destruct H2. 
  {   destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr. subst i.
      assert(Hl:=l).  rewrite H in Hl.
      ltqo.
      simpl. left.  subst i.  setxy.
      assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl. auto.
      assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
      assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
      assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.         
      crushxyorder1.
   }
   { destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr. apply IHBi'.
     all:auto.
   } Qed. 

Lemma bids_aux_intro0 (T: list transaction)(B:list order)(Bi: list nat)(b:order):
In b (bids_aux T B Bi) ->  Qty_bid T (id b) = oquantity b/\
timestamp B (id b) = otime b/\price B (id b) = oprice b/\In (id b) Bi.
Proof. 
revert b T B. induction Bi as [|i Bi']. simpl. intros. inversion H.
simpl. intros.
  {   destruct (lt_dec (Qty_bid T i) 1) eqn:Hlr.
      apply IHBi' in H. repeat split. apply H. apply H. apply H.
      right. apply H. destruct H. subst b. simpl. auto.
      apply IHBi' in H. repeat split. apply H. apply H. apply H. 
      right. apply H.
  } Qed. 

Lemma bids_perm (T: list transaction)(B1 B2:list order)(b:order):
NoDup (ids B1) -> NoDup (ids B2) -> perm B1 B2 ->  perm (bids T B1) (bids T B2). 
Proof. intros NDB1 NDB2 H. apply perm_intro. intros.
       assert(count a (uniq (bids_aux T B1 (ids B1))) = 0 \/
       count a (uniq (bids_aux T B1 (ids B1)))  = 1).  
       assert(NoDup (uniq (bids_aux T B1 (ids B1)))). eauto.
       apply nodup_count with (x:=a) in H0. lia.
       assert(count a (uniq (bids_aux T B2 (ids B2))) = 0 \/
       count a (uniq (bids_aux T B2 (ids B2)))  = 1).
       assert(NoDup (uniq (bids_aux T B2 (ids B2)))). eauto.
       apply nodup_count with (x:=a) in H1. lia.
       destruct H0;destruct H1. { unfold bids.  lia. } 3:{ unfold bids. lia. }
       { assert(In a (uniq (bids_aux T B2 (ids B2)))). apply countP1b.
         lia. assert(~In a (uniq (bids_aux T B1 (ids B1)))). apply countP3.
         auto. apply uniq_intro_elim in H2. assert(~In a (bids_aux T B1 (ids B1))).
         intro. apply uniq_intro_elim in H4. destruct(H3 H4). clear H3.
         apply bids_aux_intro0 in H2.
         destruct H2. destruct H3. destruct H5.
         destruct H4. assert(timestamp B2 (id a) = timestamp B1 (id a)).
         apply timeprice_perm. auto. auto. auto. apply bids_aux_elim0. 
         all:auto. lia. rewrite <- H5. apply timeprice_perm. auto.
         auto. auto. apply ids_perm in H. unfold perm in H.
         move /andP in H. destruct H. eauto.
       }
       { assert(In a (uniq (bids_aux T B1 (ids B1)))). apply countP1b.
         lia. assert(~In a (uniq (bids_aux T B2 (ids B2)))). apply countP3.
         auto. apply uniq_intro_elim in H2. assert(~In a (bids_aux T B2 (ids B2))).
         intro. apply uniq_intro_elim in H4. destruct(H3 H4). clear H3.
         apply bids_aux_intro0 in H2.
         destruct H2. destruct H3. destruct H5.
         destruct H4. assert(timestamp B1 (id a) = timestamp B2 (id a)).
         apply timeprice_perm. auto. auto. auto. apply bids_aux_elim0. 
         all:auto. lia. rewrite <- H5. apply timeprice_perm. auto.
         auto. auto. apply ids_perm in H. unfold perm in H.
         move /andP in H. destruct H. eauto.
       } Qed.

End Bids.

Section Asks.
(****Start: This part is for Asks which is mirror image of Bids**********)

Definition Asks (A:list order)(T: list transaction)(A': list order):=
subset (ids_ask_aux T) (ids A') ->
(forall a, In a A -> (exists t, (In t T)/\(ida t = id a)/\(oquantity a = Qty_ask T (id a))/\
(exists a', (In a' A')/\(id a = id a')/\(otime a = otime a')/\(oprice a = oprice a'))))
/\
(subset (ids_ask_aux T) (ids A))/\(NoDup A).

Fixpoint asks_aux (T: list transaction)(A:list order)(Ai :list nat):(list order).
refine ( match Ai with
    |nil => nil
    |i::Ai' => match (Compare_dec.lt_dec (Qty_ask T i) 1) with
        |left _ => asks_aux T A Ai'
        |right _ => (Mk_order i (timestamp A i) (Qty_ask T i) (price A i) _ ):: (asks_aux T A Ai')
 end
 end). rewrite PeanoNat.Nat.ltb_nlt. auto.
 Defined.
 
Lemma In_ids_asks_in_Bi (T: list transaction)(B:list order)(Bi :list nat)(j:nat):
In j (ids (asks_aux T B Bi)) -> In j Bi.
Proof. revert T B j. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B b H. simpl in H.  destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr.
  simpl. right. 
  apply IHBi' in H. auto. simpl in H. destruct H. simpl. left. auto.
  apply IHBi' in H. auto. }
Qed.
 
Lemma In_ids_asks_in_idb_T (T: list transaction)(B:list order)(Bi :list nat)(j:nat):
In j (ids (asks_aux T B Bi)) -> In j (ids_ask_aux T).
Proof. revert T B j. induction Bi as [|i Bi']. 
{ intros T B b H. simpl in H. inversion H. }
{ intros T B b H. simpl in H. destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr.
  apply IHBi' in H. auto. simpl in H. destruct H. 
  assert(In b (ids_ask_aux T)\/~In b (ids_ask_aux T)). eauto.
  destruct H0. auto. apply Qty_ask_t_zero in H0. subst i. lia.
  apply IHBi' in H. auto. }
Qed.

Lemma asks_aux_elim (T: list transaction)(B:list order)(Bi :list nat) (b:order):
~ In (id b) (ids (asks_aux T (b :: B) Bi)) ->
asks_aux T B Bi = asks_aux T (b :: B) Bi.
Proof. revert T B b. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B b H. simpl. destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr.
  apply IHBi'. simpl in H. rewrite Hlr in H. auto. simpl in H.
  rewrite Hlr in  H. simpl in H. destruct (id b =? i) eqn:Hi.
  destruct H.  left. move /eqP in Hi. auto. f_equal. 
  simpl in H. apply in_inv4 in H. destruct H. apply IHBi'. auto. }
Qed.

Lemma asks_aux_nil (B:list order)(Bi :list nat): asks_aux nil B Bi = nil. 
Proof.
induction Bi as [|b B']. simpl. auto.
simpl. auto.
Qed.

Lemma asks_aux_elim2 (T: list transaction)(B:list order)(Bi :list nat) (m:transaction):
~ In (ida m) Bi ->
asks_aux (m::T) B Bi = asks_aux T B Bi.
Proof. revert T B m. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B m H. simpl. 
  match goal with |[ |- context[if ?X then _ else _ ]] => destruct X eqn: HX end.
  simpl in H. destruct H. left. move /eqP in HX. auto. dlt1.
  apply IHBi'. intro. destruct H. simpl. auto. 
  replace (asks_aux (m :: T) B Bi') with (asks_aux T B Bi'). f_equal.
  symmetry. apply IHBi'. intro. destruct H. simpl. auto. } Qed.
  
Lemma In_a_asks_in_ida_Bi (T: list transaction)(B:list order)(Bi :list nat)(a:order):
In a (asks_aux T B Bi) -> In (id a) Bi.
Proof. revert T B a. induction Bi as [|i Bi']. 
{ intros T B a H. simpl. auto. }
{ intros T B a H. simpl in H.  destruct (lt_dec (Qty_ask T i ) 1) eqn:Hlr.
  simpl. right. 
  apply IHBi' in H. auto. simpl in H. destruct H. subst a. simpl. left. auto.
  apply IHBi' in H. auto. }
Qed.

Lemma Qty_ask_zero_implies_not_in (T: list transaction)(B:list order)(Bi :list nat)(j:nat):
(Qty_ask T j) = 0 -> ~In j (ids (asks_aux T B Bi)).
Proof. revert T B j. induction Bi as [|i Bi']. 
{ intros T B b H. simpl. auto. }
{ intros T B b H. simpl. destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr.
  apply IHBi'. auto. simpl. intro.
  destruct H0. subst i. lia. apply IHBi' with (B:=B) in H. eauto. }
Qed.

Lemma nodup_Bi_nodup_ids_asks_aux (T: list transaction)(B:list order)(Bi :list nat):
NoDup Bi -> NoDup (ids (asks_aux T B Bi)).
Proof.  revert T B. induction Bi as [|i Bi']. 
{ intros T B H. simpl. auto. }
{ intros T B H. simpl.  destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr.
  apply IHBi'. eauto. simpl. constructor. assert(~In i Bi'). eauto. intro.
  destruct H0. apply In_ids_asks_in_Bi in H1. auto. apply IHBi'. eauto. }
Qed.

Lemma quant_asks_independent_A (T: list transaction)(B1 B2:list order)(Bi :list nat) (j:nat):
quant (asks_aux T B1 Bi) j = quant (asks_aux T B2 Bi) j.
Proof. revert T B1 B2 j. induction Bi as [|i Bi']. 
{ intros T B1 B2 j. simpl. auto. }
{ intros T B1 B2 j. simpl.  destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr.
  apply IHBi'. simpl. destruct (i =? j). auto. auto. }
 Qed.

Definition asks (T: list transaction)(A:list order):= uniq (asks_aux T A (ids A)).

Lemma asks_nil (B:list order): asks nil B = nil. 
Proof.
unfold asks. induction B as [|b B']. simpl. auto.
simpl. replace ((asks_aux nil (b :: B') (ids B'))) with (asks_aux nil B' (ids B')).
auto. apply asks_aux_elim. apply Qty_ask_zero_implies_not_in. simpl. auto.
Qed.

Lemma nodup_ids_asks (T: list transaction)(B:list order):
NoDup (ids B) -> NoDup (ids (asks T B)).
Proof.  unfold asks. intro. assert(NoDup (ids (asks_aux T B (ids B)))).
apply nodup_Bi_nodup_ids_asks_aux. auto. apply ndp_orders. auto. Qed.

Lemma id_In_ids_asks2 (T: list transaction)(B:list order)(j:nat):
In j (ids (asks T B)) -> In j (ids_ask_aux T).
Proof. unfold asks. intros. 
apply In_ids_asks_in_idb_T with (T:=T)(Bi:=(ids B))(B:=B). 
 apply ids_uniq1. auto. Qed.

Lemma asks_id_quant (T: list transaction)(B:list order) (i : nat):
NoDup (ids B) -> In i (ids B)->quant (asks T B) i = Qty_ask T i.
Proof. revert T i. unfold asks. induction B as [|b B']. simpl. 
intros. inversion H0. intros T i NDB. intros. simpl in H. destruct H. 
{
replace (quant (uniq (asks_aux T (b :: B') (ids (b :: B')))) i) with
(quant (asks_aux T (b :: B') (ids (b :: B'))) i). simpl. 
destruct (lt_dec (Qty_ask T (id b)) 1) eqn:Hlr. 
assert(~In i (ids (asks_aux T (b :: B') (ids B')))). 
apply Qty_ask_zero_implies_not_in. rewrite <- H. lia.
apply quant_elim in H0. subst i. lia.
simpl. assert (id b =? i = true). apply /eqP. auto. rewrite H0.
subst i. auto. 
apply quant_uniq.  apply nodup_Bi_nodup_ids_asks_aux. auto.
}
{
replace (quant (uniq (asks_aux T (b :: B') (ids (b :: B')))) i) with
(quant (asks_aux T (b :: B') (ids (b :: B'))) i). simpl. 
destruct (lt_dec (Qty_ask T (id b)) 1) eqn:Hlr.
replace ((asks_aux T (b :: B') (ids B'))) with
((asks_aux T B' (ids B'))).
replace (quant (asks_aux T B' (ids (B'))) i) with 
(quant (uniq (asks_aux T B' (ids (B')))) i). apply IHB'. eauto.
auto. symmetry. apply quant_uniq.  apply nodup_Bi_nodup_ids_asks_aux. eauto.
assert(~In (id b) (ids (asks_aux T (b :: B') (ids B')))).
apply Qty_ask_zero_implies_not_in. lia. apply asks_aux_elim. auto.
simpl.  destruct (id b =? i ) eqn:Hb.
move /eqP in Hb. subst i. auto.
replace (quant (asks_aux T (b :: B') (ids B')) i) with
(quant (asks_aux T B' (ids B')) i). 
replace (quant (asks_aux T B' (ids B')) i) with
(quant (uniq (asks_aux T B' (ids B'))) i). apply IHB'. eauto.
 auto. symmetry. apply quant_uniq. apply nodup_Bi_nodup_ids_asks_aux. eauto.
 apply quant_asks_independent_A. apply quant_uniq. apply nodup_Bi_nodup_ids_asks_aux. eauto.
 } Qed.



Lemma asks_simplify (M: list transaction)(A:list order)(m:transaction)(a:order):
NoDup (ids (a::A)) -> 
id a = ida m -> oquantity a = tquantity m -> Subset (ids_ask_aux M) (ids A) ->
(uniq  (asks_aux (m :: M) (a :: A) (ids (a :: A)))) = a::(uniq  (asks_aux M A (ids A))).
Proof.  intros. simpl. 
destruct (ida m =? id a) eqn: Hmb.
2:{ move /eqP in Hmb. destruct Hmb. auto. }
{ destruct (id a =? id a) eqn: Hb.
  2: { move /eqP in Hb. destruct Hb. auto. }
  { dlt1. { ltq1. }
    { replace (asks_aux (m :: M) (a :: A) (ids A)) with (asks_aux M (a::A) (ids A)).
      2:{ symmetry. apply asks_aux_elim2. intro. rewrite <- H0 in H3.
          assert(~In (id a) (ids A)). eauto. destruct (H4 H3). }
      replace (asks_aux M (a :: A) (ids A)) with (asks_aux M A (ids A)).
      2:{ apply asks_aux_elim.  intro. apply In_ids_asks_in_Bi in H3. simpl in H.
          assert(~In (id a) (ids A)). eauto. destruct (H4 H3). }
      simpl. match goal with |[ |- context[if ?X then _ else _ ]] => destruct X eqn: HX end.
      move /membP in HX. apply In_a_asks_in_ida_Bi in HX. simpl in HX.
      simpl in H. assert(~In (id a) (ids A)). eauto. destruct (H3 HX).
      f_equal. clear HX. setxy.
      assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl.
      replace (Qty_ask M (id a)) with 0. lia. symmetry. apply Qty_ask_t_zero.
      intro. apply H2 in H3. simpl in H. assert(~In (id a) (ids A)). eauto. destruct (H4 H3).
      assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
      assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
      assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.         
      crushxyorder1. 
   }
 }
} Qed.

Lemma asks_aux_elim0 (T: list transaction)(B:list order)(Bi: list nat)(b:order):
Qty_ask T (id b) = oquantity b -> timestamp B (id b) = otime b -> price B (id b) = oprice b
-> In (id b) Bi -> In b (asks_aux T B Bi).
Proof. revert b T B. induction Bi as [|i Bi']. simpl. intros. inversion H2.
simpl. intros. destruct H2. 
  {   destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr. subst i.
      assert(Hl:=l).  rewrite H in Hl.
      ltqo.
      simpl. left.  subst i.  setxy.
      assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl. auto.
      assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
      assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
      assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.         
      crushxyorder1.
   }
   { destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr. apply IHBi'.
     all:auto.
   } Qed. 

Lemma asks_aux_intro0 (T: list transaction)(B:list order)(Bi: list nat)(b:order):
In b (asks_aux T B Bi) -> 
Qty_ask T (id b) = oquantity b/\timestamp B (id b) = otime b/\price B (id b) = oprice b/\In (id b) Bi.
Proof. 
revert b T B. induction Bi as [|i Bi']. simpl. intros. inversion H.
simpl. intros.
  {   destruct (lt_dec (Qty_ask T i) 1) eqn:Hlr.
      apply IHBi' in H. repeat split. apply H. apply H. apply H.
      right. apply H. destruct H. subst b. simpl. auto.
      apply IHBi' in H. repeat split. apply H. apply H. apply H. 
      right. apply H.
  } Qed. 

Lemma asks_perm (T: list transaction)(B1 B2:list order)(b:order):
NoDup (ids B1) -> NoDup (ids B2) -> perm B1 B2 ->  perm (asks T B1) (asks T B2). 
Proof. intros NDB1 NDB2 H. apply perm_intro. intros.
       assert(count a (uniq (asks_aux T B1 (ids B1))) = 0 \/
       count a (uniq (asks_aux T B1 (ids B1)))  = 1).  
       assert(NoDup (uniq (asks_aux T B1 (ids B1)))). eauto.
       apply nodup_count with (x:=a) in H0. lia.
       assert(count a (uniq (asks_aux T B2 (ids B2))) = 0 \/
       count a (uniq (asks_aux T B2 (ids B2)))  = 1).
       assert(NoDup (uniq (asks_aux T B2 (ids B2)))). eauto.
       apply nodup_count with (x:=a) in H1. lia.
       destruct H0;destruct H1. { unfold asks.   lia. } 3:{ unfold asks. lia. }
       { assert(In a (uniq (asks_aux T B2 (ids B2)))). apply countP1b.
         lia. assert(~In a (uniq (asks_aux T B1 (ids B1)))). apply countP3.
         auto. apply uniq_intro_elim in H2. assert(~In a (asks_aux T B1 (ids B1))).
         intro. apply uniq_intro_elim in H4. destruct(H3 H4). clear H3.
         apply asks_aux_intro0 in H2.
         destruct H2. destruct H3. destruct H5.
         destruct H4. assert(timestamp B2 (id a) = timestamp B1 (id a)).
         apply timeprice_perm. auto. auto. auto. apply asks_aux_elim0. 
         all:auto. lia. rewrite <- H5. apply timeprice_perm. auto.
         auto. auto. apply ids_perm in H. unfold perm in H.
         move /andP in H. destruct H. eauto.
       }
       { assert(In a (uniq (asks_aux T B1 (ids B1)))). apply countP1b.
         lia. assert(~In a (uniq (asks_aux T B2 (ids B2)))). apply countP3.
         auto. apply uniq_intro_elim in H2. assert(~In a (asks_aux T B2 (ids B2))).
         intro. apply uniq_intro_elim in H4. destruct(H3 H4). clear H3.
         apply asks_aux_intro0 in H2.
         destruct H2. destruct H3. destruct H5.
         destruct H4. assert(timestamp B1 (id a) = timestamp B2 (id a)).
         apply timeprice_perm. auto. auto. auto. apply asks_aux_elim0. 
         all:auto. lia. rewrite <- H5. apply timeprice_perm. auto.
         auto. auto. apply ids_perm in H. unfold perm in H.
         move /andP in H. destruct H. eauto.
       } Qed.

(****End: This part is for Asks which is mirror image of Bids*******)

End Asks.

Section Matchings.

(*####Definitions: over, valid, Valid, Qty, idas, idbs, Bids, Asks #######*)
Definition tradable (b a: order):= (oprice b >= oprice a).

Definition matchable (B A : list order):= exists b a, (In a A)/\(In b B)/\(tradable b a).

Definition over (t : transaction)(B A : list order):= exists b a, (In a A)/\(In b B)/\(idb t = id b)/\(ida t = id a).

Definition valid (t : transaction)(B A : list order):= exists b a, (In a A)/\(In b B)/\(idb t = id b)/\(ida t = id a)/\(tradable b a)/\(tquantity t <= oquantity b)/\(tquantity t <= oquantity a).

Definition Tvalid (T : list transaction)(B A : list order):=forall t, (In t T) -> (valid t B A).



(* ####### Definitions: Matching, Canonical form ######### *)

Definition Matching (M: list transaction)(B A: list order):= 
  (Tvalid M B A)/\
  (forall b: order, In b B -> (Qty_bid M (id b)) <= (oquantity b))/\
  (forall a: order, In a A-> (Qty_ask M (id a)) <= (oquantity a)).

End Matchings.

Section CannonicalForm.

Definition CanonicalForm (M M': list transaction):= (*M is canForm of M'*)
(forall m, In m M -> (Qty M' (idb m) (ida m) = tquantity m)/\(exists m', (In m' M')/\(idb m = idb m')/\(ida m = ida m')))
/\(forall m', In m' M' -> exists m, (In m M)/\(idb m' = idb m)/\(ida m' = ida m)/\(Qty M' (idb m) (ida m) = tquantity m))
/\(NoDup M).

Fixpoint cform_aux (T: list transaction)(Bi Ai :list nat):(list transaction).
refine ( match (Bi,Ai) with
    |(nil, _) => nil
    |(_, nil) => nil
    |(i::Bi', j::Ai') => match (Compare_dec.lt_dec (Qty T i j) 1) with
        |left _ => cform_aux T Bi' Ai'
        |right _ => (Mk_transaction i j (Qty T i j) _ ):: (cform_aux T Bi' Ai')
 end
 end). rewrite PeanoNat.Nat.ltb_nlt. auto.
 Defined.

Lemma cform_aux_intro0 (M: list transaction)(m m0:transaction)(I J: list nat):
(idb m <> idb m0) \/ (ida m <> ida m0) -> In m (cform_aux M I J) <-> In m (cform_aux (m0 :: M) I J).
Proof. revert J m m0. induction I as [| i Bi]. 
{ intros.
simpl. split. auto. auto. 
}
{ split.  
  { intros. case J as [|j Ai]. 
    { simpl in H0. inversion H0. }
    { simpl in H0. destruct (lt_dec (Qty M i j) 1) eqn:Hlt.
      { simpl. destruct ((idb m0 =? i) && (ida m0 =? j)) eqn:Hm0i.
        { destruct (lt_dec (tquantity m0 + Qty M i j) 1 ).
          { destruct m0. simpl in l0. assert((tquantity0 <? 1) = false) as Hl.
            auto. move /ltP in Hl. lia.  }
          { simpl. right. apply IHBi. auto. auto. } 
        }
        { rewrite Hlt. apply IHBi. auto. auto. }
        }
      { destruct H0. 
        { simpl. destruct ((idb m0 =? i) && (ida m0 =? j)) eqn:Hm0i.
          { destruct (lt_dec (tquantity m0 + Qty M i j) 1 ).
            { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
            auto. move /ltP in Hl. lia. }
            { simpl. left. subst. simpl in H. { destruct H as [Hi | Hj]. { 
              move /andP in Hm0i. destruct Hm0i as [H0i H0j]. move /eqP in H0i.
              subst i. destruct Hi;auto. } { move /andP in Hm0i. destruct Hm0i as [H0i H0j]. 
              move /eqP in H0j. subst j. destruct Hj;auto. }   } } 
          }
          { rewrite Hlt. left. subst. f_equal. } 
        }
        { simpl. destruct ((idb m0 =? i) && (ida m0 =? j)) eqn:Hm0i.
          { destruct (lt_dec (tquantity m0 + Qty M i j) 1 ).
            { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
              auto. move /ltP in Hl. lia. }
            { simpl. right. apply IHBi. auto. auto.  } 
          }
          { rewrite Hlt. right. apply IHBi. auto. auto. }
       }
      }
    }
  }
  { (*Other side *) intros. case J as [|j Ai]. 
   { simpl in H0. inversion H0. }
    { simpl. destruct (lt_dec (Qty M i j) 1) eqn:Hlt. 
      { simpl. destruct ((idb m0 =? i) && (ida m0 =? j)) eqn:Hm0i.
        { destruct (lt_dec (tquantity m0 + Qty M i j) 1 ).
          { destruct m0. simpl in l0. assert((tquantity0 <? 1) = false) as Hl.
            auto. move /ltP in Hl. lia.  }
          { simpl in H0. rewrite Hm0i in  H0.
            destruct (lt_dec (tquantity m0 + Qty M i j) 1 ).
              { lia. }
              { destruct H0. 
                { subst m. destruct H as [Hi | Hj]. { 
                  move /andP in Hm0i. destruct Hm0i as [H0i H0j]. move /eqP in H0i.
                  subst i. destruct Hi;auto. } { move /andP in Hm0i. destruct Hm0i as [H0i H0j]. 
                  move /eqP in H0j. subst j. destruct Hj;auto. } 
                }   
                { apply IHBi in H0. auto. auto. }
              } 
          }
        }
        { simpl in H0. rewrite Hm0i in H0. rewrite Hlt in H0. 
            apply IHBi in H0.  auto.  auto. 
        }
      }
      { simpl in H0. destruct ((idb m0 =? i) && (ida m0 =? j)) eqn:Hm0i.
        { destruct (lt_dec (tquantity m0 + Qty M i j) 1 ) eqn:Hlt2.
          { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
            auto. move /ltP in Hl. lia.  
          }
         { destruct H0. 
                { subst m. simpl in H. destruct H as [Hi | Hj]. { 
                  move /andP in Hm0i. destruct Hm0i as [H0i H0j]. move /eqP in H0i.
                  subst i. destruct Hi;auto. } { move /andP in Hm0i. destruct Hm0i as [H0i H0j]. 
                  move /eqP in H0j. subst j. destruct Hj;auto. } 
                }   
                { apply IHBi in H0. auto. auto. }
              } 
        }
        { rewrite Hlt in H0. destruct H0. 
          { subst m.  auto. } 
          { apply IHBi in H0. auto. auto. }
        }
      }
    }
  }
} Qed.

Lemma cform_aux_Qty_positive (M:list transaction) (m:transaction) (I J:list nat):
In m (cform_aux M I J) -> Qty M (idb m) (ida m) >0.
Proof. 
revert M J m. induction I as [| i Bi]. 
{ intros. simpl in H. inversion H. }
{ intros. case J as [|j Ai]. 
    { simpl in H. inversion H. }
    { simpl in H. destruct (lt_dec (Qty M i j) 1) eqn:Hlt. 
      { apply IHBi in H. auto. }
      { destruct H. subst m. simpl. lia. 
        apply IHBi in H. auto. 
      }
    }
} Qed. 

Lemma cform_aux_Qty_correct (M:list transaction) (m:transaction) (I J:list nat):
In m (cform_aux M I J) -> tquantity m = Qty M (idb m) (ida m).
Proof. 
revert M J m. induction I as [| i Bi]. 
{ intros. simpl in H. inversion H. }
{ intros. case J as [|j Ai]. 
    { simpl in H. inversion H. }
    { simpl in H. destruct (lt_dec (Qty M i j) 1) eqn:Hlt. 
      { apply IHBi in H. auto. }
      { destruct H. subst m. simpl. lia. 
        apply IHBi in H. auto. 
      }
    }
} Qed. 


Lemma cform_aux_elim0 (M: list transaction)(m:transaction):
(~(Qty M (idb m) (ida m)) <1) /\ ((tquantity m = Qty M (idb m) (ida m)))
<->(In m (cform_aux M (ids_bid_aux M) (ids_ask_aux M))).
Proof. split. 
{ intros. destruct H. induction M as [|m0 M0]. 
  { simpl in H0. destruct m. simpl in H0. assert((tquantity0 <? 1) = false). auto.
    move /ltP in H1. lia. 
  } 
  { destruct ((idb m =? idb m0) && (ida m =? ida m0)) eqn:Hmm0.
    { move /andP in Hmm0. destruct Hmm0. move /eqP in H1.
      move /eqP in H2. destruct m. destruct m0.
      simpl in H1. simpl in H2. subst. simpl in H. simpl in H0.
      simpl in IHM0. assert ((idb1 =? idb1) && (ida1 =? ida1) = true).
      { apply /andP. split. apply /eqP;auto. apply /eqP;auto. } 
      simpl. rewrite H1. rewrite H1 in H. rewrite H1 in H0.
      destruct (lt_dec (tquantity1 + Qty M0 idb1 ida1) 1) eqn:Hlt.
      { lia. }
      { left. subst tquantity0. f_equal. apply eq_proofs_unicity. eauto. } 
    }
    { simpl. assert ((idb m0 =? idb m0) && (ida m0 =? ida m0) =true).
      { apply /andP. split. apply /eqP;auto. apply /eqP;auto. } 
      rewrite H1. destruct (lt_dec (tquantity m0 + Qty M0 (idb m0) (ida m0)) 1) eqn: Hlt. 
      { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Ht. auto. move /ltP in Ht.
        lia. }
      { simpl. right. simpl in H.  assert(((idb m0 =? idb m) && (ida m0 =? ida m)) =false) as Hmm0'.
        { apply /andP. intro. destruct H2. move /eqP in H2. move /eqP in H3. 
          rewrite H2 in Hmm0. rewrite H3 in Hmm0. move /andP in Hmm0.
          destruct Hmm0. split. apply /eqP;auto. apply /eqP;auto. } 
        rewrite Hmm0' in H. apply IHM0 in H. eapply cform_aux_intro0 in H. exact H.
        { apply nat_tr. auto. } simpl in H0. destruct ((idb m0 =? idb m) && (ida m0 =? ida m)) eqn: Hm.
        move /andP in Hm. destruct Hm. move /eqP in H2.
        move /eqP in H3. inversion Hmm0'. exact.
      }
    }
  }
}
{ intros. split. 
          { apply cform_aux_Qty_positive in H. lia. }
          { apply cform_aux_Qty_correct in H. lia. }
} Qed.

Lemma cform_aux_elim1 (M: list transaction)(m:transaction)(I J: list nat): 
In m (cform_aux M I J) -> In m (cform_aux M (ids_bid_aux M) (ids_ask_aux M)).
Proof. revert M J. induction I as [|i Bi]. 
    { intros. simpl in H. inversion H. }
    { intros. destruct J as [|j Bj]. simpl in H. inversion H.
      simpl in H. destruct (lt_dec (Qty M i j) 1) eqn:Hlt. 
      { apply IHBi in H. auto. }
      { destruct H. 
        { eapply cform_aux_elim0. repeat split.
          { subst m. simpl. auto. }
          { subst m. simpl. auto. }
        }
        { apply IHBi in H. auto. }}
    } Qed.


Definition cform (M: list transaction):(list transaction) :=
uniq (cform_aux M (ids_bid_aux M) (ids_ask_aux M)).


Lemma cform_correct_I (M:list transaction):
forall m, In m (cform M) -> (Qty M (idb m) (ida m) = tquantity m)/\(exists m', In m' M /\ (idb m = idb m')/\(ida m = ida m')).
Proof. induction M as [|m0 M]. 
    { unfold cform. intros m H0. apply uniq_intro_elim in H0. simpl in H0. inversion H0. }
    { unfold cform. intros m H0. apply uniq_intro_elim in H0.
      simpl in H0. assert ((idb m0 =? idb m0) && (ida m0 =? ida m0) = true) as H1. 
      apply /andP. split. apply /eqP;auto. apply /eqP;auto. 
      rewrite H1 in H0. destruct (lt_dec (tquantity m0 + Qty M (idb m0) (ida m0)) 1 ).
      { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
        auto. move /ltP in Hl. lia.  }
      { destruct H0. 
        { assert ((tquantity m0 + Qty M (idb m0) (ida m0) <? 1) = false) as Hn1. 
          apply /ltP. auto. repeat split.
            { simpl. assert((idb m0 =? idb m) && (ida m0 =? ida m) = true). 
              apply /andP. subst m. simpl. split. apply /eqP;auto. apply /eqP;auto.
              rewrite H0. subst m. simpl. auto.
            }
            { exists m0. simpl. intros. subst m. simpl. auto. }
        }
        { (*induction main case:*) 
          eapply cform_aux_elim1 in H.
          simpl in H. assert ((idb m0 =? idb m0) && (ida m0 =? ida m0) = true) as H2. 
          apply /andP. split. apply /eqP;auto. apply /eqP;auto. 
          rewrite H2 in H. destruct (lt_dec (tquantity m0 + Qty M (idb m0) (ida m0)) 1 ).
          { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
            auto. move /ltP in Hl. lia.  }
          { simpl. destruct((idb m0 =? idb m) && (ida m0 =? ida m)) eqn:Hmm0.
          { destruct H. 
            { repeat split.
              { subst. simpl. auto. }
              { exists m0. simpl. intros. subst m. simpl. auto. } 
            } 
            { split. apply cform_aux_Qty_correct in H as Hm. simpl in Hm. 
              rewrite Hmm0 in Hm. exact. exists m0. intros.
              move /andP in Hmm0. destruct Hmm0. move /eqP in H3.
              move /eqP in H0. auto.
            }
          } 
          { destruct H. 
            { repeat split.
              { subst m. simpl in Hmm0. simpl. assert((idb m0 =? idb m0) && (ida m0 =? ida m0) =true).
                apply /andP. split. apply /eqP;auto. apply /eqP;auto. rewrite H in Hmm0. inversion Hmm0.  
              }
              { subst m. simpl in Hmm0.  replace ((idb m0 =? idb m0) && (ida m0 =? ida m0)) with true in Hmm0. inversion Hmm0. } 
            } 
            { split. apply cform_aux_Qty_correct in H as Hm. simpl in Hm. 
              rewrite Hmm0 in Hm. exact. apply cform_aux_intro0 in H.
              apply uniq_intro_elim in H. apply IHM in H. destruct H. destruct H0.
              exists x. split. right. apply H0. apply H0. assert ((idb m = idb m0 \/ idb m <> idb m0)).
              eauto. assert ((ida m = ida m0 \/ ida m <> ida m0)). eauto. destruct H3;destruct H4.
              assert((idb m0 =? idb m) && (ida m0 =? ida m)). apply  /andP. split.
              apply /eqP. auto. apply /eqP. auto. rewrite Hmm0 in H5. inversion H5. auto. auto.
              auto.
            }
         }
       }
     }
   }
 } Qed.



Lemma cform_correct_II (M:list transaction):
(forall m', In m' M -> exists m, (In m  (cform M))/\(idb m' = idb m)/\(ida m' = ida m)/\(Qty M (idb m) (ida m) = tquantity m)).
Proof. 
{ intros. induction M as [|m0 M0]. 
  { inversion H. }
  { destruct H. 
    { subst m'. assert (Nat.ltb (Qty (m0 :: M0) (idb m0) (ida m0)) 1 = false).
      simpl. assert ((idb m0 =? idb m0) && (ida m0 =? ida m0) = true).
      apply /andP. split. apply /eqP;auto. apply /eqP;auto. rewrite H.
      rewrite PeanoNat.Nat.ltb_nlt. intro. destruct m0.
      simpl in H0. assert( (tquantity0 <? 1) = false). auto.
      move /ltP in H1. lia. simpl in H. 
      assert ((idb m0 =? idb m0) && (ida m0 =? ida m0) = true) as Hms.
      apply /andP. split. apply /eqP;auto. apply /eqP;auto. rewrite Hms in H.
      set m':= {|idb := idb m0; ida := ida m0; tquantity := 
          tquantity m0 + Qty M0 (idb m0) (ida m0); tquantity_cond := H|}.
      exists m'. assert (In m' (cform (m0 :: M0)))  as oGoal.
      unfold cform. 
      cut (In m'(cform_aux (m0 :: M0) (ids_bid_aux (m0 :: M0))
        (ids_ask_aux (m0 :: M0)))). apply uniq_intro_elim.
      simpl. rewrite Hms. 
      destruct (lt_dec (tquantity m0 + Qty M0 (idb m0) (ida m0)) 1 ).
      { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
        auto. move /ltP in Hl. lia. } 
      left. subst m'. f_equal. apply eq_proofs_unicity. eauto.
      repeat split. 
      { exact. }
      { apply uniq_intro_elim in oGoal.
        apply cform_aux_Qty_correct in oGoal. auto.
      } 
    }
    { apply IHM0 in H. destruct H as [ m H].
      destruct H. destruct H0. destruct H1.
      apply cform_correct_I in H as H3. destruct H3. 
      destruct ((idb m' =? idb m0) && (ida m' =? ida m0)) eqn: Hmm.
      { replace (idb m') with (idb m). replace (ida m') with (ida m).
        replace (idb m') with (idb m) in Hmm. replace (ida m') with (ida m) in Hmm.
        assert (Nat.ltb (tquantity m0 + Qty M0 (idb m0) (ida m0)) 1 = false).
        { rewrite PeanoNat.Nat.ltb_nlt. destruct m0. simpl. 
          assert( (tquantity0 <? 1) = false). auto.
          move /ltP in H5. lia.
        }
        { assert ((idb m0 =? idb m0) && (ida m0 =? ida m0) = true) as Hms.
          apply /andP. split. apply /eqP;auto. apply /eqP;auto.
          set m1:= {|idb := idb m0; ida := ida m0; tquantity := 
          (tquantity m0 + Qty M0 (idb m0) (ida m0)); tquantity_cond := H5|}.
          exists m1. assert (In m1 (cform (m0 :: M0)))  as oGoal.
          { unfold cform. 
            cut (In m1 (cform_aux (m0 :: M0) (ids_bid_aux (m0 :: M0))
            (ids_ask_aux (m0 :: M0)))). apply uniq_intro_elim.
            simpl. rewrite Hms. 
            destruct (lt_dec (tquantity m0 + Qty M0 (idb m0) (ida m0)) 1 ).
            { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
              auto. move /ltP in Hl. lia. 
            } 
            { simpl. left. subst m1. f_equal. apply eq_proofs_unicity. eauto. }
          }
          { move /andP in Hmm. destruct Hmm. move /eqP in H6.
            move /eqP in H7. repeat split. 
            { exact. } 
            { subst m1. simpl;auto. }
            { subst m1. simpl;auto. }
            { apply uniq_intro_elim in oGoal. apply cform_aux_Qty_correct in oGoal. auto. }
          }
        }
      }
      { assert((idb m <> idb m0) \/ (ida m <> ida m0)) as Hnm.
        { rewrite H0 in Hmm. rewrite H1 in Hmm. destruct m. destruct m0. simpl. simpl in Hmm.
          apply nat_tr in Hmm. exact. (*crush_this*) } 
        apply cform_aux_intro0 with (M:=M0)(I:=ids_bid_aux M0) (J:=ids_ask_aux M0) in Hnm.
        unfold cform in H. apply uniq_intro_elim in H. apply Hnm in H.
        assert ((idb m0 =? idb m0) && (ida m0 =? ida m0) = true) as Hms.
        { apply /andP. split. apply /eqP;auto. apply /eqP;auto. (*crush_this*) }
        exists m. assert (In m (cform (m0 :: M0)))  as oGoal.
        { unfold cform. cut (In m (cform_aux (m0 :: M0) (ids_bid_aux (m0 :: M0))
          (ids_ask_aux (m0 :: M0)))). apply uniq_intro_elim.
          simpl. rewrite Hms. 
          destruct (lt_dec (tquantity m0 + Qty M0 (idb m0) (ida m0)) 1 ).
          { destruct m0. simpl in l. assert((tquantity0 <? 1) = false) as Hl.
            auto. move /ltP in Hl. lia. (*crush_this*) } 
          right. exact H. 
        } 
        repeat split. { exact. } { auto. } { auto. }
        { apply uniq_intro_elim in oGoal. apply cform_aux_Qty_correct in oGoal. auto. }
      }
    }
  }
} Qed.


Lemma cform_correct (M:list transaction): CanonicalForm (cform M) M.
Proof.
unfold CanonicalForm. 
repeat split.
 { apply uniq_intro_elim in H. apply cform_aux_Qty_correct in H. auto. }
 { apply cform_correct_I. auto. }
 { apply cform_correct_II. }
 { apply uniq_NoDup. } Qed. 

Lemma included_cannonical_form (T1 T2 : list transaction):
(forall i j, Qty T1 i j = Qty T2 i j) -> included (cform T1) (cform T2).
Proof.
intros. apply included_intro. intros. 
assert(NoDup (cform T1)). unfold cform. eauto. 
apply nodup_count with (x:=a) in H0.
assert(count a (cform T1) =0\/count a (cform T1) =1).
lia. destruct H1. lia. assert(In a (cform T1)).
assert((count a (cform T1) >= 1)). lia. eauto.
apply cform_correct_I in H2. 
destruct H2. replace (Qty T1 (idb a) (ida a)) with 
(Qty T2 (idb a) (ida a)) in H2. 2:{ symmetry;apply H. }
assert(~(Qty T2 (idb a) (ida a) < 1)/\ tquantity a = Qty T2 (idb a) (ida a)).
split. destruct a. simpl. simpl in H2. assert(Ht:=tquantity_cond0).
move /ltP in Ht. lia. lia. apply cform_aux_elim0 in H4. 
assert(In a (cform T2)). unfold cform.
apply uniq_intro_elim in H4. auto. apply countP1 in H5. lia. Qed.

Lemma perm_cannonical_form (T1 T2 : list transaction):
(forall i j, Qty T1 i j = Qty T2 i j) -> perm (cform T1) (cform T2).
Proof. intros. apply (included_cannonical_form) in H as H1.
assert(included (cform T2) (cform T1)). apply included_cannonical_form.
intros. symmetry. auto. unfold perm. apply /andP. split. auto. auto. Qed.


(******************Patch begins here************************)


Lemma QTY_zero_nil (M:list transaction):
(forall i j : nat, 0 = Qty M i j) -> M = nil.
Proof. intros. induction M. auto. simpl in H. specialize (H (idb a)). 
specialize (H (ida a)). destruct ((idb a =? idb a)) eqn:htb;destruct ((ida a =? ida a)) eqn:hta.
simpl in H. destruct a. simpl in H. assert(ht:=tquantity_cond0). move /ltP in ht. lia.
move /eqP in hta. destruct hta. auto. move /eqP in htb. destruct htb. auto. move /eqP in hta. destruct hta. auto. Qed.

Fixpoint delete_idb_M (M:list transaction)(bi:nat):=
match M with
|nil => nil
|m::M' => if idb m =? bi then (delete_idb_M M' bi) else m::(delete_idb_M M' bi)
end.

Lemma delete_idb_M_correct (M:list transaction) (ai bi:nat):
Qty_ask M ai = Qty_ask (delete_idb_M M bi) ai + Qty M bi ai.
Proof. induction M as [|m M0]. simpl. auto. simpl. 
destruct (ida m =? ai) eqn:hai;destruct (idb m =? bi) eqn:hbi.
{ simpl.  rewrite IHM0. lia. }
{ simpl. rewrite hai. rewrite IHM0. lia. }
{ simpl. auto. }
{ simpl. rewrite hai. auto. } Qed.
 
Fixpoint delete_ida_M (M:list transaction)(ai:nat):=
match M with
|nil => nil
|m::M' => if ida m =? ai then (delete_ida_M M' ai) else m::(delete_ida_M M' ai)
end.

Lemma delete_ida_M_correct (M:list transaction) (ai bi:nat):
Qty_bid M bi = Qty_bid (delete_ida_M M ai) bi + Qty M bi ai.
Proof. induction M as [|m M0]. simpl. auto. simpl. 
destruct (ida m =? ai) eqn:hai;destruct (idb m =? bi) eqn:hbi.
{ simpl.  rewrite IHM0. lia. }
{ simpl. rewrite IHM0. lia. }
{ simpl. rewrite hbi. lia. }
{ simpl. rewrite hbi. auto. } Qed.

Lemma Qty_delete_ida_zero (M:list transaction)(ai:nat)(i j : nat):
0 = Qty M i j -> 0 = Qty (delete_ida_M M ai) i j.
Proof. induction M. simpl. auto. simpl. intros. destruct((idb a =? i) && (ida a =? j)) eqn:hi.
destruct a. simpl in H. assert(ht:=tquantity_cond0). move /ltP in ht. lia.
destruct (ida a =? ai) eqn:hai. apply IHM. auto. simpl. rewrite hi. apply IHM. auto. Qed.

Lemma Qty_delete_ida_zero0 (M:list transaction)(i j : nat):
Qty (delete_ida_M M j) i j = 0. 
Proof. induction M. simpl. auto. simpl. destruct (ida a =? j) eqn:h. auto.
simpl. rewrite h. simpl. destruct ((idb a =? i)). simpl. auto. simpl. auto. Qed.

Lemma Qty_delete_ida_lt_len (M:list transaction)(i: nat):(| delete_ida_M M i |) <= (| M |).
Proof. induction M. simpl. auto. simpl. intros. destruct(ida a =? i). lia. simpl. lia. Qed. 

Lemma Qty_delete_idb_zero (M:list transaction)(bi:nat)(i j : nat):
0 = Qty M i j -> 0 = Qty (delete_idb_M M bi) i j.
Proof. induction M. simpl. auto. simpl. intros. destruct((idb a =? i) && (ida a =? j)) eqn:hi.
destruct a. simpl in H. assert(ht:=tquantity_cond0). move /ltP in ht. lia.
destruct (idb a =? bi) eqn:hai. apply IHM. auto. simpl. rewrite hi. apply IHM. auto. Qed.

Lemma Qty_delete_idb_zero0 (M:list transaction)(i j : nat): 
Qty (delete_idb_M M i) i j = 0. 
Proof. induction M. simpl. auto. simpl. destruct (idb a =? i) eqn:h. auto.
simpl. rewrite h. simpl. auto. Qed.

Lemma Qty_delete_idb_lt_len (M:list transaction)(i: nat):(| delete_idb_M M i |) <= (| M |).
Proof. induction M. simpl. auto. simpl. intros. destruct(idb a =? i). lia. simpl. lia. Qed. 

Lemma  Qty_delete_ida_invariant (M:list transaction)(ai:nat)(i j : nat):
ai <> j -> Qty (delete_ida_M M ai) i j = Qty M i j.
Proof. induction M. simpl. auto. simpl. intros.
destruct (ida a =? ai) eqn:h. destruct ((idb a =? i) && (ida a =? j)) eqn:hi.
move /eqP in h. move /andP in hi. destruct hi. move /eqP in H1. subst. destruct H.  auto.
apply IHM. auto. simpl. destruct ((idb a =? i) && (ida a =? j)) eqn:hi. rewrite IHM.
auto.  auto. apply IHM. auto. Qed.

Lemma  Qty_delete_idb_invariant (M:list transaction)(bi:nat)(i j : nat):
bi <> i -> Qty (delete_idb_M M bi) i j = Qty M i j.
Proof. induction M. simpl. auto. simpl. intros.
destruct (idb a =? bi) eqn:h. destruct ((idb a =? i) && (ida a =? j)) eqn:hi.
move /eqP in h. move /andP in hi. destruct hi. move /eqP in H1. subst. destruct H.  auto.
apply IHM. auto. simpl. destruct ((idb a =? i) && (ida a =? j)) eqn:hi. rewrite IHM.
auto.  auto. apply IHM. auto. Qed.

Lemma Qty_delete_ida_M (T1 T2: list transaction)(ai:nat):
(forall i j : nat, Qty T1 i j = Qty T2 i j) ->
(forall i j : nat, Qty (delete_ida_M T1 ai) i j = Qty (delete_ida_M T2 ai) i j).
Proof. intros. specialize (H i). specialize (H j). 
revert T2 H. induction T1 as [|t1 M1].
             { intros. simpl. simpl in H. apply Qty_delete_ida_zero. auto. }
             { intros. simpl. simpl in H. 
             destruct ((idb t1 =? i) && (ida t1 =? j)) eqn:ha;destruct (ida t1 =? ai) eqn:hb.
             move /andP in ha. destruct ha. move /eqP in hb. move /eqP in H1. rewrite hb in H1.
             rewrite H1. rewrite Qty_delete_ida_zero0. symmetry. apply Qty_delete_ida_zero0.
             simpl. rewrite ha. rewrite Qty_delete_ida_invariant. move /andP in ha. destruct ha.
             move /eqP in H1. move /eqP in hb. subst. auto. rewrite Qty_delete_ida_invariant.
             move /andP in ha. destruct ha. move /eqP in H1. move /eqP in hb. subst. auto. auto.
             apply IHM1 in H. auto. simpl. rewrite ha. apply IHM1 in H. auto. } Qed.

Lemma Qty_delete_idb_M (T1 T2: list transaction)(bi:nat):
(forall i j : nat, Qty T1 i j = Qty T2 i j) ->
(forall i j : nat, Qty (delete_idb_M T1 bi) i j = Qty (delete_idb_M T2 bi) i j).
Proof. intros. specialize (H i). specialize (H j). 
revert T2 H. induction T1 as [|t1 M1].
             { intros. simpl. simpl in H. apply Qty_delete_idb_zero. auto. }
             { intros. simpl. simpl in H. 
             destruct ((idb t1 =? i) && (ida t1 =? j)) eqn:ha;destruct (idb t1 =? bi) eqn:hb.
             move /andP in ha. destruct ha. move /eqP in hb. move /eqP in H0. rewrite hb in H0.
             rewrite H0. rewrite Qty_delete_idb_zero0. symmetry. apply Qty_delete_idb_zero0.
             simpl. rewrite ha. rewrite Qty_delete_idb_invariant. move /andP in ha. destruct ha.
             move /eqP in H0. move /eqP in hb. subst. auto. rewrite Qty_delete_idb_invariant.
             move /andP in ha. destruct ha. move /eqP in H0. move /eqP in hb. subst. auto. auto.
             apply IHM1 in H. auto. simpl. rewrite ha. apply IHM1 in H. auto. } Qed.

Lemma Qty_ij_Qty_bid_i_k (k:nat): 
forall T1 T2, |T1| <= k -> ((forall i j, Qty T1 i j = Qty T2 i j) ->
(forall i, Qty_bid T1 i = Qty_bid T2 i)).
Proof. induction k.
  { intros. destruct T1 eqn:HT1. assert(T2=nil). apply QTY_zero_nil. simpl in H0;auto.
    subst. simpl. auto. simpl in H. lia. }
  { intros. destruct T1 as [|t T1'] eqn:HT. assert(T2=nil). apply QTY_zero_nil.
    simpl in H0;auto. subst. simpl. auto. set(a:= ida t). set (M1:=(delete_ida_M T1 a)).
    set (M2:=(delete_ida_M T2 a)). assert((|M1|)<=k). subst M1. subst T1. simpl. subst a.
    destruct (ida t =? ida t) eqn:ht. assert((|T1'|)<=k). simpl in H. lia. 
    assert((| delete_ida_M T1' (ida t) |) <= (| T1' |)). apply Qty_delete_ida_lt_len. lia.
    move /eqP in ht. destruct ht. auto. assert(forall i j : nat, Qty M1 i j = Qty M2 i j).
    apply Qty_delete_ida_M. intros. subst T1. apply H0. apply IHk with (i:=i) in H2 as H3.
    rewrite <- HT. specialize (H0 i) as hi.  specialize (hi a). rewrite <- HT in hi.
    rewrite -> delete_ida_M_correct with (M:=T1)(ai:=a).
    rewrite -> delete_ida_M_correct with (M:=T2)(ai:=a).
    subst M1. subst M2. lia. auto.
  } Qed.

Lemma Qty_ij_Qty_ask_i_k (k:nat): 
forall T1 T2, |T1| <= k -> ((forall i j, Qty T1 i j = Qty T2 i j) ->
(forall i, Qty_ask T1 i = Qty_ask T2 i)).
Proof. induction k.
  { intros. destruct T1 eqn:HT1. assert(T2=nil). apply QTY_zero_nil. simpl in H0;auto.
    subst. simpl. auto. simpl in H. lia. }
  { intros. destruct T1 as [|t T1'] eqn:HT. assert(T2=nil). apply QTY_zero_nil.
    simpl in H0;auto. subst. simpl. auto. set(b:= idb t). set (M1:=(delete_idb_M T1 b)).
    set (M2:=(delete_idb_M T2 b)). assert((|M1|)<=k). subst M1. subst T1. simpl. subst b.
    destruct (idb t =? idb t) eqn:ht. assert((|T1'|)<=k). simpl in H. lia. 
    assert((| delete_idb_M T1' (idb t) |) <= (| T1' |)). apply Qty_delete_idb_lt_len. lia.
    move /eqP in ht. destruct ht. auto. assert(forall i j : nat, Qty M1 i j = Qty M2 i j).
    apply Qty_delete_idb_M. intros. subst T1. apply H0. apply IHk with (i:=i) in H2 as H3.
    rewrite <- HT. specialize (H0 b) as hi.  specialize (hi i). rewrite <- HT in hi.
    rewrite -> delete_idb_M_correct with (M:=T1)(bi:=b).
    rewrite -> delete_idb_M_correct with (M:=T2)(bi:=b).
    subst M1. subst M2. lia. auto.
  } Qed.
  
Lemma cform_aux_Qty (M:list transaction)(m: transaction) (I J:list nat):
In m (cform_aux M I J) -> Qty (uniq (cform_aux M I J)) (idb m) (ida m) = tquantity m.
Proof.
revert M J m. induction I as [| i Bi]. 
{ intros. simpl in H. inversion H. }
{ intros. case J as [|j Ai]. 
    { simpl in H. inversion H. }
    { simpl in H. simpl. destruct (lt_dec (Qty M i j) 1) eqn:Hlt2. 
      { apply IHBi. auto. }
      { destruct H. simpl. dlt1.
        { apply IHBi. move /membP in Hlt. subst m. auto. }
        { simpl. destruct ((i =? idb m) && (j =? ida m)) eqn:Ha.
          cut(Qty (uniq (cform_aux M Bi Ai)) (idb m) (ida m) = 0). subst m. simpl. lia.
          assert( Qty (uniq (cform_aux M Bi Ai)) (idb m) (ida m) = 0\/ 
          Qty (uniq (cform_aux M Bi Ai)) (idb m) (ida m) >0). lia. destruct H0. auto.
          apply Qty_elim in H0. destruct H0 as [m0 H0]. destruct H0. destruct H1.
          apply uniq_intro_elim in H0. apply cform_aux_Qty_correct in H0 as h1.
          assert(m=m0). assert (tquantity m = tquantity m0) as Hxyq. subst m. simpl.
          simpl in H2. simpl in H1. subst. lia.
          assert (ida m = ida m0) as Hxyi. subst m;simpl;auto.
          assert (idb m = idb m0) as Hxyj. subst m;simpl;auto.
          destruct m as [ix jx qx blx], m0 as [iy jy qy bly]; simpl in Hxyq. 
          simpl in Hxyi; simpl in Hxyj; simpl in Hxyq. intros. simpl in Ha. simpl in h1.
          simpl in H1. simpl in H2. clear H0. revert bly. clear H. revert blx.  
          rewrite Hxyi; rewrite Hxyq; rewrite Hxyj.
          intros; f_equal. rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto.
          subst m0. move /membP in Hlt. subst m. destruct (Hlt H0).
          assert((i =? i) && (j =? j)). apply /andP. split. apply /eqP. auto.
          apply /eqP. auto. rewrite <- H in Ha. simpl in Ha. rewrite Ha in H0. inversion H0.
        }
        simpl. dlt1. 
        { rewrite IHBi. eauto. auto. }
        { simpl. destruct ((i =? idb m) && (j =? ida m)) eqn:Ha.
          { match goal with |[ Hlt : context[(memb ?m _ = _)] |- _ ] => set(m':=m) end.
            move /membP in Hlt. move /andP in Ha.  destruct Ha. move /eqP in H0. 
            move /eqP in H1. subst. apply cform_aux_Qty_correct in H as h1. 
            assert(m=m'). assert (tquantity m = tquantity m') as Hxyq. subst m'. simpl. lia.
            assert (idb m = idb m') as Hxyi. subst m'. simpl. lia.
            assert (ida m = ida m') as Hxyj. subst m'. simpl. lia.
            destruct m as [ix jx qx blx], m' as [iy jy qy bly]; simpl in Hxyq. 
            simpl in Hxyi. simpl in Hxyj. revert bly. simpl in n. simpl in Hlt.
            simpl in h1. simpl in Hlt2. clear H. revert blx.
            rewrite Hxyq. rewrite Hxyi. rewrite Hxyj. intros.
            f_equal. rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto.
            rewrite H0 in H. subst m'. destruct (Hlt H). 
          } 
          { apply IHBi. auto. } 
        } 
      } 
    } 
  } 
Qed. 

Lemma cform_Qty (M:list transaction)(m: transaction):
In m (cform M) -> Qty (cform M) (idb m) (ida m) = tquantity m.
Proof. unfold cform. intros. apply cform_aux_Qty. apply uniq_intro_elim. auto. Qed.

Lemma cform_M_Qty (M:list transaction)(i j:nat):
(Qty (cform M) i j = Qty M i j).
Proof. assert(Qty (cform M) i j = Qty M i j\/Qty (cform M) i j < Qty M i j\/Qty (cform M) i j > Qty M i j).
       lia. destruct H. auto. destruct H. assert(Qty M i j>0). lia. apply Qty_elim in H0.
       destruct H0 as [t H0]. destruct H0. destruct H1. subst. apply cform_correct_II in H0.
       destruct H0 as [m H0]. destruct H0. destruct H1. destruct H2. apply cform_Qty in H0.
       rewrite H1. rewrite H2. lia. assert(Qty (cform M) i j>0). lia. apply Qty_elim in H0.
       destruct H0 as [t H0]. destruct H0. destruct H1. subst. apply cform_correct_I in H0 as h1.
       destruct h1 as [ hp h0]. apply cform_Qty in H0. lia. Qed.

Lemma cform_Qty_bid(M: list transaction)(i:nat):
 Qty_bid M i = Qty_bid (cform M) i.
Proof. apply Qty_ij_Qty_bid_i_k with (k:=(|M|)). auto. intros.
symmetry. apply cform_M_Qty. Qed.

Lemma cform_Qty_ask(M: list transaction)(i:nat):
 Qty_ask M i = Qty_ask (cform M) i.
Proof. apply Qty_ij_Qty_ask_i_k with (k:=(|M|)). auto. intros.
symmetry. apply cform_M_Qty. Qed.

(******************Patch ends here************************)


Lemma cform_bids_perm (M1 M2 : list transaction)(B1 B2:list order):
NoDup (ids B1) -> NoDup (ids B2) -> perm B1 B2 -> perm (cform M1) (cform M2) -> perm (bids M1 B1) (bids M2 B2).
Proof. intros NDB1 NDB2. intros. apply perm_intro. intros. unfold bids.
assert(count a (uniq (bids_aux M1 B1 (ids B1))) = 0 \/
count a (uniq (bids_aux M1 B1 (ids B1)))  = 1).
assert(NoDup (uniq (bids_aux M1 B1 (ids B1)))). eauto.
apply nodup_count with (x:=a) in H1. lia.
assert(count a (uniq (bids_aux M2 B2 (ids B2))) = 0 \/
count a (uniq (bids_aux M2 B2 (ids B2)))  = 1). 
assert(NoDup (uniq (bids_aux M2 B2 (ids B2)))). eauto.
apply nodup_count with (x:=a) in H2. lia.
destruct H1;destruct H2. {  lia. } 3:{ lia. }
{
  assert(In a (uniq (bids_aux M2 B2 (ids B2)))). apply countP1b.
  lia. assert(~In a (uniq (bids_aux M1 B1 (ids B1)))). apply countP3.
  auto. apply uniq_intro_elim in H3. 
  assert(~In a (bids_aux M1 B1 (ids B1))).
  intro. apply uniq_intro_elim in H5. destruct(H4 H5).
  clear H4. apply bids_aux_intro0 in H3.
  destruct H5. destruct H3. destruct H4. destruct H5.
  apply bids_aux_elim0. rewrite <- H3. 
  apply perm_Qty_bid with (i:=id a) in H0. 
  rewrite <- cform_Qty_bid with(i:=id a) in H0.
  rewrite <- cform_Qty_bid with(i:=id a) in H0.
  auto.
  rewrite <- H4. apply timeprice_perm. all: auto.
  rewrite <- H5. apply timeprice_perm. all: auto.
  apply ids_perm in H. unfold perm in H. move /andP in H.
  destruct H. eauto.  
}
{
  assert(In a (uniq (bids_aux M1 B1 (ids B1)))). apply countP1b.
  lia. assert(~In a (uniq (bids_aux M2 B2 (ids B2)))). apply countP3.
  auto. apply uniq_intro_elim in H3. 
  assert(~In a (bids_aux M2 B2 (ids B2))).
  intro. apply uniq_intro_elim in H5. destruct(H4 H5).
  clear H4. apply bids_aux_intro0 in H3.
  destruct H5. destruct H3. destruct H4. destruct H5.
  apply bids_aux_elim0. rewrite <- H3.
  apply perm_Qty_bid with (i:=id a) in H0. 
  rewrite <- cform_Qty_bid with(i:=id a) in H0.
  rewrite <- cform_Qty_bid with(i:=id a) in H0.
  auto. rewrite <- H4. apply timeprice_perm. all: auto.
  rewrite <- H5. apply timeprice_perm. all: auto.
  apply ids_perm in H. unfold perm in H. move /andP in H.
  destruct H. eauto.  
} Qed.

Lemma cform_asks_perm (M1 M2 : list transaction)(B1 B2:list order):
NoDup (ids B1) -> NoDup (ids B2) -> 
perm B1 B2 -> perm (cform M1) (cform M2) -> perm (asks M1 B1) (asks M2 B2).
Proof.  intros NDB1 NDB2. intros. apply perm_intro. intros. unfold asks.
assert(count a (uniq (asks_aux M1 B1 (ids B1))) = 0 \/
count a (uniq (asks_aux M1 B1 (ids B1)))  = 1).
assert(NoDup (uniq (asks_aux M1 B1 (ids B1)))). eauto.
apply nodup_count with (x:=a) in H1. lia.
assert(count a (uniq (asks_aux M2 B2 (ids B2))) = 0 \/
count a (uniq (asks_aux M2 B2 (ids B2)))  = 1). 
assert(NoDup (uniq (asks_aux M2 B2 (ids B2)))). eauto.
apply nodup_count with (x:=a) in H2. lia.
destruct H1;destruct H2. {  lia. } 3:{ lia. }
{
  assert(In a (uniq (asks_aux M2 B2 (ids B2)))). apply countP1b.
  lia. assert(~In a (uniq (asks_aux M1 B1 (ids B1)))). apply countP3.
  auto. apply uniq_intro_elim in H3. 
  assert(~In a (asks_aux M1 B1 (ids B1))).
  intro. apply uniq_intro_elim in H5. destruct(H4 H5).
  clear H4. apply asks_aux_intro0 in H3.
  destruct H5. destruct H3. destruct H4. destruct H5.
  apply asks_aux_elim0. rewrite <- H3. 
  apply perm_Qty_ask with (i:=id a) in H0. 
  rewrite <- cform_Qty_ask with(i:=id a) in H0.
  rewrite <- cform_Qty_ask with(i:=id a) in H0.
  auto.
  rewrite <- H4. apply timeprice_perm. all: auto.
  rewrite <- H5. apply timeprice_perm. all: auto.
  apply ids_perm in H. unfold perm in H. move /andP in H.
  destruct H. eauto.  
}
{
  assert(In a (uniq (asks_aux M1 B1 (ids B1)))). apply countP1b.
  lia. assert(~In a (uniq (asks_aux M2 B2 (ids B2)))). apply countP3.
  auto. apply uniq_intro_elim in H3. 
  assert(~In a (asks_aux M2 B2 (ids B2))).
  intro. apply uniq_intro_elim in H5. destruct(H4 H5).
  clear H4. apply asks_aux_intro0 in H3.
  destruct H5. destruct H3. destruct H4. destruct H5.
  apply asks_aux_elim0. rewrite <- H3.
  apply perm_Qty_ask with (i:=id a) in H0. 
  rewrite <- cform_Qty_ask with(i:=id a) in H0.
  rewrite <- cform_Qty_ask with(i:=id a) in H0.
  auto. rewrite <- H4. apply timeprice_perm. all: auto.
  rewrite <- H5. apply timeprice_perm. all: auto.
  apply ids_perm in H. unfold perm in H. move /andP in H.
  destruct H. eauto.  
} Qed.


End CannonicalForm.

Section MSet.

Fixpoint odiff (Omega1 Omega2:list order):(list order).
refine (match Omega1 with
  |nil => nil
  |w1::Omega1' => match (Compare_dec.lt_dec ((oquantity w1) - (quant Omega2 (id w1))) 1) with
    |left _ => odiff Omega1' Omega2
    |right _ => (Mk_order (id w1) (otime w1) ((oquantity w1) - (quant Omega2 (id w1))) (price Omega1 (id w1)) _)::(odiff Omega1' Omega2)
    end
  end).
rewrite PeanoNat.Nat.ltb_nlt. auto.
 Defined.

Lemma odiff_nil (Omega1:list order):
odiff Omega1 nil= Omega1.
Proof. induction Omega1 as [|w1 Omega1']. 
  { simpl. auto. }
  { intros. simpl.
    { destruct (lt_dec (oquantity w1 - 0) 1) eqn:Hlr. destruct w1. 
      assert(H:=oquantity_cond0). simpl in l. move /ltP in H. lia.
      simpl. rewrite IHOmega1'. f_equal. setxy. 
      assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl. lia.
      assert (id x = id y) as Hxyi. crushxyorder1.
        assert (otime x = otime y) as Hxyt. crushxyorder1.
        assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl. 
        destruct (id w1 =? id w1) eqn:op. auto. 
        move /eqP in op. destruct op. auto.   crushxyorder1.
   } } Qed.


Lemma odiff_intro (Omega1 Omega2:list order) (b:order):
quant Omega1 (id b) > quant Omega2 (id b) -> In (id b) (ids (odiff Omega1 Omega2)).
Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. lia. }
  { intros. simpl. simpl in  H.  destruct (id w1 =? id b) eqn: Hb.
    { destruct (lt_dec (oquantity w1 - quant Omega2 (id w1)) 1) eqn:Hlr.
      move /eqP in Hb. rewrite <- Hb in H. lia. simpl. left. move /eqP in Hb;auto.
    }
    { destruct (lt_dec (oquantity w1 - quant Omega2 (id w1)) 1) eqn: Hlr.
      apply IHOmega1'. auto. simpl. right. apply IHOmega1'. auto.
    }
  } Qed.

Lemma odiff_elim (Omega1 Omega2:list order)(b:order): 
In b (odiff Omega1 Omega2) -> NoDup (ids Omega1) -> 
In (id b) (ids Omega1)/\(oprice b = price Omega1 (id b)).

Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. lia. }
  { intros. simpl. simpl in  H.
    destruct (lt_dec (oquantity w1 - quant Omega2 (id w1)) 1) eqn:Hlr.
    { assert ( In (id b) (ids Omega1')). apply IHOmega1' with (Omega2:=Omega2). 
      auto. eauto. split. auto. destruct (id w1 =? id b) eqn:Hb. 
      move /eqP in Hb. simpl in H0;rewrite Hb in H0. 
      assert(~In (id b) (ids Omega1')). eauto. destruct (H2 H1).
      apply IHOmega1' in H. apply H. eauto. }
    { destruct H. subst b;simpl. assert(id w1 =? id w1 = true). 
      apply /eqP. auto. rewrite H. split. auto. auto.
      assert ( In (id b) (ids Omega1')). apply IHOmega1' with 
      (Omega2:=Omega2). auto. eauto.  split. auto. 
      destruct (id w1 =? id b) eqn:Hb. move /eqP in Hb. 
      simpl in H0;rewrite Hb in H0. assert(~In (id b) (ids Omega1')). 
      eauto. destruct (H2 H1). apply IHOmega1' in H. apply H. eauto. } } Qed. 
  
  
Lemma odiff_elim2 (Omega1 Omega2:list order)(b:order): 
~In (id b) (ids Omega1) ->  NoDup (ids Omega1) -> 
odiff Omega1 (b::Omega2) = odiff Omega1 Omega2.
Proof.  revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. destruct (id b =? id w1) eqn: Hb.
    { move /eqP in Hb. destruct H.  simpl. left. auto. }
    { dlt1. 
      { apply IHOmega1'. intro.  destruct H.  simpl. 
      right. auto. eauto. }
      { f_equal. apply IHOmega1'. intro.  destruct H.  simpl. 
      right. auto. eauto. 
      }
    }
  } Qed.
  
Lemma odiff_elim3 (Omega1 Omega2:list order): 
(forall i, In i (ids Omega2) -> ~In i (ids Omega1)) ->  NoDup (ids Omega1) -> 
 odiff Omega1 Omega2 = Omega1.
Proof.  revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. specialize (H (id w1)) as Hi. simpl in Hi. 
    assert(In (id w1) (ids Omega2)\/~In (id w1) (ids Omega2)).
    eauto. destruct H1. apply Hi in  H1. destruct H1. auto.
    apply quant_elim in H1. dlt1. 
    { assert(Hl:=l). rewrite H1 in Hl.
      destruct w1. simpl in Hl. assert(Hw:=oquantity_cond0).
      move /ltP in Hw. lia.
    }
    { rewrite IHOmega1'. intros. intro.
      firstorder. eauto. f_equal. setxy.
      assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl. lia.
      assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
      assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
      assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.
      eq1. crushxyorder1. }} Qed. 
  
Lemma odiff_elim4 (Omega1 Omega2:list order)(b:order): 
quant Omega2 (id b) >= oquantity b ->  NoDup (ids Omega1) -> 
odiff (b::Omega1) Omega2 = odiff Omega1 Omega2.
Proof. simpl. intros. dlt1. auto. lia. Qed. 


Lemma odiff_included_timesof (Omega1 Omega2:list order): 
included (timesof (odiff Omega1 Omega2)) (timesof Omega1).
Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. dlt1. specialize (IHOmega1' Omega2).
    eauto. simpl. destruct (otime w1 =? otime w1) eqn:Hw1. simpl. auto.
    move /eqP in Hw1. destruct Hw1. auto. } Qed. 

Lemma odiff_notIn_timesof12 (Omega1 Omega2:list order)(t:nat): 
~In t (timesof Omega1) -> ~In t (timesof (odiff Omega1 Omega2)).
Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. dlt1. specialize (IHOmega1' Omega2).
    simpl in H. apply in_inv4 in H. destruct H.  
    apply IHOmega1'. eauto.
    simpl. simpl in H. apply in_inv4 in H. destruct H.  
     intro. destruct H1. lia. eapply IHOmega1' with (Omega2:=Omega2) in H.
     destruct (H H1). } Qed. 


Lemma odiff_nodup_timesof (Omega1 Omega2:list order): 
NoDup (timesof Omega1) -> NoDup (timesof (odiff Omega1 Omega2)).
Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. dlt1. specialize (IHOmega1' Omega2). 
    apply IHOmega1'. eauto.
    simpl. constructor.  apply odiff_notIn_timesof12. 
    eauto. apply IHOmega1'. eauto. } Qed. 
    
Lemma odiff_included_ids (Omega1 Omega2:list order): 
included (ids (odiff Omega1 Omega2)) (ids Omega1).
Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. dlt1. specialize (IHOmega1' Omega2).
    eauto. simpl. destruct (id w1 =? id w1) eqn:Hw1. simpl. auto.
    move /eqP in Hw1. destruct Hw1. auto. } Qed.

Lemma odiff_notIn_ids12 (Omega1 Omega2:list order)(i:nat): 
~In i (ids Omega1) -> ~In i (ids (odiff Omega1 Omega2)).
Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. dlt1. specialize (IHOmega1' Omega2).
    simpl in H. apply in_inv4 in H. destruct H.  
    apply IHOmega1'. eauto.
    simpl. simpl in H. apply in_inv4 in H. destruct H.  
     intro. destruct H1. lia. eapply IHOmega1' with (Omega2:=Omega2) in H.
     destruct (H H1). } Qed.
     
Lemma odiff_nodup_ids (Omega1 Omega2:list order): 
NoDup (ids Omega1) -> NoDup (ids (odiff Omega1 Omega2)).
Proof.  revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. auto. }
  { intros. simpl. dlt1. specialize (IHOmega1' Omega2). 
    apply IHOmega1'. eauto.
    simpl. constructor.  apply odiff_notIn_ids12. 
    eauto. apply IHOmega1'. eauto. } Qed. 

Lemma odiff_price_invariance (Omega1 Omega2: list order)(b:order):
NoDup (ids Omega1) -> In b (odiff Omega1 Omega2) -> 
(oprice b = price Omega1 (id b)).
Proof. revert Omega2. induction Omega1 as [|w1 Omega1']. 
  { simpl. intros. inversion H0. }
  { intros. simpl. simpl in  H0.
    { destruct (lt_dec (oquantity w1 - quant Omega2 (id w1)) 1) eqn:Hlr.
      destruct (id w1 =? id b) eqn:Hb. move /eqP in Hb.
      apply odiff_elim in H0. destruct H0.
      simpl in H. rewrite Hb in H. assert(~In (id b) (ids Omega1')). eauto.
      destruct (H2 H0).  eauto. apply odiff_elim in H0. destruct H0.
      auto. eauto.
      destruct H0. subst b. simpl. auto.
      destruct (id w1 =? id b) eqn:Hb. move /eqP in Hb.
      apply odiff_elim in H0. destruct H0.
      simpl in H. rewrite Hb in H. assert(~In (id b) (ids Omega1')). eauto.
      destruct (H2 H0).  eauto. apply odiff_elim in H0. destruct H0.
      auto. eauto.
    }
  } Qed.

Lemma odiff_exists (Omega1 Omega2: list order)(i:nat):
In i (ids (odiff Omega1 Omega2)) -> NoDup (ids Omega1)  -> 
(exists b, In b ((odiff Omega1 Omega2))/\(id b = i)/\
(oprice b = price Omega1 i)).
Proof. intros. apply ids_elim  in H. destruct H. exists x. split.
       apply H. split. apply H. destruct H. subst i. 
       apply odiff_price_invariance with (Omega2:=Omega2). auto. auto. Qed.

Lemma odiff_correct1 (Omega1 Omega2: list order)(w:order):
NoDup (ids Omega1) -> In w (odiff Omega1 Omega2) -> 
In (id w) (ids Omega1) /\
(otime w) = (timestamp Omega1 (id w)) /\
oprice w = (price Omega1 (id w)) /\
oquantity w = quant Omega1 (id w) - (quant Omega2 (id w)).
Proof. revert w Omega2. induction Omega1. simpl. intros.
inversion H0. simpl. intros.
dlt1. 
{ destruct(lt_dec (oquantity a - quant Omega2 (id a)) 1 ) eqn:Hl.
{ move /eqP in Hlt. rewrite Hlt in H. assert(~In (id w) (ids Omega1)).
eauto. apply odiff_elim in H0. destruct H0.
destruct (H1 H0). eauto.
}
{ move /eqP in Hlt. destruct H0. repeat split. auto.
  subst w. simpl. auto. subst w. simpl.
  destruct (id a =? id a) eqn:Hp. auto.
  move /eqP in Hp. destruct Hp. auto. subst w. simpl. auto.
  rewrite Hlt in H. assert(~In (id w) (ids Omega1)). eauto.
  apply odiff_elim in H0. destruct H0.
  destruct (H1 H0). eauto.
} }
{ destruct(lt_dec (oquantity a - quant Omega2 (id a)) 1 ) eqn:Hl.
{ apply IHOmega1 in H0. destruct H0. destruct H1.
  destruct H2. repeat split. all:auto. eauto.
}
{ move /eqP in Hlt. destruct H0. subst w.
  simpl in Hlt. destruct Hlt. auto.
  apply IHOmega1 in H0. destruct H0. destruct H1.
  destruct H2. repeat split. all:auto. eauto.
} } Qed.

Lemma odiff_correct2 (Omega1 Omega2: list order)(w:order):
NoDup (ids Omega1) ->
In (id w) (ids Omega1) ->
(otime w) = (timestamp Omega1 (id w)) ->
oprice w = (price Omega1 (id w)) ->
oquantity w = quant Omega1 (id w) - (quant Omega2 (id w))
 -> In w (odiff Omega1 Omega2).
Proof. revert w Omega2. induction Omega1. simpl. intros.
inversion H0. simpl. intros.
destruct H0. {
destruct (id a =? id w) eqn:Ha.
{ dlt1. assert(Hl:=l). rewrite H0 in Hl. rewrite <- H3 in Hl.
  ltqo. simpl. left.
  setxy. 
 assert (oquantity x = oquantity y) as Hxyq. subst x. subst y. simpl.
        rewrite <- H0 in H3. lia.
        assert (id x = id y) as Hxyi. subst x;subst y. simpl. lia.
        assert (otime x = otime y) as Hxyt. subst x. subst y. simpl. lia.
        assert (oprice x = oprice y) as Hxyp. subst x. subst y. simpl.
        destruct (id a =? id a) eqn:Hb. lia. move /eqP in Hb. destruct Hb. auto.
        crushxyorder1.
}
{ move /eqP in Ha. destruct Ha. auto. }
}
{ destruct (id a =? id w) eqn:Ha. 
{ dlt1. assert(Hl:=l). move /eqP in Ha. rewrite Ha in Hl. rewrite <- H3 in Hl.
  ltqo. simpl. left.
  setxy. 
 assert (oquantity x = oquantity y) as Hxyq. subst x. subst y. simpl.
        move /eqP in Ha. rewrite <- Ha in H3. lia.
        assert (id x = id y) as Hxyi. subst x;subst y. simpl. 
        move /eqP in Ha. lia.
        assert (otime x = otime y) as Hxyt. subst x. subst y. simpl. lia.
        assert (oprice x = oprice y) as Hxyp. subst x. subst y. simpl.
        destruct (id a =? id a) eqn:Hb. lia. move /eqP in Hb. destruct Hb. auto.
        crushxyorder1.
 }
{  dlt1. apply IHOmega1. eauto. auto. auto. auto. auto. simpl.
right.  apply IHOmega1. eauto. auto. auto. auto. auto. }
} Qed.


Lemma ndp_ids_order (B:list order) :
NoDup (ids B) -> NoDup B.
Proof. induction B. simpl. auto. simpl. intros.
constructor. intro. apply ids_intro in H0. assert(~In (id a) (ids B)). eauto.
destruct(H1 H0). apply IHB. eauto. Qed.

Lemma odiff_perm (B1 B2 B1' B2': list order):
NoDup (ids B1) -> NoDup (ids B1') -> perm B1 B2 -> perm B1' B2' -> 
perm (odiff B1 B1') (odiff B2 B2').
Proof. intros. apply perm_intro. intros. 
       assert(NoDup (ids B2)).
       apply ids_perm in H1. eauto. 
       assert(NoDup (odiff B1 B1')).
       apply ids_perm in H1.
       apply odiff_nodup_ids with (Omega2 := B1') in H.
       apply ndp_ids_order. eauto.
       assert(NoDup (odiff B2 B2')). 
       assert(NoDup (odiff B2 B2')). apply ids_perm in H2.
       apply odiff_nodup_ids with (Omega2 := B2') in H3.
       apply ndp_ids_order. eauto. auto.
       assert(count a (odiff B1 B1')<=1). 
       eauto. assert(count a (odiff B2 B2')<=1). eauto. 
       assert(count a (odiff B1 B1') =0 \/count a (odiff B1 B1') =1). lia.
       assert(count a (odiff B2 B2') =0 \/count a (odiff B2 B2') =1). lia.
       destruct H8;destruct H9.
       { lia. } 3:{ lia. }
       { assert(~In a (odiff B1 B1')). eauto. 
         assert(In a (odiff B2 B2')).  apply countP1b. lia.
         apply odiff_correct1 in H11. destruct H11.
         destruct H12. destruct H13.
         destruct H10. apply odiff_correct2. eauto. 
         apply ids_perm in H1. unfold perm in H1. move /andP in H1. 
         destruct H1. eauto.
         rewrite H12. apply timeprice_perm. eauto. auto. auto. 
         rewrite H13. apply timeprice_perm. eauto. auto. auto. 
         rewrite H14. assert(quant B2 (id a) = quant B1 (id a)).
         apply quant_perm. auto. auto. auto. 
         assert(quant B2' (id a) = quant B1' (id a)).
         apply quant_perm. auto. apply ids_perm in  H2. eauto.
         auto.  lia. eauto.
       }
       { assert(~In a (odiff B2 B2')). eauto. 
         assert(In a (odiff B1 B1')).  apply countP1b. lia.
         apply odiff_correct1 in H11. destruct H11.
         destruct H12. destruct H13.
         destruct H10. apply odiff_correct2. eauto. 
         apply ids_perm in H1. unfold perm in H1. move /andP in H1. 
         destruct H1. eauto. rewrite H12. apply timeprice_perm. eauto. auto. auto. 
         rewrite H13. apply timeprice_perm. eauto. auto. auto. 
         rewrite H14. assert(quant B2 (id a) = quant B1 (id a)).
         apply quant_perm. auto. auto. auto. 
         assert(quant B2' (id a) = quant B1' (id a)).
         apply quant_perm. auto. auto. apply ids_perm in  H2. eauto. eauto. lia. auto.
       } Qed.     

End MSet.
