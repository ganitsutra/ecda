
(*--------------------------------------*)
(*--This file contains proofs of the ---*)
(*-----------Maximum Theorem:-----------*)
(*----and lemmas required to prove it---*)
(*--------------------------------------*)



Require Import Definitions Properties.

Set Implicit Arguments.

Section Matching.

Definition MaxMatch (M: list transaction) (B A: list order):=
forall M', Matching M' B A -> Matching M B A -> (Vol M') <= (Vol M).

Lemma Matching_over (M: list transaction) (B A: list order): Matching M B A ->
forall t : transaction, In t M -> over t B A.
Proof. unfold Matching. unfold Tvalid. unfold valid. intros. destruct H.
       unfold over. apply H in H0. destruct H0. destruct H0. exists x. 
       exists x0. repeat split. all: apply H0. Qed.

Lemma anot_matchable_tradable (B A: list order)(b :order):~ matchable B A ->
~ (exists a : order, In a A -> tradable b a) -> ~matchable (b::B) A.
Proof. unfold matchable. intros. intro. destruct H1. destruct H1. simpl in H1.
destruct H1. destruct H2. destruct H2. { subst x. destruct H0. exists x0. auto. }
{ destruct H. exists x. exists x0. auto. } Qed. 

Lemma bnot_matchable_tradable (B A: list order)(a :order): ~ matchable B A -> 
~ (exists b : order, In b B -> tradable b a) -> ~matchable B (a::A).
Proof. unfold matchable. intros. intro. destruct H1. destruct H1. simpl in H1.
destruct H1. destruct H2. destruct H1. { subst. destruct H0. exists x. auto. }
{ destruct H. exists x. exists x0. auto. } Qed. 

Lemma not_matchable_delete (B A: list order)(b a :order): ~matchable B A ->
~matchable (delete_order B (id b)) (delete_order A (id a)).
Proof. intros H H0. unfold matchable in H0. destruct H0 as [b0 H0].
       destruct H0 as [a0 H0]. destruct H0 as [H1 H2]. destruct H2 as [H2 H3].
       assert(In  b0 B). eapply delete_order_intro. exact H2. 
       assert(In  a0 A). eapply delete_order_intro. exact H1. destruct H.
       unfold matchable. exists b0. exists a0. auto. Qed.

Lemma not_matchable_matching_nil (M: list transaction) (B A: list order):
~matchable B A -> Matching M B A -> M=nil.
Proof. intros. destruct H0. unfold Tvalid in H0. unfold valid in H0.
       destruct M eqn:HM. auto. assert(In t (t::l)). auto.  apply 
       H0 in H2.  destruct H2. destruct H2. destruct H2. destruct H3.
       destruct H4. destruct H5. destruct H6. unfold matchable in H.
       destruct H. exists x. exists x0. auto. Qed.

Lemma not_matchable_perm_invariance (A A' B B': list order):
not (matchable B A) -> perm B B' -> perm A A' -> not (matchable B' A').
Proof. intros. unfold perm in H0. unfold perm in H1. move /andP in H0.
       move /andP in H1. destruct H0. destruct H1. intro. destruct H.
       unfold matchable. unfold matchable in H4. firstorder. exists x.
       exists x0. repeat split. eauto. eauto. auto. Qed.

Lemma Maching_perm (A1 A2 B1 B2: list order)(M1 M2: list transaction):
perm B1 B2 -> perm A1 A2 -> Matching M1 B1 A1 -> Matching M2 B2 A2 ->
Matching M2 B1 A1.
Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0.
       repeat split. { intros. apply H2 in H5. destruct H5 as [b0 H5]. 
       destruct H5 as [a0 H5]. exists b0. exists a0.  destruct H5. 
       destruct H6. split. eauto. split. eauto. auto. } { intros. 
       apply H2. eauto.  } { intro. intro. apply H2. eauto. } Qed.

Lemma Maching_perm_wB (A1 A2 B1 B2: list order)(M1 M2: list transaction)(w:order):
perm B1 B2 -> perm A1 A2 -> Matching M2 (w :: B2) A2 -> Matching M2 (w :: B1) A1.
Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0. repeat 
       split. { intros. apply H1 in H4. destruct H4 as [b0 H4]. destruct H4
       as [a0 H4]. exists b0. exists a0.  destruct H4. destruct H5. split.
       eauto. split. destruct H5. simpl. auto. simpl. right. eauto. auto. }
       { intros. apply H1. destruct H4. subst. auto. eauto. } { intro. intro.
       apply H1. eauto. } Qed.
       
Lemma Maching_perm_wA (A1 A2 B1 B2: list order)(M1 M2: list transaction)(w:order):
perm B1 B2 -> perm A1 A2 -> Matching M2 B2 (w::A2) -> Matching M2 B1 (w::A1).
Proof. unfold perm. unfold Matching. unfold Tvalid. unfold valid. intros.
       move /andP in H. destruct H. move /andP in H0. destruct H0. repeat split.
       { intros. apply H1 in H4. destruct H4 as [b0 H4]. destruct H4 as 
       [a0 H4]. exists b0. exists a0.  destruct H4. destruct H5. split. 
       destruct H4. simpl. auto. simpl. right. eauto. split. eauto. auto. }
       { intros. apply H1. eauto. }  { intro. intros. destruct H4. subst. 
       apply H1. auto. apply H1. simpl. right. eauto. } Qed.

Lemma insert_order_transaction_bid (M: list transaction) (B A: list order) (b:order):
~matchable B A -> Matching M (b::B) A -> (forall t, In t M -> idb t = id b).
Proof. intros.  destruct H0. unfold Tvalid in H0. unfold valid in H0. destruct M
       eqn:HM. auto. assert(In t (t::l)). auto.  apply H0 in H1. destruct H1.
       destruct H1. destruct H1. destruct H4. destruct H5. destruct H6. simpl 
       in H4. destruct H4. { subst x. auto. } { unfold matchable in H. destruct H.
       exists x. exists x0. destruct H7. auto. } Qed.

Lemma insert_order_transaction_ask (M: list transaction) (B A: list order) (a:order):
~matchable B A -> Matching M B (a::A) -> (forall t, In t M -> ida t = id a).
Proof. intros.  destruct H0. unfold Tvalid in H0. unfold valid in H0. 
       destruct M eqn:HM. auto. assert(In t (t::l)). auto.  apply H0 in H1. 
       destruct H1. destruct H1. destruct H1. destruct H4. destruct H5. destruct H6.
       simpl in H1. destruct H1. { subst x0. auto. }  { unfold matchable in H.
       destruct H. exists x. exists x0. destruct H7. auto. } Qed.

Lemma insert_order_t_Q_le_bid_aux1 (M: list transaction) (b:order) :
(forall t, In t M-> idb t = id b) -> Qty_bid M (id b) = Vol M.
Proof. induction M. simpl. auto. intros. simpl. destruct(Nat.eqb (idb a)
       (id b)) eqn:Ht. specialize (H a) as H2. simpl in H2. cut(Qty_bid M
       (id b) = Vol M). lia. apply IHM. intros. move /eqP in Ht. 
       specialize (H t) as H3. simpl in H3. destruct H3. auto. auto.
       specialize (H a) as H2. simpl in H2. destruct H2. auto. 
       move /eqP in Ht. destruct Ht. auto. Qed.

Lemma insert_order_t_Q_le_ask_aux1 (M: list transaction) (b:order) :
(forall t, In t M-> ida t = id b) -> Qty_ask M (id b) = Vol M.
Proof. induction M. simpl. auto. intros. simpl. 
       destruct(Nat.eqb (ida a) (id b)) eqn:Ht. specialize (H a) as H2.
       simpl in H2. cut(Qty_ask M (id b) = Vol M). lia. apply IHM. 
       intros. move /eqP in Ht. specialize (H t) as H3. simpl in H3. 
       destruct H3. auto. auto. specialize (H a) as H2. simpl in H2.
       destruct H2. auto. move /eqP in Ht. destruct Ht. auto. Qed.

Lemma insert_order_t_Q_le_bid_aux2 (M: list transaction) (b:order) :
(forall t, In t M -> idb t = id b) -> Qty_bid M (id b) <= oquantity b
-> Vol M <= oquantity b. intros.
Proof. intros. replace (Vol M) with (Qty_bid M (id b)). induction M 
       as [|m0 M]. simpl;auto. simpl. simpl in H0. 
       destruct(Nat.eqb (idb m0) (id b)) eqn:Ht. auto. auto. 
       apply insert_order_t_Q_le_bid_aux1. auto. Qed.

Lemma insert_order_t_Q_le_ask_aux2 (M: list transaction) (b:order) :
(forall t, In t M -> ida t = id b) -> Qty_ask M (id b) <= oquantity b
-> Vol M <= oquantity b. intros.
Proof. intros. replace (Vol M) with (Qty_ask M (id b)). induction M 
       as [|m0 M]. simpl;auto. simpl. simpl in H0. 
       destruct(Nat.eqb (idb m0) (id b)) eqn:Ht. auto. auto.
       apply insert_order_t_Q_le_ask_aux1. auto. Qed.


Lemma insert_order_t_Q_le_bid (M: list transaction) (B A: list order) (b:order):
~matchable B A -> Matching M (b::B) A -> (Vol M) <= (oquantity b).
Proof. intros. assert((forall t, In t M -> idb t = id b)). intros.
       eapply insert_order_transaction_bid. exact H. exact H0. auto.
       destruct H0. unfold Tvalid in H0. unfold valid in H0. destruct H2.
       assert(In b (b::B)).  auto.  specialize (H2 b). 
       apply insert_order_t_Q_le_bid_aux2. apply H1. auto. Qed.

Lemma insert_order_t_Q_le_ask (M: list transaction) (B A: list order) (a:order):
~matchable B A -> Matching M B (a::A) -> (Vol M) <= (oquantity a).
Proof.  intros. assert((forall t, In t M -> ida t = id a)). intros. 
        eapply insert_order_transaction_ask. exact H. exact H0. auto.
        destruct H0. unfold Tvalid in H0. unfold valid in H0. destruct H2.
        assert(In a (a::A)).  auto.  specialize (H2 a). 
        apply  insert_order_t_Q_le_ask_aux2. apply H1. auto. Qed.


Lemma insert_order_Qle_id_of_b_in_Bhat_aux2 (M: list transaction) (B A: list order) (b:order):
NoDup (ids B)-> In b B -> Matching M B A -> Vol M < oquantity b -> 
In (id b) (ids (odiff B (bids M B))). intros.
Proof. intros. apply odiff_intro. replace (quant B (id b)) with 
       (oquantity b). replace (quant (bids M B) (id b)) with (Qty_bid M (id b)).
       assert(Vol M >= Qty_bid M (id b)). apply Q_vs_Qty_bid. lia. symmetry.
       apply bids_id_quant. auto. apply ids_intro. auto. symmetry. 
       apply quant_elim1. auto. Qed.

Lemma insert_order_Qle_id_of_a_in_Ahat_aux2 (M: list transaction) (B A: list order) (a:order):
NoDup (ids A)-> In a A -> Matching M B A -> Vol M < oquantity a -> 
In (id a) (ids (odiff A (asks M A))). 
Proof. intros. apply odiff_intro. replace (quant A (id a)) with 
       (oquantity a). replace (quant (asks M A) (id a)) with (Qty_ask M (id a)).
       assert(Vol M >= Qty_ask M (id a)). apply Q_vs_Qty_ask. lia. symmetry.
       apply asks_id_quant. auto. apply ids_intro. auto.
       symmetry. apply quant_elim1. auto. Qed.

Lemma insert_order_Qle_id_of_b_in_Bhat 
(M: list transaction) (B A: list order) (b:order):
NoDup (ids (b :: B)) -> ~matchable B A -> Matching M (b::B) A -> 
(Vol M) < (oquantity b) -> In (id b) (ids (odiff (b::B) (bids M (b::B)))).
Proof. intros. apply insert_order_Qle_id_of_b_in_Bhat_aux2 with (A:=A). all: auto. Qed.

Lemma insert_order_Qle_id_of_a_in_Ahat (M: list transaction) (B A: list order) (a:order):
NoDup (ids (a :: A)) -> ~matchable B A -> Matching M B (a::A)-> 
(Vol M) < (oquantity a) -> In (id a) (ids (odiff (a::A) (asks M (a::A)))).
Proof. intros. apply insert_order_Qle_id_of_a_in_Ahat_aux2 with (B:=B). all: auto. Qed.

Lemma QM1_gt_QM2_extra_bid_in_M1_aux1 (M1 M2: list transaction):
(Vol M1)>(Vol M2) -> 
(exists i, (In i (ids_bid_aux M1))/\(Qty_bid M1 i) > Qty_bid M2 i).
Proof. intro. assert(subset (fun_ids_bid M1) (fun_ids_bid M2)
        \/~subset (fun_ids_bid M1) (fun_ids_bid M2)). eauto. destruct H0.
       replace (Vol M1) with (Q_by_bids M1) in H. replace (Vol M2) with 
       (Q_by_bids M2) in H. intros.  unfold Q_by_bids in H.
       assert(Q_by_bids_aux M2 (fun_ids_bid M2) >= Q_by_bids_aux M2 (fun_ids_bid M1)).
       apply Q_by_bids_aux_subset_I1_I2. unfold fun_ids_bid. eauto.
       unfold fun_ids_bid. eauto. auto. assert(Q_by_bids_aux M1 (fun_ids_bid M1) >
       Q_by_bids_aux M2 (fun_ids_bid M1)). lia. apply Q_by_bids_aux_T1_T2 in H2.
       destruct H2 as [i H2]. destruct H2. exists i. split.  unfold fun_ids_bid in H2.
       apply uniq_intro_elim. auto. auto. symmetry. apply Q_Qty_bid. 
       symmetry;apply Q_Qty_bid. assert(exists i, In i (fun_ids_bid M1)/\~In i
       (fun_ids_bid M2)). apply no_subset_existsA. auto. destruct H1 as [i H1].
       exists i. destruct H1. split. apply uniq_intro_elim. auto.
       assert(Qty_bid M2 i = 0). apply Qty_bid_t_zero. intro. apply uniq_intro_elim
       in H3. eauto. rewrite H3. apply ids_bid_intro0. apply uniq_intro_elim;auto.
       Qed.

Lemma QM1_gt_QM2_extra_bid_in_M1 (M1 M2: list transaction) (B A: list order):
Matching M1 B A ->Matching M2 B A -> (Vol M1)>(Vol M2) ->
(exists b, (In b B)/\(Qty_bid M1 (id b)) > 
Qty_bid M2 (id b)/\(exists t, In t M1/\(idb t = id b))).
Proof. intros. apply QM1_gt_QM2_extra_bid_in_M1_aux1 in H1.
       destruct H1. destruct H1. apply ids_bid_aux_intro1 in H1 as H3.
       destruct H3. destruct H. unfold Tvalid in H.
       destruct H3. apply H in H3 as H3m. unfold valid in H3m. destruct H3m.
       destruct H6. exists x1. split. apply H6. split. replace (id x1) with (x).
       auto. subst x. apply H6. exists x0. split.  auto. apply H6. Qed.

Lemma QM1_gt_QM2_extra_ask_in_M1_aux1 (M1 M2: list transaction):
(Vol M1)>(Vol M2) -> 
(exists i, (In i (ids_ask_aux M1))/\(Qty_ask M1 i) > Qty_ask M2 i).
Proof. intro. assert(subset (fun_ids_ask M1) (fun_ids_ask M2)
       \/~subset (fun_ids_ask M1) (fun_ids_ask M2)). eauto.
       destruct H0. replace (Vol M1) with (Q_by_asks M1) in H. 
       replace (Vol M2) with (Q_by_asks M2) in H. intros.  unfold Q_by_asks in H.
       assert(Q_by_asks_aux M2 (fun_ids_ask M2) >= Q_by_asks_aux M2 (fun_ids_ask M1)).
       apply Q_by_asks_aux_subset_I1_I2. unfold fun_ids_ask. eauto. unfold
       fun_ids_ask. eauto. auto. assert(Q_by_asks_aux M1 (fun_ids_ask M1) >
       Q_by_asks_aux M2 (fun_ids_ask M1)). lia. apply Q_by_asks_aux_T1_T2 in H2.
       destruct H2 as [i H2]. destruct H2. exists i. split.  unfold fun_ids_ask in H2.
       apply uniq_intro_elim. auto. auto. symmetry;apply Q_Qty_ask. 
       symmetry;apply Q_Qty_ask. assert(exists i, In i (fun_ids_ask M1)/\
       ~In i (fun_ids_ask M2)). apply no_subset_existsA. auto. destruct H1 as [i H1].
       exists i. destruct H1. split. apply uniq_intro_elim. auto.
       assert(Qty_ask M2 i = 0). apply Qty_ask_t_zero. intro. apply uniq_intro_elim
       in H3. eauto. rewrite H3. apply ids_ask_intro0. apply uniq_intro_elim;auto.
       Qed.

Lemma QM1_gt_QM2_extra_ask_in_M1 (M1 M2: list transaction) (B A: list order):
Matching M1 B A ->Matching M2 B A -> (Vol M1)>(Vol M2) ->
(exists a, (In a A)/\(Qty_ask M1 (id a)) > Qty_ask M2 (id a)/\(exists t, In t M1/\(ida t = id a))).
Proof. intros. apply QM1_gt_QM2_extra_ask_in_M1_aux1 in H1.
       destruct H1. destruct H1. apply ids_ask_aux_intro1 in H1 as H3.
       destruct H3. destruct H. unfold Tvalid in H.
       destruct H3. apply H in H3 as H3m. unfold valid in H3m. destruct H3m.
       destruct H6. exists x2. split. apply H6. split. replace (id x2) with (x).
       auto. subst x. apply H6. exists x0. split.  auto. apply H6. Qed.



Lemma QM1_eq_QM2_extra_bid_in_M1 (M1 M2: list transaction)(i:nat):
Vol M1 = Vol M2 -> Qty_bid M1 i > Qty_bid M2 i -> exists i' : nat, Qty_bid M1 i' < Qty_bid M2 i'. 
Proof. replace (Vol M1) with (Q_by_bids M1).
       replace (Vol M2) with (Q_by_bids M2).
       intros.  unfold Q_by_bids in H.  
       assert(Q_by_bids_aux M1 (fun_ids_bid M1) = Q_by_bids_aux M2 (fun_ids_bid M1)\/
       Q_by_bids_aux M1 (fun_ids_bid M1) > Q_by_bids_aux M2 (fun_ids_bid M1)\/
       Q_by_bids_aux M1 (fun_ids_bid M1) < Q_by_bids_aux M2 (fun_ids_bid M1)). lia. 
       destruct H1. assert(In i(fun_ids_bid M1)\/~In i(fun_ids_bid M1)).
       eauto. destruct H2. apply Q_by_bids_aux_T_i_In_I with (T:=M1) in H2 as Ha1.
       rewrite Ha1 in H1. apply Q_by_bids_aux_T_i_In_I with (T:=M2) in H2 as Ha2.
       rewrite Ha2 in H1. assert(Q_by_bids_aux M1 (delete i (fun_ids_bid M1)) <
       Q_by_bids_aux M2 (delete i (fun_ids_bid M1))). lia. 
       apply Q_by_bids_aux_T1_T2 in H3.
       destruct H3. destruct H3. exists x. lia. unfold not in H2.
       assert(Qty_bid M1 i = 0). apply Qty_bid_t_zero. intro.
       apply uniq_intro_elim in H3. eauto. lia.
       destruct H1. 2:{ apply Q_by_bids_aux_T1_T2 in H1. destruct H1.
       destruct H1. exists x. lia. }
       rewrite H in H1.
       assert(Subset (fun_ids_bid M2) (fun_ids_bid M1)
       \/~Subset (fun_ids_bid M2) (fun_ids_bid M1)). eauto.
       destruct H2.  assert(Q_by_bids_aux M2 (fun_ids_bid M1) >= 
       Q_by_bids_aux M2 (fun_ids_bid M2) ). eapply Q_by_bids_aux_subset_I1_I2 in H2. 
       exact H2. unfold fun_ids_bid. eauto. unfold fun_ids_bid. eauto. lia.
       assert(exists i, In i (fun_ids_bid M2)/\~In i (fun_ids_bid M1)).
       apply no_subset_existsA. auto. destruct H3. exists x. destruct H3. 
       assert(Qty_bid M1 x = 0).  apply Qty_bid_t_zero. intro. 
       apply uniq_intro_elim in H3. apply uniq_intro_elim in H5.
       destruct H4. auto. 
       apply uniq_intro_elim in H3. apply ids_bid_intro0 in H3.
       lia. symmetry;apply Q_Qty_bid. symmetry;apply Q_Qty_bid. Qed.


Lemma QM1_eq_QM2_extra_ask_in_M1 (M1 M2: list transaction)(i:nat):
Vol M1 = Vol M2 -> Qty_ask M1 i > Qty_ask M2 i -> exists i' : nat, Qty_ask M1 i' < Qty_ask M2 i'. 
Proof. replace (Vol M1) with (Q_by_asks M1).
       replace (Vol M2) with (Q_by_asks M2).
       intros.  unfold Q_by_asks in H.  
       assert(Q_by_asks_aux M1 (fun_ids_ask M1) = Q_by_asks_aux M2 (fun_ids_ask M1)\/
       Q_by_asks_aux M1 (fun_ids_ask M1) > Q_by_asks_aux M2 (fun_ids_ask M1)\/
       Q_by_asks_aux M1 (fun_ids_ask M1) < Q_by_asks_aux M2 (fun_ids_ask M1)). lia. 
       destruct H1. assert(In i(fun_ids_ask M1)\/~In i(fun_ids_ask M1)).
       eauto. destruct H2. apply Q_by_asks_aux_T_i_In_I with (T:=M1) in H2 as Ha1.
       rewrite Ha1 in H1. apply Q_by_asks_aux_T_i_In_I with (T:=M2) in H2 as Ha2.
       rewrite Ha2 in H1. assert(Q_by_asks_aux M1 (delete i (fun_ids_ask M1)) <
       Q_by_asks_aux M2 (delete i (fun_ids_ask M1))). lia. 
       apply Q_by_asks_aux_T1_T2 in H3.
       destruct H3. destruct H3. exists x. lia. unfold not in H2.
       assert(Qty_ask M1 i = 0). apply Qty_ask_t_zero. intro.
       apply uniq_intro_elim in H3. eauto. lia.
       destruct H1. 2:{ apply Q_by_asks_aux_T1_T2 in H1. destruct H1.
       destruct H1. exists x. lia. }
       rewrite H in H1.
       assert(Subset (fun_ids_ask M2) (fun_ids_ask M1)
       \/~Subset (fun_ids_ask M2) (fun_ids_ask M1)). eauto.
       destruct H2.  assert(Q_by_asks_aux M2 (fun_ids_ask M1) >= 
       Q_by_asks_aux M2 (fun_ids_ask M2) ). eapply Q_by_asks_aux_subset_I1_I2 in H2. 
       exact H2. unfold fun_ids_ask. eauto. unfold fun_ids_ask. eauto. lia.
       assert(exists i, In i (fun_ids_ask M2)/\~In i (fun_ids_ask M1)).
       apply no_subset_existsA. auto. destruct H3. exists x. destruct H3. 
       assert(Qty_ask M1 x = 0).  apply Qty_ask_t_zero. intro. 
       apply uniq_intro_elim in H3. apply uniq_intro_elim in H5.
       destruct H4. auto. 
       apply uniq_intro_elim in H3. apply ids_ask_intro0 in H3.
       lia. symmetry;apply Q_Qty_ask. symmetry;apply Q_Qty_ask. Qed.


End Matching.

Section Maximum. 

Lemma MaxLemmaDelete (M: list transaction) (B A: list order) (w:order):
~ matchable B A -> 
Matching M (delete_order B (id w)) (delete_order A (id w)) -> 
MaxMatch M (delete_order B (id w)) (delete_order A (id w)).
Proof. intros. unfold MaxMatch. intros. 
       apply not_matchable_delete with (b:=w) (a:=w) in H.
       apply not_matchable_matching_nil  in H1. subst. simpl.
       lia. auto. Qed.

Lemma MaxLemmaBuy (M: list transaction) (B A: list order) (b:order):
NoDup (ids A) -> NoDup (ids (b :: B)) -> 
~matchable B A -> 
Matching M (b::B) A -> 
~matchable (odiff (b::B) (bids M (b::B))) (odiff A (asks M A)) ->
MaxMatch M (b::B) A.

Proof.
assert(~(exists a, In a A->tradable b a)\/(exists a, In a A->tradable b a)) as H. 
{ unfold tradable. eauto. }
destruct H. 
  { intros NDA NDB. intro H0. unfold MaxMatch.
    intros H1 H2 M' H3 H4. assert (M' = nil). 
    { apply anot_matchable_tradable with (b:=b) in H0.
      apply not_matchable_matching_nil with (M:=M') in H0.
      auto. auto. auto. }
    subst. simpl. lia. }
  { unfold MaxMatch. intros NDA NDB.
    intros H0 H1 H2 M' H3 H4. assert(HM':=H3).
    assert(~matchable B A -> 
    Matching M' (b::B) A -> (forall t, In t M' -> idb t = id b)) as H5.
    intros H5 H6 t H7. 
    apply insert_order_transaction_bid with (B:=B)(A:=A)(M:=M'). auto. auto. auto.
    apply insert_order_t_Q_le_bid in H3 as Hm3.
    apply insert_order_t_Q_le_bid in H4 as Hm4.
    assert(Vol M = oquantity b\/Vol M < oquantity b) as H6. lia.
    destruct H6. { lia. }
    { apply insert_order_Qle_id_of_b_in_Bhat with (B:=B)(A:=A) in H6.
    apply odiff_exists in H6 as H7.  (*separate out this proof.*)
    assert(Vol M' = Vol M\/Vol M' < Vol M\/Vol M' > Vol M) as H8. lia.
    destruct H8. lia. destruct H8. lia. 
    apply QM1_gt_QM2_extra_ask_in_M1 with (B:=b::B)(A:=A) in H8.
    destruct H8 as [a0 H8]. destruct H8 as [HA H8]. 
    destruct H8 as [H8 H9]. destruct H9 as [m0 H9].
    destruct H7 as [b0 H7]. destruct H9 as [H9 H10]. apply H5 in H9 as Hm10.
    destruct H3 as [H3 H11]. unfold Tvalid in H3. apply H3 in H9 as Hm9.
    unfold valid in Hm9.
    assert(Qty_ask M' (id a0) <= oquantity a0) as H12.
    apply HM'. eauto.
    assert(Qty_ask M (id a0) < oquantity a0) as H13. lia.
    assert(quant (asks M A) (id a0) = Qty_ask M (id a0)) as H14. apply asks_id_quant.
    eauto. destruct Hm9. apply ids_intro. auto.
    assert(In (id a0) (ids (odiff A (asks M A)))).
    apply odiff_intro. replace (quant A (id a0)) with (oquantity a0).
    lia. symmetry. apply quant_elim1. split. auto. auto.
    apply odiff_exists in H15 as H16. destruct H16 as [a' H16]. unfold matchable in H2.
    destruct H2. exists b0. exists a'. split.  apply H16.
    split. apply H7. unfold tradable. replace (oprice b0) with (price (b::B) (id b0)).
    replace (oprice a') with (price A (id a0)).
    destruct Hm9 as [b1 Hm9]. destruct Hm9 as [a1 Hm9]. destruct Hm9 as [Hm9 H17].
    destruct H17 as [H17 H18]. destruct H18 as [H18 H19]. 
    destruct H19 as [H19 H20]. destruct H20 as [H20 H21]. unfold tradable in H20.
    rewrite Hm10 in H18. replace (id b) with (id b0) in H18. 
    rewrite H10 in H19. replace (oprice b1) with (price (b :: B) (id b1)) in H20.
    replace (oprice a1) with (price A (id a1)) in H20. rewrite H18. rewrite H19. auto.
    apply price_elim1. split.  auto. auto. apply price_elim1. split.  auto. auto.
    apply H7. symmetry. apply H16. destruct Hm9 as [b1 Hm9]. 
    destruct Hm9 as [a1 Hm9]. destruct Hm9 as [Hm9 H17].
    destruct H17 as [H17 H18]. destruct H18 as [H18 H19]. 
    destruct H19 as [H19 H20]. destruct H20 as [H20 H21]. unfold tradable in H20.
    replace (id b0) with (id b).  symmetry. apply H7. symmetry;apply H7. eauto. 
    all:auto. } all:auto. } Qed.


Lemma MaxLemmaSell (M: list transaction) (B A: list order) (a:order):
NoDup (ids (a :: A)) -> NoDup (ids B) -> ~matchable B A -> 
Matching M B (a::A) -> 
~matchable (odiff B (bids M B)) (odiff (a::A) (asks M (a::A))) ->
MaxMatch M B (a::A).
Proof. assert(~(exists b, In b B->tradable b a)\/(exists b, In b B->tradable b a)) as H. 
{ unfold tradable. eauto. }
destruct H. 
  { intros NDA NDB. intro H0. unfold MaxMatch.
    intros H1 H2 M' H3 H4. assert (M' = nil). 
    { apply bnot_matchable_tradable with (a:=a) in H0.
      apply not_matchable_matching_nil with (M:=M') in H0.
      auto. auto. auto. }
    subst. simpl. lia. }
  { unfold MaxMatch. intros NDA NDB.
    intros H0 H1 H2 M' H3 H4. assert(HM':=H3).
    assert(~matchable B A -> 
    Matching M' B (a::A) -> (forall t, In t M' -> ida t = id a)) as H5.
    intros H5 H6 t H7. 
    apply insert_order_transaction_ask with (B:=B)(A:=A)(M:=M'). auto. auto. auto.
    apply insert_order_t_Q_le_ask in H3 as Hm3.
    apply insert_order_t_Q_le_ask in H4 as Hm4.
    assert(Vol M = oquantity a\/Vol M < oquantity a) as H6. lia.
    destruct H6. { lia. }
    { apply insert_order_Qle_id_of_a_in_Ahat with (B:=B)(A:=A) in H6.
    apply odiff_exists in H6 as H7.  (*separate out this proof.*)
    assert(Vol M' = Vol M\/Vol M' < Vol M\/Vol M' > Vol M) as H8. lia.
    destruct H8. lia. destruct H8. lia. 
    apply QM1_gt_QM2_extra_bid_in_M1 with (B:=B)(A:=(a::A)) in H8.
    destruct H8 as [b0 H8]. destruct H8 as [HB H8]. 
    destruct H8 as [H8 H9]. destruct H9 as [m0 H9].
    destruct H7 as [a0 H7]. destruct H9 as [H9 H10].
    apply H5 in H9 as Hm10.
    destruct H3 as [H3 H11]. unfold Tvalid in H3. apply H3 in H9 as Hm9.
    unfold valid in Hm9.
    assert(Qty_bid M' (id b0) <= oquantity b0) as H12.
    apply HM'. auto.
    assert(Qty_bid M (id b0) < oquantity b0) as H13. lia.
    assert(quant (bids M B) (id b0) = Qty_bid M (id b0)) as H14. apply bids_id_quant.
    eauto. destruct Hm9. apply ids_intro. auto.
    assert(In (id b0) (ids (odiff B (bids M B)))).
    apply odiff_intro. replace (quant B (id b0)) with (oquantity b0).
    lia. symmetry. apply quant_elim1. split. auto. auto.
    apply odiff_exists in H15 as H16. destruct H16 as [b' H16]. 
    unfold matchable in H2.
    destruct H2. exists b'. exists a0. split.  apply H7.
    split. apply H16. unfold tradable. 
    destruct Hm9 as [b1 Hm9]. destruct Hm9 as [a1 Hm9]. destruct Hm9 as [Hm9 H17].
    destruct H17 as [H17 H18]. destruct H18 as [H18 H19]. 
    destruct H19 as [H19 H20]. destruct H20 as [H20 H21]. unfold tradable in H20.
    destruct H16. destruct H16. rewrite H22. destruct H7. destruct H23.
    rewrite H24.
    rewrite price_elim1. split.  auto. auto. rewrite price_elim1. split.  auto. auto.
    assert(a1=a). apply nodup_ids_uniq_order with (B:=a::A). auto. auto. auto.
    lia.
    assert(b1=b0). apply nodup_ids_uniq_order with (B:=B). auto. auto. auto.
    lia. subst.  auto. all:auto. } all:auto. } Qed.



Theorem Maximum_Maching (Process: list order->list order -> instruction ->
(list order)*(list order)*(list transaction))(B A hat_B hat_A : list order)(tau:instruction):
let B' := (fst (Absorb B A tau)) in
let A' := (snd (Absorb B A tau)) in
let hat_B := (Blist (Process B A tau)) in
let hat_A := (Alist (Process B A tau)) in
let M := (Mlist (Process B A tau)) in

Condition1 M B A hat_B hat_A tau->

Condition3a M B A tau->
Condition3b M B A hat_B tau ->
Condition3c M B A hat_A tau ->

not (matchable B A) ->

NoDup (ids B') ->
NoDup (ids A') ->

MaxMatch (Mlist (Process B A tau)) B' A'.
Proof. set(M:=(Process B A tau)). case (cmd tau) eqn:Ht. 
        { 
        simpl. unfold Condition1, Condition3a, Condition3b, Condition3c.
        unfold Absorb. rewrite Ht. unfold fst. unfold snd. 
        intros H H0 H1 H2 H3 H4 H5.
        apply MaxLemmaBuy. all: auto. 
        eapply not_matchable_perm_invariance. exact H. auto. auto.
       }
       {
        simpl. unfold Condition1, Condition3a, Condition3b, Condition3c.
        unfold Absorb. rewrite Ht. unfold fst. unfold snd. 
        intros H H0 H1 H2 H3 H4 H5.
        apply MaxLemmaSell. all:auto.
        eapply not_matchable_perm_invariance. exact H. auto. auto.
       }
       { 
        simpl. unfold Condition1, Condition3a, Condition3b, Condition3c.
        unfold Absorb. rewrite Ht. unfold fst. unfold snd. 
        intros H H0 H1 H2 H3 H4 H5.
        apply MaxLemmaDelete. all:auto.
       } Qed.

End Maximum.

Section PTPsize.

Lemma uniq_time (A:list order)(a1 a2:order):
NoDup (timesof A) -> In a1 A -> In a2 A ->a1<>a2 -> otime a1 <> otime a2.
Proof. revert a1 a2. induction A. simpl. auto. simpl. intros.
destruct H0;destruct H1. { subst. auto. }
{ subst. assert(~In (otime a1) (timesof A)). eauto.
  apply timesof_elim in H1. intro. rewrite H3 in H0. destruct (H0 H1). }
{ subst. assert(~In (otime a2) (timesof A)). eauto.
  apply timesof_elim in H0. intro. rewrite H3 in H0. destruct (H1 H0). }
{ apply IHA. eauto. all:auto. } Qed.

Lemma size_equal_and_price_time_priorityA (M1 M2: list transaction)(B A: list order):
NoDup (ids A) -> NoDup (ids B) ->
NoDup (timesof A) -> NoDup (timesof B) ->
(forall t, In t M1 -> over t B A) -> (forall t, In t M2 -> over t B A) ->
Vol M1 = Vol M2 -> 
(forall a a', (In a A)/\(In a' A)/\(acompetitive a a'/\~eqcompetitive a a')/\(In (id a') (ids_ask_aux M1)) 
-> (Qty_ask M1 (id a)) = (oquantity a)) ->
(forall a a', (In a A)/\(In a' A)/\(acompetitive a a'/\~eqcompetitive a a')/\(In (id a') (ids_ask_aux M2)) 
-> (Qty_ask M2 (id a)) = (oquantity a)) ->
(forall a, In a A -> (Qty_ask M1 (id a) ) <= (oquantity a)) ->
(forall a, In a A-> (Qty_ask M2 (id a) ) <= (oquantity a)) ->
(forall i, Qty_ask M1 i = Qty_ask M2 i).
Proof. 
intros NDtA NDtB NDA NDB M1BA M2BA H H01 H02 H11 H12 i. assert (Qty_ask M1 i = Qty_ask M2 i\/Qty_ask M1 i > Qty_ask M2 i
\/Qty_ask M1 i < Qty_ask M2 i) as H2. lia. destruct H2 as [H2 | H2]. auto. destruct H2 as [H2 | H2]. 
{ assert(exists i', Qty_ask M1 i' < Qty_ask M2 i') as H3. 
  apply QM1_eq_QM2_extra_ask_in_M1 in H2.
  auto. auto. unfold over in M1BA.
  unfold over in M2BA. destruct H3 as [i' H3]. 
  assert(Qty_ask M1 i >0) as H4. lia. apply Qty_ask_elim in H4.
  assert(Qty_ask M2 i' >0) as H5. lia. apply Qty_ask_elim in H5.
  destruct H4 as [m1 H4]. destruct H5 as [m2 H5].
  destruct H4 as [H4a H4b]. destruct H5 as [H5a H5b]. 
  apply M1BA in H4a as M1a. apply M2BA in H5a as M2a.
  destruct M1a as [b1 M1a]. destruct M1a as [a1 M1a].
  destruct M1a as [a1A M1a]. destruct M1a as [b1B M1a].
  destruct M1a as [idb1 ida1].
  destruct M2a as [b2 M2a]. destruct M2a as [a2 M2a].
  destruct M2a as [a2A M2a]. destruct M2a as [b2B M2a].
  destruct M2a as [idb2 ida2].
  assert (a1 = a2\/a1<>a2) as Ha1a2. eauto. destruct Ha1a2 as [Heq|Hneq].
  { assert(i = i'). subst a1. lia. subst i. subst i'. rewrite H0 in H2. lia. }
  { (*Case:a1<>a2*)
  assert (acompetitive a1 a2 \/~acompetitive a1 a2) as H4. eauto.
  destruct H4 as [H4|H4]. 
   { specialize (H02 a1 a2). 
     specialize (H11 a1). specialize (H11 a1A). 
     assert (Qty_ask M2 (id a1) < oquantity a1) as M2q.
     replace i with (ida m1) in H2. replace (ida m1) with (id a1) in H2.  
     lia. assert(Qty_ask M2 (id a1) = oquantity a1) as H2q'.
     apply H02. split. auto. split. auto. replace (id a2) with (ida m2).
     split. split. auto. intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime a1 <> otime a2). 
     apply uniq_time with (A:=A). all:auto. apply uniq_intro_elim. 
     apply ids_ask_intro1. auto. 
     replace i with (id a2) in H2. replace i' with (id a2) in H3. lia. lia. 
     lia.
   }
   { apply not_acompetitive in H4. specialize (H01 a2 a1). 
     specialize (H12 a2).  specialize (H12 a2A). 
     assert (Qty_ask M1 (id a2) < oquantity a2) as M1q.
     replace i' with (ida m2) in H3. replace (ida m2) with (id a2) in H3.
     lia. assert(Qty_ask M1 (id a2) = oquantity a2) as H1q'.
     apply H01. split. auto. split. auto. split. split. auto. 
     intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime a1 <> otime a2).  
     apply uniq_time with (A:=A). all:auto. 
     replace (id a1) with (ida m1). 
     apply uniq_intro_elim.
     auto. apply ids_ask_intro1. auto. 
     lia. 
   }
} }
{ assert(exists i', Qty_ask M2 i' < Qty_ask M1 i') as H3. 
  apply QM1_eq_QM2_extra_ask_in_M1 in H2.
  auto. auto. unfold over in M1BA.
  unfold over in M2BA. destruct H3 as [i' H3]. 
  assert(Qty_ask M2 i >0) as H4. lia. apply Qty_ask_elim in H4.
  assert(Qty_ask M1 i' >0) as H5. lia. apply Qty_ask_elim in H5.
  destruct H4 as [m2 H4]. destruct H5 as [m1 H5].
  destruct H4 as [H4a H4b]. destruct H5 as [H5a H5b]. 
  apply M1BA in H5a as M1a. apply M2BA in H4a as M2a.
  destruct M1a as [b1 M1a]. destruct M1a as [a1 M1a].
  destruct M1a as [a1A M1a]. destruct M1a as [b1B M1a].
  destruct M1a as [idb1 ida1].
  destruct M2a as [b2 M2a]. destruct M2a as [a2 M2a]. 
  destruct M2a as [a2A M2a]. destruct M2a as [b2B M2a].
  destruct M2a as [idb2 ida2].
  assert (a1 = a2\/a1<>a2) as Ha1a2. eauto. destruct Ha1a2 as [Heq|Hneq].
  { assert(i = i'). subst a1. lia. subst i. subst i'. rewrite H0 in H2. lia. }
  { (*Case:a1<>a2*)
  assert (acompetitive a1 a2 \/~acompetitive a1 a2) as H4. eauto.
  destruct H4 as [H4|H4]. 
   { subst. specialize (H02 a1 a2). 
     specialize (H11 a1).  specialize (H11 a1A). 
     assert (Qty_ask M2 (id a1) < oquantity a1) as M1q.
     replace (ida m1) with (id a1) in H3.
     lia. assert(Qty_ask M2 (id a1) = oquantity a1) as H2q'.
     apply H02. split. auto. split. auto. split. split. auto. 
     intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime a1 <> otime a2).  
     apply uniq_time with (A:=A). all:auto. 
     replace (id a2) with (ida m2). 
     apply uniq_intro_elim. apply ids_ask_intro1. auto.
     lia. 
   }
   { subst. apply not_acompetitive in H4. specialize (H01 a2 a1). 
     specialize (H12 a2).  specialize (H12 a2A). 
     assert (Qty_ask M1 (id a2) < oquantity a2) as M1q.
     replace (ida m2) with (id a2) in H2.
     lia. assert(Qty_ask M1 (id a2) = oquantity a2) as H1q'.
     apply H01. split. auto. split. auto.
     split. split. auto. 
     intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime a1 <> otime a2).  
     apply uniq_time with (A:=A). all:auto. 
     replace (id a1) with (ida m1). 
     apply uniq_intro_elim. apply ids_ask_intro1. auto.
     lia. 
   }
} }
Qed.
    

Lemma size_equal_and_price_time_priorityB (M1 M2: list transaction)(B A: list order):
NoDup (ids A) -> NoDup (ids B) ->
NoDup (timesof A) -> NoDup (timesof B) ->
(forall t, In t M1 -> over t B A) -> (forall t, In t M2 -> over t B A) ->
Vol M1 = Vol M2 -> 
(forall b b', (In b B)/\(In b' B)/\(bcompetitive b b'/\~eqcompetitive b b')/\(In (id b') (ids_bid_aux M1)) 
-> (Qty_bid M1 (id b)) = (oquantity b)) ->
(forall b b', (In b B)/\(In b' B)/\(bcompetitive b b'/\~eqcompetitive b b')/\(In (id b') (ids_bid_aux M2)) 
-> (Qty_bid M2 (id b)) = (oquantity b)) ->
(forall b, In b B -> (Qty_bid M1 (id b) ) <= (oquantity b)) ->
(forall b, In b B -> (Qty_bid M2 (id b) ) <= (oquantity b)) ->
(forall i, Qty_bid M1 i = Qty_bid M2 i).
Proof. 
intros NDtA NDtB NDA NDB M1BA M2BA H H01 H02 H11 H12 i. assert (Qty_bid M1 i = Qty_bid M2 i\/Qty_bid M1 i > Qty_bid M2 i
\/Qty_bid M1 i < Qty_bid M2 i) as H2. lia. destruct H2 as [H2 | H2]. auto. destruct H2 as [H2 | H2]. 
{ assert(exists i', Qty_bid M1 i' < Qty_bid M2 i') as H3. 
  apply QM1_eq_QM2_extra_bid_in_M1 in H2.
  auto. auto. unfold over in M1BA.
  unfold over in M2BA. destruct H3 as [i' H3]. 
  assert(Qty_bid M1 i >0) as H4. lia. apply Qty_bid_elim in H4.
  assert(Qty_bid M2 i' >0) as H5. lia. apply Qty_bid_elim in H5.
  destruct H4 as [m1 H4]. destruct H5 as [m2 H5].
  destruct H4 as [H4a H4b]. destruct H5 as [H5a H5b]. 
  apply M1BA in H4a as M1a. apply M2BA in H5a as M2a.
  destruct M1a as [b1 M1a]. destruct M1a as [a1 M1a].
  destruct M1a as [a1A M1a]. destruct M1a as [b1B M1a].
  destruct M1a as [idb1 ida1].
  destruct M2a as [b2 M2a]. destruct M2a as [a2 M2a].
  destruct M2a as [a2A M2a]. destruct M2a as [b2B M2a].
  destruct M2a as [idb2 ida2].
  assert (b1 = b2\/b1<>b2) as Ha1a2. eauto. destruct Ha1a2 as [Heq|Hneq].
  { assert(i = i'). subst b1. lia. subst i. subst i'. rewrite H0 in H2. lia. }
  { (*Case:b1<>b2*)
  assert (bcompetitive b1 b2 \/~bcompetitive b1 b2) as H4. eauto.
  destruct H4 as [H4|H4]. 
   { specialize (H02 b1 b2). 
     specialize (H11 b1). specialize (H11 b1B). 
     assert (Qty_bid M2 (id b1) < oquantity b1) as M2q.
     replace i with (idb m1) in H2. replace (idb m1) with (id b1) in H2.
     lia. assert(Qty_bid M2 (id b1) = oquantity b1) as H2q'.
     apply H02. split. auto. split. auto. replace (id b2) with (idb m2).
     split. split. auto. intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime b1 <> otime b2). 
     apply uniq_time with (A:=B). all:auto. apply uniq_intro_elim.
     apply ids_bid_intro1. auto. lia.
   }
   { apply not_bcompetitive in H4. specialize (H01 b2 b1). 
     specialize (H12 b2). specialize (H12 b2B). 
     assert (Qty_bid M1 (id b2) < oquantity b2) as M1q.
     replace i' with (idb m2) in H3. replace (idb m2) with (id b2) in H3.
     lia. assert(Qty_bid M1 (id b2) = oquantity b2) as H1q'.
     apply H01. split. auto. split. auto. split. split. auto.
     intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime b1 <> otime b2).  
     apply uniq_time with (A:=B). all:auto. 
     replace (id b1) with (idb m1). 
     apply uniq_intro_elim.
     auto. apply ids_bid_intro1. auto. 
     lia. 
   }
} }
{ assert(exists i', Qty_bid M2 i' < Qty_bid M1 i') as H3. 
  apply QM1_eq_QM2_extra_bid_in_M1 in H2.
  auto. auto. unfold over in M1BA.
  unfold over in M2BA. destruct H3 as [i' H3]. 
  assert(Qty_bid M2 i >0) as H4. lia. apply Qty_bid_elim in H4.
  assert(Qty_bid M1 i' >0) as H5. lia. apply Qty_bid_elim in H5.
  destruct H4 as [m2 H4]. destruct H5 as [m1 H5].
  destruct H4 as [H4a H4b]. destruct H5 as [H5a H5b]. 
  apply M1BA in H5a as M1a. apply M2BA in H4a as M2a.
  destruct M1a as [b1 M1a]. destruct M1a as [a1 M1a].
  destruct M1a as [a1A M1a]. destruct M1a as [b1B M1a].
  destruct M1a as [idb1 ida1].
  destruct M2a as [b2 M2a]. destruct M2a as [a2 M2a]. 
  destruct M2a as [a2A M2a]. destruct M2a as [b2B M2a].
  destruct M2a as [idb2 ida2].
  assert (b1 = b2\/b1<>b2) as Ha1a2. eauto. destruct Ha1a2 as [Heq|Hneq].
  { assert(i = i'). subst b1. lia. subst i. subst i'. rewrite H0 in H2. lia. }
  { (*Case:b1<>b2*)
  assert (bcompetitive b1 b2 \/~bcompetitive b1 b2) as H4. eauto.
  destruct H4 as [H4|H4]. 
   { subst. specialize (H02 b1 b2). 
     specialize (H11 b1). specialize (H11 b1B). 
     assert (Qty_bid M2 (id b1) < oquantity b1) as M1q.
     replace (idb m1) with (id b1) in H3.
     lia. assert(Qty_bid M2 (id b1) = oquantity b1) as H2q'.
     apply H02. split. auto. split. auto. split. split. auto. 
     intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime b1 <> otime b2).  
     apply uniq_time with (A:=B). all:auto. 
     replace (id b2) with (idb m2). 
     apply uniq_intro_elim. apply ids_bid_intro1. auto.
     lia. 
   }
   { subst. apply not_bcompetitive in H4. specialize (H01 b2 b1). 
     specialize (H12 b2). specialize (H12 b2B). 
      assert (Qty_bid M1 (id b2) < oquantity b2) as M1q.
     replace (idb m2) with (id b2) in H2. 
     lia. assert(Qty_bid M1 (id b2) = oquantity b2) as H1q'.
     apply H01. split. auto. split. auto.
     split. split. auto. 
     intro Hcontra. unfold eqcompetitive in Hcontra.
     move /andP in Hcontra. destruct Hcontra as [H1c H2c].
     move /eqP in H2c. assert(otime b1 <> otime b2).  
     apply uniq_time with (A:=B). all:auto. 
     replace (id b1) with (idb m1). 
     apply uniq_intro_elim. apply ids_bid_intro1. auto.
     lia. 
   }
} }
Qed.


End PTPsize.



