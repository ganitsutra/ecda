

(*------------------------------------------*)
(*--This file contains proofs of both the---*)
(*-----------uniqueness Theorems:-----------*)
(*--Local uniqueness and Global uniqueness--*)
(*------------------------------------------*)


Require Import Definitions Properties MaxMatch.

Set Implicit Arguments.

Section Uniqness.
Notation "s === t" := (perm s t) (at level 80, no associativity).

Theorem Local_uniqueness 
(Process1 Process2: list order->list order -> instruction->
(list order)*(list order)*(list transaction))
(B1 B2 A1 A2 : list order)(tau:instruction):
B1 === B2 -> A1 === A2 ->
Legal_input B1 A1 tau ->
Properties Process1 -> Properties Process2 ->

(cform (Mlist (Process1 B1 A1 tau))) === (cform (Mlist (Process2 B2 A2 tau))) /\
(Blist (Process1 B1 A1 tau)) === (Blist (Process2 B2 A2 tau))/\
(Alist (Process1 B1 A1 tau)) === (Alist (Process2 B2 A2 tau))/\
(included (timesof (Blist (Process1 B1 A1 tau))) (timesof ((ord tau)::B1)))/\
(included (timesof (Alist (Process1 B1 A1 tau))) (timesof ((ord tau)::A1)))/\
(not (matchable (Blist (Process1 B1 A1 tau)) 
(Alist (Process1 B1 A1 tau))))/\
admissible (Blist (Process1 B1 A1 tau)) (Alist (Process1 B1 A1 tau))
/\
(included (ids (Blist (Process1 B1 A1 tau))) (ids ((ord tau)::B1)))/\
(included (ids (Alist (Process1 B1 A1 tau))) (ids ((ord tau)::A1)))/\
((cmd tau) = del -> ~ In (id (ord tau)) (ids (Blist (Process1 B1 A1 tau))))/\
((cmd tau) = del -> ~ In (id (ord tau)) (ids (Alist (Process1 B1 A1 tau)))).
Proof.  unfold Properties. 
        intros HpermB HpermA Leg1 HP1 HP2.
        Ltac my_auto_unfold conditioni := repeat match goal with 
            | [ H: _|-_ ] => progress unfold conditioni in H
        end. my_auto_unfold Condition1.
        my_auto_unfold Condition2a. my_auto_unfold Condition2b.
        my_auto_unfold Condition3a. my_auto_unfold Condition3b.
        my_auto_unfold Condition3c. 
        specialize (HP1 A1). specialize (HP1 B1).
        specialize (HP1 tau).
        specialize (HP2 A2). specialize (HP2 B2).
        specialize (HP2 tau).
        assert(Legal_input B2 A2 tau) as Leg2.
        eapply legal_perm. split. auto. split. auto. auto. 
        assert(L1:=Leg1). assert(L2:=Leg2).
        apply HP1 in Leg1. apply HP2 in Leg2. clear HP1 HP2.
        revert Leg1 Leg2 L1 L2. unfold Legal_input.
        set(B1':=(fst (Absorb B1 A1 tau))).
        set(A1':=(snd (Absorb B1 A1 tau))). 
        set(B2':=(fst (Absorb B2 A2 tau))).
        set(A2':=(snd (Absorb B2 A2 tau))). 
        set(M1:=Mlist (Process1 B1 A1 tau)). 
        set(M2:=Mlist (Process2 B2 A2 tau)).
        set(hat_B1:=Blist (Process1 B1 A1 tau)). 
        set(hat_B2:=Blist (Process2 B2 A2 tau)).
        set(hat_A1:=Alist (Process1 B1 A1 tau)). 
        set(hat_A2:=Alist (Process2 B2 A2 tau)).
        intros Cond1 Cond2 L1 L2. destruct Cond1 as [c1_1 Hn].
        destruct Hn as [c2bid_1 Hn]. destruct Hn as [c2ask_1 Hn].
        destruct Hn as [c3a_1 Hn]. destruct Hn as [c3b_1 c3c_1].
        destruct Cond2 as [c1_2 Hn]. destruct Hn as [c2bid_2 Hn]. 
        destruct Hn as [c2ask_2 Hn]. destruct Hn as [c3a_2 Hn]. 
        destruct Hn as [c3b_2 c3c_2].
        destruct L1 as [L1 nm1]. destruct L1 as [ndiB1 L1].
        destruct L1 as [ndiA1 L1]. destruct L1 as [ndtB1 ndtA1].
        destruct L2 as [L2 nm2]. destruct L2 as [ndiB2 L2].
        destruct L2 as [ndiA2 L2]. destruct L2 as [ndtB2 ndtA2].
        assert(perm B1' B2') as HpermB'. apply Absorb_perm.
        auto. auto.
        assert(perm A1' A2') as HpermA'. apply Absorb_perm.
        auto. auto.
        assert (MaxMatch M1 B1' A1') as M1max. 
        eapply Maximum_Maching. auto. auto. 
        exact c1_1. all:auto. 
        assert (MaxMatch M2 B2' A2') as M2max. eapply Maximum_Maching. auto. auto. 
        exact c1_2. all:auto.
        unfold MaxMatch in M1max. unfold MaxMatch in M2max.
        assert(Vol M1 = Vol M2) as HQ. 
        { specialize (M1max M2). specialize (M2max M1). 
          apply M1max in c3a_1 as H4a. 
          apply M2max in c3a_2 as H2a. lia.
          eapply Maching_perm. assert(perm B2' B1'). eauto.  exact H.
          assert(perm A2' A1'). eauto.  exact H. exact c3a_2. auto. 
          eapply Maching_perm. exact HpermB'. exact HpermA'. exact c3a_1. auto.
        }
        my_auto_unfold Absorb. destruct (cmd tau) eqn:Hact.
        {  subst B1'. subst A1'. subst B2'. subst A2'. 
           repeat match goal with 
            | [ H: context[ snd ] |-_ ] => unfold snd in H end.
            repeat match goal with 
            | [ H: context[ fst ] |-_ ] => unfold fst in H end.
           assert(perm (cform M1) (cform M2)) as Hcform.
           {  apply perm_cannonical_form. intros. 
              apply size_equal_and_price_time_priorityA with 
              (B:=(ord tau)::B1)(A:=A1)(i:=j) in HQ.
              assert((forall t, In t M1 -> idb t = id (ord tau))) as idb1w.
              apply insert_order_transaction_bid with (b:=(ord tau))(B:=B1)(A:=A1).
              auto. auto.
              assert((forall t, In t M2 -> idb t = id (ord tau))) as ibd2w.
              apply insert_order_transaction_bid with (b:=(ord tau))(B:=B2)(A:=A2).
              auto. auto. 
              assert((forall j, Qty_ask M1 j = Qty M1 (id (ord tau)) j)) as aq1.
              apply Qty_Qty_ask. auto.
              assert((forall j, Qty_ask M2 j = Qty M2 (id (ord tau)) j)) as aq2.
              apply Qty_Qty_ask. auto. 
              replace(Qty_ask M1 j) with (Qty M1 (id (ord tau)) j) in HQ.
              replace(Qty_ask M2 j) with (Qty M2 (id (ord tau)) j) in HQ.
              apply Qty_ask_M1_M2 with (w:=(ord tau)). all: auto.
              apply Matching_over.
              auto. apply Matching_over. auto. 
              eapply Maching_perm_wB. auto. exact HpermB. exact HpermA. auto.
              intros. apply c2ask_2 with (a':=a'). destruct H.
              destruct H0. destruct H1. unfold perm in HpermA. move /andP in HpermA.
              destruct HpermA. repeat split. eauto. eauto. 
              apply H1. apply H1. auto. apply c3a_1. intros. apply c3a_2.
              unfold perm in HpermA. move /andP in HpermA. destruct HpermA.
              eauto.
           }
           repeat split.
           { auto. }
           { assert(perm (odiff ((ord tau) :: B1) (bids M1 ((ord tau) :: B1))) 
             (odiff ((ord tau) :: B2) (bids M2 ((ord tau) :: B2)))) as Hn. 
             { apply odiff_perm. 
              all:auto. apply nodup_ids_bids. auto. apply cform_bids_perm.
              all:auto. }  eauto. }
           {  assert(perm (odiff A1 (asks M1 A1)) 
             (odiff A2 (asks M2 A2))). apply odiff_perm. 
              all:auto. apply nodup_ids_asks. auto. apply cform_asks_perm. all:auto.
           }
           { apply timesof_perm in c3b_1. 
             assert(included (timesof (odiff ((ord tau) :: B1) 
             (bids M1 ((ord tau) :: B1)))) (timesof ((ord tau) :: B1))). 
             apply odiff_included_timesof.
             unfold perm in c3b_1. move /andP in c3b_1. destruct c3b_1.
             eauto.
           }
           { apply timesof_perm in c3c_1. 
             assert(included (timesof (odiff A1 (asks M1 A1)))
              (timesof A1)). apply odiff_included_timesof.
             unfold perm in c3c_1. move /andP in c3c_1. destruct c3c_1.
             simpl. apply included_elim3d with (a:=otime (ord tau)). eauto.
           }
           { auto. }
           { assert(perm (ids (odiff ((ord tau) :: B1) 
             (bids M1 ((ord tau) :: B1)))) (ids hat_B1)). 
             apply ids_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_ids. auto. }
           { assert(perm (ids (odiff A1 (asks M1 A1))) (ids hat_A1)). 
             apply ids_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_ids. auto. }
           { assert(perm (timesof (odiff ((ord tau) :: B1) 
             (bids M1 ((ord tau) :: B1)))) (timesof hat_B1)). 
             apply timesof_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_timesof. auto. }
           { assert(perm (timesof (odiff A1 (asks M1 A1))) 
             (timesof hat_A1)). 
             apply timesof_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_timesof. auto. }
           { apply ids_perm in c3b_1. 
             assert(included (ids (odiff ((ord tau) :: B1) 
             (bids M1 ((ord tau) :: B1)))) (ids ((ord tau) :: B1))).
             apply odiff_included_ids. 
             unfold perm in c3b_1. move /andP in c3b_1. destruct c3b_1. eauto. }
           { apply ids_perm in c3c_1. 
             assert(included (ids (odiff A1 (asks M1 A1)))
              (ids A1)). apply odiff_included_ids. 
              unfold perm in c3c_1. move /andP in c3c_1. destruct c3c_1.
              simpl. apply included_elim3d. eauto. }
           { intro. inversion H. }
           { intro. inversion H. }
         }
        {  my_auto_unfold Absorb. 
           subst B1'. subst A1'. subst B2'. subst A2'. 
           repeat match goal with 
            | [ H: context[ snd ] |-_ ] => unfold snd in H end.
            repeat match goal with 
            | [ H: context[ fst ] |-_ ] => unfold fst in H end.
           assert(perm (cform M1) (cform M2)) as Hcform.
           {
              apply perm_cannonical_form. intros. 
              apply size_equal_and_price_time_priorityB with 
              (B:=B1)(A:=(ord tau)::A1)(i:=i) in HQ.
              assert((forall t, In t M1 -> ida t = id (ord tau))) as ida1w.
              apply insert_order_transaction_ask with (a:=(ord tau))(B:=B1)(A:=A1).
              auto. auto.
              assert((forall t, In t M2 -> ida t = id (ord tau))) as iba2w.
              apply insert_order_transaction_ask with (a:=(ord tau))(B:=B2)(A:=A2).
              auto. auto. 
              assert((forall i, Qty_bid M1 i = Qty M1 i (id (ord tau)))) as bq1.
              apply Qty_Qty_bid. auto.
              assert((forall i, Qty_bid M2 i = Qty M2 i (id (ord tau)))) as bq2.
              apply Qty_Qty_bid. auto. 
              replace(Qty_bid M1 i) with (Qty M1 i (id (ord tau)) ) in HQ.
              replace(Qty_bid M2 i) with (Qty M2 i (id (ord tau)) ) in HQ.
              apply Qty_bid_M1_M2 with (w:=(ord tau)). all: auto.
              apply Matching_over.
              auto. apply Matching_over.
              eapply Maching_perm_wA. auto. exact HpermB. exact HpermA. auto.
              intros. apply c2bid_2 with (b':=b'). destruct H.
              destruct H0. unfold perm in HpermB. move /andP in HpermB.
              destruct HpermB. repeat split. eauto. eauto. 
              apply H1. apply H1. apply H1.  
              apply c3a_1. intros. apply c3a_2.
              unfold perm in HpermB. move /andP in HpermB. destruct HpermB.
              eauto.
           }
           repeat split.
           { auto. }
           {  assert(perm (odiff B1 (bids M1 B1)) 
             (odiff B2 (bids M2 B2))). apply odiff_perm. 
              all:auto. apply nodup_ids_bids.  auto. apply cform_bids_perm.
              all:auto.  }
           {  assert(perm (odiff ((ord tau) :: A1) (asks M1 ((ord tau) :: A1))) 
             (odiff ((ord tau) :: A2) (asks M2 ((ord tau) :: A2)))). apply odiff_perm. 
              all:auto. apply nodup_ids_asks. auto. apply cform_asks_perm. all:auto.  }
           { apply timesof_perm in c3b_1. 
             assert(included (timesof (odiff B1 (bids M1 B1)))
              (timesof B1)). apply odiff_included_timesof.
             unfold perm in c3b_1. move /andP in c3b_1. destruct c3b_1.
             simpl. apply included_elim3d. eauto.
           }
           { apply timesof_perm in c3c_1. 
             assert(included (timesof (odiff ((ord tau) :: A1) 
             (asks M1 ((ord tau) :: A1)))) (timesof ((ord tau) :: A1))). 
             apply odiff_included_timesof.
             unfold perm in c3c_1. move /andP in c3c_1. destruct c3c_1.
             eauto.
           }
           { auto. }
           { assert(perm (ids (odiff B1 (bids M1 B1))) (ids hat_B1)). 
             apply ids_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_ids. auto. }
           { assert(perm (ids (odiff ((ord tau) :: A1) 
             (asks M1 ((ord tau) :: A1)))) (ids hat_A1)). 
             apply ids_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_ids. auto. }
           { assert(perm (timesof (odiff B1 (bids M1 B1))) 
             (timesof hat_B1)). 
             apply timesof_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_timesof. auto. }
           { assert(perm (timesof (odiff ((ord tau) :: A1) 
             (asks M1 ((ord tau) :: A1)))) (timesof hat_A1)). 
             apply timesof_perm. eauto. apply perm_nodup in H. auto. 
             apply odiff_nodup_timesof. auto. }
           { apply ids_perm in c3b_1. 
             assert(included (ids (odiff B1 (bids M1 B1)))
              (ids B1)). apply odiff_included_ids. 
              unfold perm in c3b_1. move /andP in c3b_1. destruct c3b_1.
              simpl. apply included_elim3d. eauto. }
           { apply ids_perm in c3c_1. 
             assert(included (ids (odiff ((ord tau) :: A1) 
             (asks M1 ((ord tau) :: A1)))) (ids ((ord tau) :: A1))). 
             apply odiff_included_ids. 
             unfold perm in c3c_1. move /andP in c3c_1. destruct c3c_1. eauto. }
           { intro. inversion H. }
           { intro. inversion H. }
         } 
          { apply not_matchable_delete with (b:=(ord tau)) (a:=(ord tau)) in nm1
            as H11M1.
            apply not_matchable_matching_nil with (M:=M1) in H11M1. 
            rewrite H11M1.
            apply not_matchable_delete with (b:=(ord tau)) (a:=(ord tau)) in nm2
            as H11M2.
            apply not_matchable_matching_nil with (M:=M2) in H11M2.
            rewrite H11M2. unfold cform. simpl.
            rewrite H11M1 in c3b_1. rewrite bids_nil in c3b_1. 
            rewrite odiff_nil in c3b_1. 
            rewrite H11M2 in c3b_2. rewrite bids_nil in c3b_2. 
            rewrite odiff_nil in c3b_2. 
            rewrite H11M1 in c3c_1. rewrite asks_nil in c3c_1. 
            rewrite odiff_nil in c3c_1. 
            rewrite H11M2 in c3c_2. rewrite asks_nil in c3c_2. 
            rewrite odiff_nil in c3c_2. split. auto.
            subst B1'.  subst B2'. subst A1'. subst A2'.
            simpl .
            repeat split. 
            { eauto. } { eauto. } 
            { simpl in c3b_1. apply included_elim3d.
              apply included_timesof. 
              apply delete_order_included with (i:= (id (ord tau))). auto.
              unfold perm in c3b_1. move /andP in c3b_1.
              apply c3b_1.
            }
            { simpl in c3c_1. apply included_elim3d.
              apply included_timesof. 
              apply delete_order_included with (i:= (id (ord tau))). auto.
              unfold perm in c3c_1. move /andP in c3c_1.
              apply c3c_1.
            }
            { auto. }
            { simpl in ndiB1. 
              apply perm_nodup with (l:=(ids (delete_order B1 (id (ord tau))))).
              simpl in c3b_1. apply ids_perm. auto. auto.
            } 
            { simpl in ndiA1. 
              apply perm_nodup with (l:=(ids (delete_order A1 (id (ord tau))))).
              simpl in c3c_1. apply ids_perm. auto. auto.
            }
            { simpl in ndtB1. 
              apply perm_nodup with (l:=(timesof (delete_order B1 (id (ord tau))))).
              simpl in c3b_1. apply timesof_perm. auto. auto.
            } 
            { simpl in ndtA1. 
              apply perm_nodup with (l:=(timesof (delete_order A1 (id (ord tau))))).
              simpl in c3c_1. apply timesof_perm. auto. auto.
            }
            { simpl in c3b_1. apply included_elim3d.
              apply included_ids. 
              apply delete_order_included with (i:= (id (ord tau))). auto.
              unfold perm in c3b_1. move /andP in c3b_1.
              apply c3b_1.
            }
            { simpl in c3c_1. apply included_elim3d.
              apply included_ids. 
              apply delete_order_included with (i:= (id (ord tau))). auto.
              unfold perm in c3c_1. move /andP in c3c_1.
              apply c3c_1.
            }
            { intros. simpl in c3b_1. 
              assert(~In (id (ord tau)) (ids (delete_order B1 (id (ord tau))))).
              apply delete_order_ids_elim. 
              apply ids_perm in c3b_1. unfold perm in c3b_1. move /andP in c3b_1.
              destruct c3b_1. intro. destruct H0. eauto.
            }
            { intros. simpl in c3c_1. 
              assert(~In (id (ord tau)) (ids (delete_order A1 (id (ord tau))))).
              apply delete_order_ids_elim. 
              apply ids_perm in c3c_1. unfold perm in c3c_1. move /andP in c3c_1.
              destruct c3c_1. intro. destruct H0. eauto.
            }
            { subst B2'. subst A2'. simpl in c3a_2. auto. }
            { subst B2'. subst A2'. simpl in c3a_1. auto. }
         }  Qed.

Theorem global_unique_aux (P1 P2 :(list order)->(list order) -> instruction -> (list order)*(list order)*(list transaction))(I : list instruction)(k:nat):
(Properties P1) -> (Properties P2) -> structured I ->
(cform (Mlist (iterated P1 I k))) === (cform (Mlist (iterated P2 I k)))/\
(Blist (iterated P1 I k)) === (Blist (iterated P2 I k)) /\
(Alist (iterated P1 I k)) === (Alist (iterated P2 I k))/\
Subset (timesof (Blist (iterated P1 I k))) (timesof (tilln (orders I) (k-1)))/\
Subset (timesof (Alist (iterated P1 I k))) (timesof (tilln (orders I) (k-1)))/\
(not (matchable (Blist (iterated P1 I k)) (Alist (iterated P1 I k)))) /\
(NoDup (ids (Blist (iterated P1 I k)))) /\ (NoDup (ids (Alist (iterated P1 I k))))/\
(NoDup (timesof (Blist (iterated P1 I k)))) /\ (NoDup (timesof (Alist (iterated P1 I k))))/\  
(Subset (ids (Blist (iterated P1 I k))) (ids (tilln (orders I) (k-1))))/\
(Subset (ids (Alist (iterated P1 I k))) (ids (tilln (orders I) (k-1))))/\
(cmd (nth (k-1) I tau0) = del -> k>0 ->
   ~In (id (ord (nth (k-1) I tau0))) (ids (Blist (iterated P1 I k)))) /\
(cmd (nth (k-1) I tau0) = del -> k>0 ->
   ~In (id (ord (nth (k-1) I tau0))) (ids (Alist (iterated P1 I k)))).
Proof.
    { assert (~ matchable nil nil) as Hnil.
      { intro. unfold matchable in H. firstorder. }
      induction k. 
        { intros H H0 H1. simpl. repeat split. 
          all:auto. }
        { (*induction step*) 
          unfold iterated. intros H H0 H1. 
          destruct(Nat.ltb (|I|) (S k)) eqn:Hlength.
          { simpl. repeat split. all:auto. }
          { (*-------The case when length(I)>=k+1-----------*)
            move /leP in Hlength. 
            assert(S k <= (| I |)) as H2. lia.
            revert IHk. unfold iterated. 
            destruct (Nat.ltb (| I |)) eqn:Hl2.
            { move /ltP in Hl2. lia. }
            { set(B10:= (Blist (iterate P1 I k))).  
              set(A10:= (Alist (iterate P1 I k))).
              set(B20:= (Blist (iterate P2 I k))). 
              set(A20:= (Alist (iterate P2 I k))).
              replace (S k -1) with k. 2:{  lia. }
              set (tau:=(nth k I tau0)). 
              intro IHk. assert(Hstruct:=H1). assert(Hstruct2:=H1).
              specialize (IHk H). specialize (IHk H0). specialize (IHk H1).
              destruct IHk as [kmperm H3]. destruct H3 as [kbperm H3].
              destruct H3 as [kaperm H3]. destruct H3 as [kbt H3].
              destruct H3 as [kat H3].
              destruct H3 as [knm H3]. destruct H3 as [knbdi H3].
              destruct H3 as [kndai H3]. destruct H3 as [kndbt H3]. 
              destruct H3 as [kndat H3]. destruct H3 as [kinclidb H3].
              destruct H3 as [kinclida H3]. destruct H3 as [kdelb kdela]. 
              assert(Legal_input B10 A10 tau) as Hmain.
              { unfold Legal_input. unfold admissible.
                assert(NoDup (timesof (orders I))) as ndtI.
                { apply Hstruct. }
                repeat split. 
                { (*Proof of:
                  NoDup (ids (fst (Absorb B10 A10 l(cmd tau) (ord tau))))*)
                  destruct k eqn: hk. 
                  subst B10.  subst A10.  unfold Absorb. simpl. 
                  destruct (cmd tau). simpl. auto. simpl. auto. simpl. auto. 
                  unfold structured in Hstruct. destruct Hstruct as [Hid Hul].
                  specialize (Hid (S n)). replace (S (S n)) with (S n +1) in H2.
                  apply Hid in H2. destruct H2.
                  { apply Absorb_del_nodup_id. all:auto. }
                  destruct H2.
                  { apply Absorb_notIn_nodup_id. all: auto. }
                  { destruct H2 as [H2a H2b]. assert(S n >0) as Hn. lia. 
                    apply Absorb_notIn_nodup_id. all: auto. specialize (kdelb H2b).
                    specialize (kdelb Hn).  subst tau. rewrite H2a. auto.
                    specialize (kdela H2b). specialize (kdela Hn). subst tau. 
                    rewrite H2a. auto.
                  }
                  lia. 
                }
                { (*Proof of:
                  NoDup (ids (snd (Absorb B10 A10 (cmd tau) (ord tau))))*)
                  destruct k eqn: hk. 
                  subst B10.  subst A10. unfold Absorb. simpl.
                  destruct (cmd tau). simpl. auto. simpl. auto. simpl. auto. 
                  unfold structured in Hstruct. destruct Hstruct as [Hid Hul].
                  specialize (Hid (S n)). replace (S (S n)) with (S n +1) in H2.
                  apply Hid in H2. destruct H2.
                  { apply Absorb_del_nodup_id. all:auto. }
                  destruct H2.
                  { apply Absorb_notIn_nodup_id. all: auto. }
                  { destruct H2 as [H2a H2b]. assert(S n >0) as Hn. lia. 
                    apply Absorb_notIn_nodup_id. all: auto. specialize (kdelb H2b).
                    specialize (kdelb Hn).  subst tau. rewrite H2a. auto.
                    specialize (kdela H2b). specialize (kdela Hn). subst tau. 
                    rewrite H2a. auto.
                  }
                  lia. 
                }
                { (*Proof of :
                   NoDup (timesof (fst (Absorb B10 A10 (cmd tau) (ord tau))))*)
                  destruct k eqn: hk. 
                  subst B10.  subst A10. unfold Absorb. simpl.
                  destruct (cmd tau). simpl. auto. simpl. auto. simpl. auto. 
                  apply Absorb_notIn_nodup_time. 
                  { auto. } { auto. } 
                  { intro h1.  
                    assert(In (otime (ord tau)) (timesof 
                    (tilln (orders I) (S n - 1)))) as h2; eauto.
                    assert(~In (otime (ord tau)) 
                    (timesof (tilln (orders I) (S n -1)))) as hin3. subst tau. 
                    assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)) as h4. apply map_nth.
                    subst k.
                    rewrite <- h4. apply timesof_nodup_notIn. auto.
                    apply Hstruct. rewrite <- ordersI_length. lia. lia.
                    destruct (hin3 h2).
                  }
                  { intro h1.  
                    assert(In (otime (ord tau)) (timesof 
                    (tilln (orders I) (S n - 1)))) as h2. 
                    apply kat. auto. 
                    assert(~In (otime (ord tau)) 
                    (timesof (tilln (orders I) (S n -1)))) as hin3. subst tau. 
                    assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)) as h4. apply map_nth.
                    subst k.
                    rewrite <- h4. apply timesof_nodup_notIn. 
                    auto. apply Hstruct. rewrite <- ordersI_length. lia. lia.
                    destruct (hin3 h2).
                  }
                }
                { (*Proof of :
                   NoDup (timesof (snd (Absorb B10 A10 (cmd tau) (ord tau))))*)
                  destruct k eqn: hk. 
                  subst B10.  subst A10. unfold Absorb. simpl.
                  destruct (cmd tau). simpl. auto. simpl. auto. simpl. auto. 
                  apply Absorb_notIn_nodup_time. 
                  { auto. } { auto. } 
                  { intro h1.  
                    assert(In (otime (ord tau)) (timesof 
                    (tilln (orders I) (S n - 1)))) as h2; eauto.
                    assert(~In (otime (ord tau)) 
                    (timesof (tilln (orders I) (S n -1)))) as hin3. subst tau. 
                    assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)) as h4. apply map_nth.
                    subst k.
                    rewrite <- h4. apply timesof_nodup_notIn. auto.
                    apply Hstruct. rewrite <- ordersI_length. lia. lia.
                    destruct (hin3 h2).
                  }
                  { intro h1.  
                    assert(In (otime (ord tau)) (timesof 
                    (tilln (orders I) (S n - 1)))) as h2. 
                    apply kat. auto. 
                    assert(~In (otime (ord tau)) 
                    (timesof (tilln (orders I) (S n -1)))) as hin3. subst tau. 
                    assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)) as h4. apply map_nth.
                    subst k.
                    rewrite <- h4. apply timesof_nodup_notIn. 
                    auto. apply Hstruct. rewrite <- ordersI_length. lia. lia.
                    destruct (hin3 h2).
                  }
                }
                { auto. }
              }
              eapply Local_uniqueness with 
              (Process1:=P1)(Process2:=P2) in Hmain . 
              repeat split.  
              { (*1*) apply Hmain. }
              { (*2*) apply Hmain. }
              { (*3*) apply Hmain. }  
              { (*4*) (*assert(Subset (timesof B10) (timesof (tilln (orders I) k)))*)
                fold iterate in Hmain. 
                assert(included (timesof (Blist (P1 B10 A10 tau)))
                (timesof (ord tau :: B10))) as h1. apply Hmain. simpl.
                assert((timesof (Blist (P1 B10 A10 tau))) [<=]
                (timesof (ord tau :: B10))). eauto. 
                assert(timesof (ord tau :: B10) [<=] timesof (tilln (orders I) k))
                as h2.
                { assert(In (otime (ord tau)) (timesof (tilln (orders I) k))).
                  { assert(In ((nth (k) (orders I) w0)) (tilln (orders I) (k))).
                    { apply tilln_contains_nth. split. apply ordersI_nil. 
                      intro. subst I. simpl in H2. lia. rewrite <- ordersI_length.
                      lia. 
                    }
                    apply timesof_elim. assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)). apply map_nth. subst tau. rewrite <- H5.
                    auto.
                  }
                  assert(Subset (timesof (tilln (orders I) (k - 1))) 
                  (timesof (tilln (orders I) k))) as h4. apply timesof_Subset.
                  apply tilln_Subset_next.
                  simpl. unfold "[<=]". unfold "[<=]" in H3. intros. simpl in H5.
                  destruct H5. subst a. auto. eauto.
                 }
                 eauto.
               }
              { (*4*) (*assert(Subset (timesof B10) (timesof (tilln (orders I) k)))*)
                fold iterate in Hmain. 
                assert(included (timesof (Alist (P1 B10 A10 tau)))
                (timesof (ord tau :: A10))) as h1. apply Hmain. simpl.
                assert((timesof (Alist (P1 B10 A10 tau))) [<=]
                (timesof (ord tau :: A10))). eauto. 
                assert(timesof (ord tau :: A10) [<=] timesof (tilln (orders I) k))
                as h2.
                { assert(In (otime (ord tau)) (timesof (tilln (orders I) k))).
                  { assert(In ((nth (k) (orders I) w0)) (tilln (orders I) (k))).
                    { apply tilln_contains_nth. split. apply ordersI_nil. 
                      intro. subst I. simpl in H2. lia. rewrite <- ordersI_length.
                      lia. 
                    }
                    apply timesof_elim. assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)). apply map_nth. subst tau. rewrite <- H5.
                    auto.
                  }
                  assert(Subset (timesof (tilln (orders I) (k - 1))) 
                  (timesof (tilln (orders I) k))) as h4. apply timesof_Subset.
                  apply tilln_Subset_next.
                  simpl. unfold "[<=]". unfold "[<=]" in H3. intros. simpl in H5.
                  destruct H5. subst a. auto. eauto.
                 }
                 eauto.
               }
               { (*6*) fold iterate in Hmain. apply Hmain. }
               { (*7*) fold iterate in Hmain. apply Hmain. }
               { (*8*) fold iterate in Hmain. apply Hmain. }
               { (*9*) fold iterate in Hmain. apply Hmain. }
               { (*10*) fold iterate in Hmain. apply Hmain. }
               { (*11*) fold iterate in Hmain. 
                 assert(included (ids (Blist (P1 B10 A10 tau)))
                (ids (ord tau :: B10))) as h1. apply Hmain. simpl.
                assert((ids (Blist (P1 B10 A10 tau))) [<=]
                (ids (ord tau :: B10))). eauto. 
                assert(ids (ord tau :: B10) [<=] ids (tilln (orders I) k))
                as h2.
                { assert(In (id (ord tau)) (ids (tilln (orders I) k))).
                  { assert(In ((nth (k) (orders I) w0)) (tilln (orders I) (k))).
                    { apply tilln_contains_nth. split. apply ordersI_nil. 
                      intro. subst I. simpl in H2. lia. rewrite <- ordersI_length.
                      lia. 
                    }
                    apply ids_intro. assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)). apply map_nth. subst tau. rewrite <- H5.
                    auto.
                  }
                  assert(Subset (ids (tilln (orders I) (k - 1))) 
                  (ids (tilln (orders I) k))) as h4. apply ids_Subset.
                  apply tilln_Subset_next.
                  simpl. unfold "[<=]". unfold "[<=]" in H3. intros. simpl in H5.
                  destruct H5. subst a. auto. eauto.
                 }
                 eauto.
               }
               { (*11*) fold iterate in Hmain. 
                 assert(included (ids (Alist (P1 B10 A10 tau)))
                (ids (ord tau :: A10))) as h1. apply Hmain. simpl.
                assert((ids (Alist (P1 B10 A10 tau))) [<=]
                (ids (ord tau :: A10))). eauto. 
                assert(ids (ord tau :: A10) [<=] ids (tilln (orders I) k))
                as h2.
                { assert(In (id (ord tau)) (ids (tilln (orders I) k))).
                  { assert(In ((nth (k) (orders I) w0)) (tilln (orders I) (k))).
                    { apply tilln_contains_nth. split. apply ordersI_nil. 
                      intro. subst I. simpl in H2. lia. rewrite <- ordersI_length.
                      lia. 
                    }
                    apply ids_intro. assert((nth k (orders I) (ord tau0)) = 
                    ord (nth k I tau0)). apply map_nth. subst tau. rewrite <- H5.
                    auto.
                  }
                  assert(Subset (ids (tilln (orders I) (k - 1))) 
                  (ids (tilln (orders I) k))) as h4. apply ids_Subset.
                  apply tilln_Subset_next.
                  simpl. unfold "[<=]". unfold "[<=]" in H3. intros. simpl in H5.
                  destruct H5. subst a. auto. eauto.
                 }
                 eauto.
               }
               { (*13*) fold iterate in Hmain. intros. 
                 assert((cmd tau = del -> ~ In (id (ord tau)) 
                 (ids (Blist (P1 B10 A10 tau))))) as h4.
                 apply Hmain. simpl. subst tau. destruct (cmd (nth k I tau0)).
                 inversion H3. inversion H3.
                 simpl. apply h4. auto.
               }
               { (*14*) fold iterate in Hmain. intros. 
                 assert((cmd tau = del -> ~ In (id (ord tau)) 
                 (ids (Alist (P1 B10 A10 tau))))) as h4.
                 apply Hmain. simpl. subst tau. destruct (cmd (nth k I tau0)).
                 inversion H3. inversion H3.
                 simpl. apply h4. auto.
               }
               { (*15*) auto. }
               { (*16*) auto. }
               { (*17*) auto. }
               { (*18*) auto. }
             }
           }
         }
       }
Qed.


Theorem global_unique (P1 P2 :(list order)->(list order) -> instruction -> (list order)*(list order)*(list transaction))(I : list instruction)(k:nat):
(Properties P1) /\(Properties P2) /\ structured I  ->
(cform (Mlist (iterated P1 I k))) === (cform (Mlist (iterated P2 I k)))/\
(Blist (iterated P1 I k)) === (Blist (iterated P2 I k)) /\
(Alist (iterated P1 I k)) === (Alist (iterated P2 I k)).
Proof. intros. destruct H. destruct H0. split. apply global_unique_aux.
all: auto. split. apply global_unique_aux. all: auto. apply global_unique_aux.
all: auto. Qed.

End Uniqness.