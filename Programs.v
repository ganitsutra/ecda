Require Import Definitions Properties MaxMatch.
Set Implicit Arguments.

Section Programs.

(*---------------------Some Ltac used in this file ---------------------*)

Lemma liaforrun (b a : order): 
oquantity b < oquantity a -> 
~ (oquantity a - oquantity b < 1). lia. Qed.

Ltac setxy :=
  match goal with
    | [ |- ?X = ?Y ] => set(x:=X); set(y:=Y)
    | [ |- context[?X::nil = ?Y::nil]] => set(x:=X); set(y:=Y)
  end.

Ltac sety :=
  match goal with
    | [ Hlt : 2 = 2|- _ ?B = ?Y:: odiff ?B _] => set(y:=Y)
  end.

Ltac crushxyorder1 := match goal with
| [ Hxyi: _, Hxyp: _, Hxyt: _, Hxyq: _ |- ?x = ?y ] =>
        destruct x as [ix tx qx px blx], y as [iy ty qy py bly]; simpl in Hxyq;
        simpl in Hxyi; simpl in Hxyt; simpl in Hxyp;
        revert blx bly; rewrite Hxyi; rewrite Hxyq; rewrite Hxyp; rewrite Hxyt;
        intros; f_equal; rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto
end.


Ltac dlt1 := match goal with
| [ |- context[ match ?X with _ => _ end]  ]=> destruct X eqn:Hcrazy1 end.

Ltac dlt2 := match goal with
| [ |- context[ match ?X with _ => _ end]  ]=> destruct X eqn:Hcrazy2 end.


Ltac ltqo:= match goal with | [ a : order, H: ?X < 1 |- _] => 
           destruct a eqn:Hm1;simpl in H;  match goal with | 
           [ H0: (PeanoNat.Nat.ltb ?t 1 = false) |- _] => assert(Hm2:=H0);
           move /ltP in Hm2;lia end end.

Ltac ltqt:= match goal with
| [ m : transaction, H: ?X < 1 |- _] => destruct m eqn:Hm1;simpl in H;
      match goal with | [ H0: (PeanoNat.Nat.ltb ?t 1 = false) |- _] =>
      assert(Hm2:=H0);move /ltP in Hm2;lia end end.

Ltac eq1 :=
match goal with |[ |- context[(if Nat.eqb ?x ?x then _ else _)] ] => 
assert (Nat.eqb x x = true) as Heq;apply /eqP;auto;rewrite Heq;auto end.


(*---------------------End of Ltac used in this file ---------------------*)

Section Match_ask.

Fixpoint Match_ask (B A: list order)(a :order):
((list order)*(list order)*(list transaction)).
destruct B as [|b B'].
exact (nil, a::A, nil). (*When B is empty*)
destruct (oprice a - oprice b).
(*destruct ((oquantity a) - (oquantity b)).*)
refine ( match (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a))  with

(*bq=ba*) 
|inleft (right _) => (B', A, ((Mk_transaction (id b) (id a) (oquantity a) 
                           (oquantity_cond a))::nil))
(*bq>ba*)

 |inright _ => ((Mk_order (id b) (otime b) ((oquantity b) - (oquantity a)) (oprice b) 
  _)::B', A, ((Mk_transaction (id b) (id a) (oquantity a) (oquantity_cond a))::nil))
 
(*bq < ba*)
 |inleft (left _) => let BAM := (Match_ask B' A (Mk_order (id a) (otime a) ((oquantity a) - (oquantity b)) (oprice a) _ )) in  (Blist BAM, Alist BAM, (Mk_transaction (id b) (id a) (oquantity b) (oquantity_cond b))::(Mlist BAM))
 end ).
rewrite PeanoNat.Nat.ltb_nlt; apply liaforrun;auto.
rewrite PeanoNat.Nat.ltb_nlt; apply liaforrun;auto.
exact (b::B', a::A, nil). Defined.



Lemma aMlist_ask_ids (B A: list order)(a :order) : 
forall t, In t (Mlist (Match_ask B A a)) -> ida t = id a.
Proof. revert  A a. induction B as [|b B'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s.
simpl in H. destruct H. subst t. simpl. 
lia. apply IHB' with (A:=A) in H. simpl in H. lia. simpl in H.
destruct H. subst t. simpl. auto. inversion H.
simpl in H. destruct H. subst t. simpl. lia. inversion H.
simpl in H. inversion H. Qed.

Lemma ask_id_is_a_id (B A: list order)(a :order)(i:nat): 
In i (ids_ask_aux (Mlist (Match_ask B A a))) -> i = id a.
Proof. revert  A a. induction B as [|b B'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s.
simpl in H. destruct H. auto. apply IHB' with (A:=A) in H. simpl in H.
auto. simpl in H.
destruct H. auto. inversion H.
simpl in H. destruct H. auto. inversion H.
simpl in H. inversion H. Qed.



Lemma aMlist_bids_ids (B A: list order)(a :order) : 
forall i, In i (ids_bid_aux (Mlist (Match_ask B A a))) 
-> In i (ids B).

Proof. revert  A a. induction B as [|b B'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s. simpl in H. destruct H. subst i. simpl. auto. 
apply IHB' with (A:=A) in H. simpl. auto. simpl in H.
destruct H. subst i. simpl. auto. inversion H.
simpl in H. destruct H. subst i. simpl. auto. inversion H.
simpl in H. inversion H. Qed.

Lemma aMlist_Q (B A: list order)(a :order) : 
Vol (Mlist (Match_ask B A a)) <= oquantity a.
Proof. revert  A a. induction B as [|b B'].
intros. simpl. lia. intros.
simpl. destruct (oprice a - oprice b).
{  destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
  { destruct s. simpl.
    { match goal with | [ |- context [ Mlist (Match_ask B' A ?a ) ] ] => 
      set (a0:=a) end. cut ( Vol (Mlist (Match_ask B' A a0)) <= oquantity a0).
      subst a0. simpl. lia. apply IHB'.
    }
    { simpl. lia. } 
  }
  { simpl. lia. }
}
{ simpl. lia. } Qed.
     
Lemma aMlist_t_valid (B A: list order)(a :order) : forall t, 
In t (Mlist (Match_ask B A a)) -> tquantity t <= oquantity a.
Proof. revert  A a. induction B as [|b B'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s. simpl in H. destruct H. subst t. simpl. 
lia. apply IHB' with (A:=A) in H. simpl in H. lia. simpl in H.
destruct H. subst t. simpl. auto. inversion H.
simpl in H. destruct H. subst t. simpl. lia. inversion H.
simpl in H. inversion H. Qed.


Lemma aMlist_Qty_ask_zero (B A: list order)(w :order) : 
forall b : order,
(id b <> id w) -> Qty_ask (Mlist (Match_ask B A w)) (id b) = 0.
Proof. revert A w. induction B as [|b B'].
intros. simpl. auto. intros.
simpl. destruct (oprice w - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity w)) eqn:Hlr.
destruct s. simpl. destruct(Nat.eqb (id w) (id b0)) eqn:Hw. move /eqP in Hw.
lia. auto. simpl. destruct(Nat.eqb (id w) (id b0)) eqn:Hw. move /eqP in Hw.
lia. auto. simpl. destruct(Nat.eqb (id w) (id b0)) eqn:Hw. move /eqP in Hw. 
lia. auto. simpl. auto. Qed.

Lemma aMlist_Qty_bid (B A: list order)(a :order) : 
NoDup (ids (B)) -> NoDup (ids (a::A)) ->
forall t, In t (Mlist (Match_ask B A a)) -> 
Qty_bid (Mlist (Match_ask B A a)) (idb t)<= quant B (idb t).
Proof.
revert  A a. 
induction B as [|b B'].
{ intros. simpl in H1. inversion H1. }
{ intros. simpl in H1. simpl. 
  destruct (oprice a - oprice b).
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
      { revert H1. simpl.
        match goal with | [ |- context [ Mlist (Match_ask B' A ?a ) ] ] => 
        set (a0:=a) end.
        intros. 
        destruct H1. 
        { subst t. simpl.
          destruct (Nat.eqb (id b) (id b)) eqn:Hb.
          cut(Qty_bid (Mlist (Match_ask B' A a0)) (id b) = 0).
          lia. apply Qty_bid_t_zero. intro.
          apply aMlist_bids_ids in H1. simpl in H.
          assert (~In (id b) (ids B')). eauto.
          destruct (H2 H1). move /eqP in Hb. destruct Hb. auto.
       }
       { apply IHB' in H1. destruct (Nat.eqb (id b) (idb t)) eqn:Hb.
         { move /eqP in Hb. rewrite <- Hb in H1. 
           replace (quant B' (id b)) with 0 in H1.
           rewrite <- Hb. lia. symmetry. apply quant_elim. simpl in H. eauto. }
         {  auto. }
         eauto. simpl. simpl in H0. eauto.
       }
     }
     { simpl in H1. destruct H1. 2:{ inversion H1. }
       subst t. simpl.
       destruct (Nat.eqb (id b) (id b)) eqn:Hb.
       lia. lia.
     }
   }
   { simpl in H1. destruct H1. 2:{ inversion H1. }
       subst t. simpl.
       destruct (Nat.eqb (id b) (id b)) eqn:Hb.
       lia. lia.
   }
 }
 { simpl in H1. inversion H1. }
} 
Qed.

Lemma aMlist_tradable (B A: list order)(a :order) : forall t, 
In t (Mlist (Match_ask B A a)) -> price B (idb t) >= oprice a.
Proof. revert  A a. induction B as [|b B'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b) eqn:Hprice.
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s. simpl in H. destruct H. subst t. simpl. 
destruct(Nat.eqb (id b) (id b)) eqn:Hb.
lia. move /eqP in Hb. destruct Hb. auto.
simpl. apply IHB' with (A:=A) in H. simpl in H.
destruct (Nat.eqb (id b) (idb t) ) eqn:Ht. lia. lia. simpl in H.
destruct H. subst t. simpl. destruct (Nat.eqb (id b) (id b) ) eqn:Ht. lia.
auto. move /eqP in Ht. destruct Ht. auto. inversion H.
simpl in H. destruct H. subst t. simpl. 
destruct (Nat.eqb (id b) (id b) ) eqn:Ht. lia.
auto. move /eqP in Ht. destruct Ht. auto. inversion H.
simpl in H. inversion H. Qed. 

Lemma a_resident_not_matchable (B A: list order)(a :order):
Sorted bcompetitive B ->
~matchable B A -> ~matchable (Blist (Match_ask B A a)) (Alist (Match_ask B A a)).
Proof. 
revert  A a. 
induction B as [|b B'].
{ intros. simpl. firstorder. }
{ intros. simpl. 
  destruct (oprice a - oprice b) eqn:Hprice.
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
      { simpl.
        match goal with | [ |- context [ Alist (Match_ask B' A ?a ) ] ] =>
        set (a0:=a) end.
        { apply IHB'. eauto. intro. unfold matchable in H1.
          firstorder. 
        }
      }
      { simpl. intro. unfold matchable in H1. firstorder.
      }
   }
   { simpl. intro. unfold matchable in H1. simpl in H1.
     destruct H1. destruct H1. destruct H1. destruct H2.
     destruct H2. unfold tradable in H3. subst x. simpl in H3.
     destruct H0. unfold matchable. exists b. exists x0.
     constructor. auto. constructor. auto. auto.
     firstorder.
   }
 } 
 { simpl. unfold matchable. unfold tradable.
   assert(oprice a > oprice b). lia.
   intro. destruct H0. destruct H2. destruct H0. destruct H0.
   destruct H2. unfold matchable. unfold tradable.
   destruct H0;destruct H2. subst. lia. subst. 
   assert(oprice b >= oprice x).
   assert(bcompetitive b x). eauto.
   unfold bcompetitive in H0. move /orP in H0.
   destruct H0. move /ltP in H0. lia.
   move /andP in H0. destruct H0. move /eqP in H0.
   lia. lia. subst. exists x. firstorder. firstorder.
 }
} 
Qed.


Lemma aMlist_hat_B (B A: list order)(a :order) : 
NoDup (ids B) -> (Blist (Match_ask B A a)) = odiff B (bids (Mlist (Match_ask B A a)) B).
Proof. intro NDB. revert A a. induction B as [|b B'].
{ intros. simpl. auto. }
{ intros. simpl. 
  destruct (oprice a - oprice b).
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
      { match goal with | [ |- context[(Match_ask B' A ?a)] ] => set (a0:=a) end. 
        match goal with | [ |- context[(Mlist (Blist (Match_ask B' A a0), 
        Alist (Match_ask B' A a0), ?m::Mlist (Match_ask B' A a0)))] ] => 
        set (m0:=m) end.
        simpl.  dlt1.
        { rewrite IHB'. eauto. 
          replace ((bids (m0 :: Mlist (Match_ask B' A a0)) (b :: B')))
          with (b::(bids (Mlist (Match_ask B' A a0)) B')). symmetry. 
          apply odiff_elim2. eauto. eauto. symmetry. apply bids_simplify.
          auto. subst m0. simpl. auto. subst m0. simpl. auto.
          unfold Subset. intros. apply aMlist_bids_ids in H. exact.
        }
        { simpl. rewrite IHB'. eauto. assert(Hl:=n). 
          replace ((bids (m0 :: Mlist (Match_ask B' A a0)) 
          (b :: B'))) with (b::(bids (Mlist (Match_ask B' A a0)) B')) in Hl.
          simpl in Hl. destruct(Nat.eqb (id b) (id b)) eqn: Hb. lia.
          move /eqP in Hb. destruct Hb. auto. symmetry. apply bids_simplify.
          auto. subst m0. simpl. auto. subst m0. simpl. auto.
          unfold Subset. intros. apply aMlist_bids_ids in H. exact. 
        } 
     }
     { match goal with | [ |- context[(B' ,A, ?a::nil)] ] => set (m0:=a) end.
       simpl. dlt1. 
       {  replace ((bids (m0 :: nil) (b :: B')))
          with (b::(bids nil B')). simpl. rewrite bids_nil.  symmetry. 
          assert(odiff B' (b :: nil) = (odiff B' nil)).
          apply odiff_elim2 with (Omega1:=B')(Omega2:=nil)(b:=b). 
          eauto. eauto. rewrite H. apply odiff_nil. symmetry. apply bids_simplify.
          auto. subst m0. simpl. auto. subst m0. simpl. auto. simpl. auto.
       }
       {  assert(Hl:=n). 
          replace ((bids (m0 :: nil) 
          (b :: B'))) with (b::(bids nil B')) in Hl.
          simpl in Hl. destruct(Nat.eqb (id b) (id b)) eqn: Hb. lia.
          move /eqP in Hb. destruct Hb. auto. symmetry. apply bids_simplify.
          auto. subst m0. simpl. auto. subst m0. simpl. auto.
          unfold Subset. intros. simpl in H. inversion H. 
       }
     }
   }
   { match goal with | [ |- context[Mlist (?b::B' ,A, ?m::nil)] ] => set (m0:=m);
    set(b0:=b) end. simpl. 
    assert((quant (bids (m0::nil) (b::B')) (id b)) = 
    (Qty_bid (m0::nil) (id b))) as Hq.
    apply bids_id_quant. eauto. simpl;auto. simpl in Hq. 
    destruct(Nat.eqb (id b) (id b)) eqn: Hb. 2:{ move /eqP in Hb. destruct Hb. auto. }
    dlt1. 
    { assert(Hl:=l0). rewrite Hq in Hl. ltqo.
    }
    { match goal with | [|- ?x0::B' = ?y0::odiff B' ?Y0 ] => 
      set(x:=x0);set(y:=y0);set(B0:=Y0) end. 
      assert(odiff B' B0 = B') as HB0. 
      { apply odiff_elim3.  intros. subst B0.
        unfold bids in H. simpl in H. rewrite Hb in H. 
        destruct (Compare_dec.lt_dec (oquantity a + 0) 1) eqn: Ha.
        ltqo. simpl in H. 
        match goal with |[ H: context[if ?X then _ else _] |- _] =>
        destruct X eqn: HX end.
        move /membP in HX. 
        apply In_b_bids_in_idb_Bi in HX.
        simpl in HX. assert(~In (id b) (ids B')). eauto.
        destruct(H0 HX). simpl in H. destruct H. subst i. 
        eauto. replace (bids_aux (m0 :: nil) (b :: B') (ids B'))
        with (bids_aux nil (b::B') (ids B')) in H. 
        assert((bids_aux nil (b :: B') (ids B')) = nil).
        apply bids_aux_nil. rewrite H0 in H. simpl in H.
        inversion H. symmetry. apply bids_aux_elim2.
        subst m0. simpl. eauto. eauto.
      }
      rewrite HB0. f_equal.
      { assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl.
        rewrite Hq. lia.
        assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
        assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
        assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.         
        crushxyorder1. 
      }
     }
   }
 }
 { dlt1.  
   { simpl.  assert ((bids nil (b :: B')) = nil) as Hb. 
     apply bids_nil.  assert(Hc:=l). rewrite Hb in Hc.
     simpl in Hc. ltqo.
   }
   {
     simpl.  assert(2=2) as Hlt. auto. sety.  assert (odiff B' nil = B') as H0.
     apply odiff_nil. assert ((bids nil (b :: B')) = nil) as Hb. 
     apply bids_nil. rewrite Hb. rewrite H0. f_equal. 
     assert (oquantity b = oquantity y) as Hxyq. destruct b. subst y;simpl.
     rewrite Hb. simpl. lia.
     assert (id b = id y) as Hxyi. subst y;simpl;auto.
     assert (otime b = otime y) as Hxyt. subst y;simpl;auto.
     assert (oprice b = oprice y) as Hxyp. subst y;simpl;auto. 
     destruct (Nat.eqb (id b) (id b)) eqn: Hp. auto.
     move /eqP in Hp;destruct Hp;auto.
     destruct b as [ix tx qx px blx], y as [iy ty qy py bly]; simpl in Hxyq;
     simpl in Hxyi; simpl in Hxyt; simpl in Hxyp. simpl in n0. simpl in Hcrazy1. 
     revert n0 Hcrazy1 bly. rewrite Hb.
     simpl. intros. rewrite Hxyi. rewrite Hxyp; rewrite Hxyt.
     assert (qx - 0 = qx) as Hq. lia. 
     revert Hcrazy1. revert n0 bly. rewrite Hq.
     revert Hb. intros. clear Hb. simpl in NDB. revert bly. revert blx. 
     rewrite Hxyq. intros; f_equal. 
     rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto.
   }
 }
} Qed.



Lemma aMlist_ptp_bid (B A: list order)(a :order):
NoDup (ids B) -> Sorted bcompetitive B ->
Condition2a (Mlist (Match_ask B A a)) (B).
Proof.
unfold Condition2a.  intros H H0 b b' H1. destruct H1 as [H1 H2]. 
destruct H2 as [H2 H3]. 
destruct H3 as [H3 H4]. revert  A a H1 H4. 
induction B as [|b0 B'].
{ intros. simpl in H1. inversion H1. }
{ intros. destruct H1;destruct H2.
  { subst. destruct H3.
    destruct H2. unfold eqcompetitive.
    apply /andP. split. apply /eqP. auto. apply /eqP. auto. 
  } 
  { subst. revert H4. simpl.
   destruct (oprice a - oprice b) eqn:Hb.
   { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
      { simpl. intros. destruct H4.
        { dlt2. 
            { match goal with |[|- context[Mlist (Match_ask B' A ?x)]] =>
              set(a0:=x) end.
              assert(Qty_bid (Mlist (Match_ask B' A a0)) (id b) = 0). 
              apply Qty_bid_t_zero.
              intro. apply aMlist_bids_ids in H4. assert(~In (id b) (ids B')). 
              eauto. destruct (H5 H4). rewrite H4. lia.
            }
            { move /eqP in Hcrazy2. destruct Hcrazy2. auto. } 
       } 
       { destruct(Nat.eqb (id b) (id b)) eqn: Hbb.
          2:{ move /eqP in Hbb. destruct Hbb;auto. } 
          match goal with |[|- context[Mlist (Match_ask B' A ?x)]] => 
          set(a0:=x) end.
          assert(Qty_bid (Mlist (Match_ask B' A a0)) (id b) = 0). 
          apply Qty_bid_t_zero. intro. apply aMlist_bids_ids in H4.
          assert(~In (id b) (ids B')). eauto.
          destruct (H5 H4). rewrite H4. lia.
       }
     }
     { simpl. intros. destruct H4.
        { destruct(Nat.eqb (id b) (id b)) eqn: Hbb.
          2:{ move /eqP in Hbb. destruct Hbb;auto. } 
          lia.
        }
        { inversion H1. }
     }
   }
   { match goal with |[|- context[Mlist (?bx::B', A, ?ax::nil)]] => 
     set(a0:=ax);set(b1:=bx) end. simpl. intros.
     destruct H4. assert(price (b::B') (id b) = oprice b).
     apply price_elim1. eauto. assert(price (b::B') (id b') = oprice b').
     apply price_elim1. split. simpl. auto. eauto. assert (oprice b = oprice b').
     rewrite<-H4. rewrite<-H5. rewrite<-H1. auto. 
     assert(timestamp (b::B') (id b) = otime b).
     apply timestamp_elim1. eauto. assert(timestamp (b::B') (id b') = otime b').
     apply timestamp_elim1. split. simpl. auto. eauto. assert (otime b = otime b').
     rewrite<-H7. rewrite<-H8. rewrite<-H1. auto. 
     destruct H3. unfold not in H10. unfold eqcompetitive in H10. 
     destruct H10. apply /andP. split. apply /eqP. auto. apply /eqP. auto. 
     inversion H1.
   }
  } 
  { simpl. intros. inversion H4. }
 }
 { subst. apply Sorted_elim4 with(x:=b) in H0. 
   apply bcompetitive_contadiction in H0.
   inversion H0. apply H3. apply H3. auto. }
 { revert H4. simpl.
   destruct (oprice a - oprice b0) eqn:Hb.
   { destruct (Compare_dec.lt_eq_lt_dec (oquantity b0) (oquantity a)) eqn:Hlr.
    { destruct s. 
      { simpl. intros. destruct H4.
        { assert(b0 = b'). apply nodup_ids_uniq_order with (B:=(b0::B')).
          all:auto. subst. apply Sorted_elim4 with(x:=b) in H0. 
          apply bcompetitive_contadiction in H0. inversion H0. 
          apply H3. apply H3. auto. }
        { revert H4.
          match goal with |[|- context[Mlist (Match_ask B' A ?x)]] => 
          set(a0:=x) end.
          dlt2. 
          { move /eqP in Hcrazy2. 
            assert(Qty_bid (Mlist (Match_ask B' A a0)) (id b) = 0). 
            apply Qty_bid_t_zero.
            intro. apply aMlist_bids_ids in H4. assert(~In (id b) (ids B')).
            rewrite <- Hcrazy2. eauto.
            destruct (H5 H4). rewrite H4. assert(b0 = b). 
            apply nodup_ids_uniq_order with (B:=(b0::B')). all:auto.
            subst. lia.
          }
          { intros. apply IHB'. eauto. eauto. all:auto. }
        }
    }
    { simpl. intros. destruct H4.
        { assert(b0 = b'). apply nodup_ids_uniq_order with (B:=(b0::B')).
          all:auto. subst. apply Sorted_elim4 with(x:=b) in H0. 
          apply bcompetitive_contadiction in H0. inversion H0. 
          apply H3. apply H3. auto.
        }
        { inversion H4. }
     }
   }
   { { simpl. intros. destruct H4.
        { assert(b0 = b'). apply nodup_ids_uniq_order with (B:=(b0::B')).
          all:auto. subst. apply Sorted_elim4 with(x:=b) in H0. 
          apply bcompetitive_contadiction in H0. inversion H0. 
          apply H3. apply H3. auto.
        }
        { inversion H4. }
     }
   }
 }
 { simpl. auto. }
 }
}
Qed.

Lemma aMlist_hat_A (B A: list order)(a :order) : 
NoDup (ids B) -> NoDup (ids (a::A))-> 
(Alist (Match_ask B A a)) = odiff (a::A) (asks (Mlist (Match_ask B A a)) (a::A)).
Proof. intro NDB. revert A a. induction B as [|b B'].
{ intros. assert(asks nil (a :: A)= nil). unfold asks.
  cut(asks_aux nil (a :: A) (ids (a :: A)) = nil). intros. rewrite H0.
  simpl. auto. apply asks_aux_nil. rewrite H0. rewrite odiff_elim3.
  simpl. auto. auto. simpl;auto.
}
{ intros. simpl. 
  destruct (oprice a - oprice b).
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
      { match goal with | [ |- context[(Match_ask B' A ?a)] ] => set (a0:=a) end. 
        match goal with | [ |- context[(Mlist (Blist (Match_ask B' A a0), 
        Alist (Match_ask B' A a0), ?m::Mlist (Match_ask B' A a0)))] ] =>
        set (m0:=m) end.
        dlt1.  
        {  rewrite IHB'. eauto. simpl. simpl in H. auto. simpl in l0.  
          assert(quant (asks (m0 :: Mlist (Match_ask B' A a0)) (a :: A)) (id a) 
          >= oquantity a). lia.         
           fold odiff. assert(Hq:=H0).
          rewrite asks_id_quant in H0.
          eauto. simpl;auto. simpl in H0. destruct(Nat.eqb (id a) (id a)) eqn:Ha.
          2:{ move /eqP in Ha. destruct Ha. auto. }  
          match goal with |[ |- ?A0 = ?B0] => replace A0 with 
          (odiff (a0 :: A) (asks (Mlist (Match_ask B' A a0)) (a0 :: A))); 
          replace B0 with 
          (odiff A (asks (m0 :: Mlist (Match_ask B' A a0)) (a :: A))) end.
          assert(Qty_ask (Mlist (Match_ask B' A a0)) (id a)>=
          oquantity a - oquantity b).
          lia. rewrite <- asks_id_quant with (B:=a0::A) in H1.
          assert(odiff (a0 :: A) (asks (Mlist (Match_ask B' A a0)) (a0 :: A)) = 
          odiff A (asks (Mlist (Match_ask B' A a0)) (a0 :: A))). apply odiff_elim4.
          subst a0;simpl;lia. eauto. rewrite H2. replace 
          (odiff A (asks (Mlist (Match_ask B' A a0)) (a0 :: A))) with A.
          symmetry. apply odiff_elim3. intros. 
          { apply id_In_ids_asks2 in H3. simpl in H3.
            destruct H3. subst i. eauto. apply ask_id_is_a_id in H3. subst a0.
            simpl in H3. subst i. eauto. } eauto. symmetry.
          apply odiff_elim3. intros. { apply id_In_ids_asks2 in H3.
          apply ask_id_is_a_id in H3. subst a0.
          simpl in H3. subst i. eauto. } eauto. eauto. subst a0. 
          simpl. auto. simpl. auto. simpl;auto. simpl;auto. 
        }
        {  destruct(Compare_dec.lt_dec (oquantity b + 
           Qty_ask (Mlist (Match_ask B' A a0)) (id a)) 1) eqn:Hlr2.
          { ltqo. }
        { rewrite IHB'. eauto. simpl. simpl in H. auto. simpl. 
          assert(quant (asks (m0 :: Mlist (Match_ask B' A a0)) (a :: A)) (id a) = 
          Qty_ask (m0 :: Mlist (Match_ask B' A a0)) (id a)). 
          { apply asks_id_quant. eauto. simpl. auto. } 
          simpl in H0. destruct(Nat.eqb (id a) (id a)) eqn: Ha.
          2:{ move /eqP in Ha. destruct Ha;auto. } 
          assert(Qty_ask (Mlist (Match_ask B' A a0)) (id a) = 
           quant (asks (Mlist (Match_ask B' A a0))
            (a0 :: A)) (id a)). symmetry;apply asks_id_quant. auto. simpl;auto.
            rewrite H1 in H0.
            dlt2. assert(Hn:=n). rewrite H0 in Hn. lia. 
            assert(odiff A (asks (Mlist (Match_ask B' A a0)) (a0 :: A)) = 
             A). apply odiff_elim3. intros. { apply id_In_ids_asks2 in H2.
          apply ask_id_is_a_id in H2. subst a0.
          simpl in H2. subst i. eauto. } eauto.
             rewrite H2. assert(odiff A 
             (asks (m0 :: Mlist (Match_ask B' A a0)) (a :: A)) 
             = A).  apply odiff_elim3. intros.           
             { apply id_In_ids_asks2 in H3. simpl in H3.
            destruct H3. subst i. eauto. apply ask_id_is_a_id in H3. subst a0.
            simpl in H3. subst i. eauto. } eauto.
             rewrite H3.  f_equal. setxy. assert (oquantity x = oquantity y) as Hxyq.
             subst x;subst y;simpl. lia.
             assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
             assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
             assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.
             crushxyorder1. } 
     }
    }
     {  match goal with | [ |- context[(B' ,A, ?a::nil)] ] => set (a0:=a) end.
        simpl. dlt1. 
        { unfold asks. simpl. destruct (Nat.eqb (id a) (id a)) eqn:Ha.
           { dlt2. ltqo. replace (asks_aux (a0::nil) (a::A) (ids A)) 
           with  (asks_aux nil (a::A) (ids A)). 
           assert (asks_aux nil (a :: A) (ids A)=nil). apply asks_aux_nil.
           rewrite H0.
           symmetry;apply odiff_elim3. simpl. intros. destruct H1.
           subst i. eauto. inversion H1. eauto. symmetry;apply asks_aux_elim2.
           subst a0. simpl. eauto.
           } move /eqP in Ha. destruct Ha. auto.
        }
        { assert((quant (asks (a0::nil) (a::A)) (id a)) = 
          (Qty_ask (a0::nil) (id a))) as Hq.  apply asks_id_quant. eauto. 
          simpl;auto. simpl in Hq. destruct(Nat.eqb (id a) (id a)) eqn: Ha. 
          2:{ move /eqP in Ha. destruct Ha. auto. } assert(Hq1:=n).
          rewrite Hq in Hq1. lia.
        }
     }
   }
   { match goal with | [ |- context[Mlist (?b::B' ,A, ?m::nil)] ] => set (m0:=m);
    set(b0:=b) end. simpl. 
    dlt1. 
    { symmetry;apply odiff_elim3.
      intros. simpl in H0. unfold asks in H0.
      replace ((uniq (asks_aux (m0 :: nil) (a :: A) (ids (a :: A)))))
      with (a::(uniq (asks_aux ( nil) ( A) (ids ( A))))) in H0.
      simpl in H0. destruct H0. subst i. eauto. 
      assert (asks_aux nil A (ids A)=nil). apply asks_aux_nil.
      rewrite H1 in H0. simpl in H0. inversion H0. symmetry. 
      apply asks_simplify. eauto. subst m0. simpl. auto. subst m0.
      simpl. auto. simpl. auto. eauto.
    }
    { assert((quant (asks (m0::nil) (a::A)) (id a)) = 
      (Qty_ask (m0::nil) (id a))) as Hq. apply asks_id_quant. eauto.
      simpl;auto. simpl in Hq. destruct(Nat.eqb (id a) (id a)) eqn: Ha. 
      2:{ move /eqP in Ha. destruct Ha. auto. } assert(Hq1:=n).
      rewrite Hq in Hq1. lia. 
    }
   }
 }
 { dlt1. 
   { simpl in l. assert(Hl:=l).  assert((asks nil (a :: A)) = nil). unfold asks. 
     simpl. assert((asks_aux nil (a :: A) (ids A)) = nil). apply asks_aux_nil
      with(B:=(a::A))(Bi:=(ids A)). rewrite H0.  simpl;auto. rewrite H0 in Hl.
      simpl in Hl. ltqo. }
   { simpl. assert((asks nil (a :: A)) = nil). unfold asks. 
     simpl. assert((asks_aux nil (a :: A) (ids A)) = nil). apply asks_aux_nil
      with(B:=(a::A))(Bi:=(ids A)). rewrite H0. auto. 
      replace (odiff A (asks nil (a :: A))) with A. f_equal.
      match goal with | [ |- a= ?x0 ] =>set(y:=x0) end.
      assert (oquantity a = oquantity y) as Hxyq. subst y;simpl. 
      rewrite H0. simpl. lia.
      assert (id a = id y) as Hxyi. subst y;simpl;auto.
      assert (otime a = otime y) as Hxyt. subst y;simpl;auto.
      assert (oprice a = oprice y) as Hxyp. subst y;simpl;auto.
      destruct (Nat.eqb (id a) (id a)) eqn:Ha. auto. move /eqP in Ha.
      destruct Ha. auto. destruct a as [ix tx qx px blx], y as [iy ty qy py bly].
      simpl in Hxyq;  clear H H0 n0 Hcrazy1 n. 
      simpl in Hxyi; simpl in Hxyt; simpl in Hxyp;
      revert blx bly; rewrite Hxyi; rewrite Hxyq; rewrite Hxyp; rewrite Hxyt;
      intros; f_equal; rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto.
      rewrite H0. symmetry;apply odiff_elim3. simpl. auto. eauto. }
 }
} Qed.

End Match_ask.

(*--------------------Program and it's properties for match bid*)


Section Match_bid.

Fixpoint Match_bid (B A: list order)(b :order):((list order)*(list order)*(list transaction)).
destruct A as [|a A'].
  exact (b::B, nil, nil).
  destruct (oprice a - oprice b). (*destruct ((oquantity b) - (oquantity a)).*)
    refine ( match (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a))  with
    |inleft (right _) => (B, A', ((Mk_transaction (id b) (id a) (oquantity b) 
                          (oquantity_cond b))::nil)) (*bq=ba*) 
    |inleft (left _) => (B, (Mk_order (id a) (otime a) ((oquantity a) - (oquantity b))
                         (oprice a) _)::A', ((Mk_transaction (id b) (id a) (oquantity b) 
                         (oquantity_cond b))::nil)) (*aq>bq*)
    |inright _ => let BAM:= (Match_bid B A' (Mk_order (id b) (otime b) ((oquantity b) 
                - (oquantity a)) (oprice b) _ )) in (Blist BAM, Alist BAM, (Mk_transaction 
                (id b) (id a) (oquantity a) (oquantity_cond a))::(Mlist BAM)) end ). (*bq > ba*)
    rewrite PeanoNat.Nat.ltb_nlt; apply liaforrun;auto. 
    rewrite PeanoNat.Nat.ltb_nlt; apply liaforrun;auto.
  exact (b::B, a::A', nil). Defined.



Lemma bMlist_bid_ids (B A: list order)(b :order) : 
forall t, In t (Mlist (Match_bid B A b)) -> idb t = id b.
Proof. revert  B b. induction A as [|a A'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s.
simpl in H. destruct H. subst t. simpl. 
lia. inversion H. simpl in H.
destruct H. subst t. simpl. auto.
inversion H. simpl in H. destruct H. 
subst t. simpl.  auto. apply IHA' with (B:=B) in H. simpl in H. 
auto. simpl in H. inversion H. Qed.

Lemma bid_id_is_b_id (B A: list order)(b :order)(i:nat): 
In i (ids_bid_aux (Mlist (Match_bid B A b))) -> i = id b.
Proof. revert  B b. induction A as [|a A'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s.
simpl in H. destruct H. auto. inversion H.
simpl in H. destruct H. auto. inversion H.
simpl in H. destruct H. auto.
apply IHA' with (B:=B) in H. simpl in H.
auto. simpl in H. inversion H. Qed.

Lemma bMlist_asks_ids (B A: list order)(b :order) : 
forall i, In i (ids_ask_aux (Mlist (Match_bid B A b))) 
-> In i (ids A).
Proof. revert  B b. induction A as [|a A'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s.
simpl in H. destruct H. subst i. simpl. auto. inversion H.
simpl in H. destruct H. subst i. simpl. auto. inversion H.
simpl in H. destruct H. simpl. auto.
apply IHA' with (B:=B) in H. simpl. auto. simpl in H. inversion H. Qed.

Lemma bMlist_Q (B A: list order)(b :order) : 
Vol (Mlist (Match_bid B A b)) <= oquantity b.
Proof.  revert  B b. induction A as [|a A'].
intros. simpl. lia. intros.
simpl. destruct (oprice a - oprice b).
{  destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
  { destruct s. simpl. lia. simpl. lia. }
  { simpl. match goal with | [ |- context [ Mlist (Match_bid B A' ?b ) ] ] => set (b0:=b) end.
      cut ( Vol (Mlist (Match_bid B A' b0)) <= oquantity b0).
      subst b0. simpl. lia. apply IHA'.
    } }
  { simpl. lia. } Qed.
     
Lemma bMlist_t_valid (B A: list order)(b :order) : forall t, 
In t (Mlist (Match_bid B A b)) -> tquantity t <= oquantity b.
Proof. revert  B b. induction A as [|a A'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b).
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s.
simpl in H. destruct H. subst t. simpl. 
lia. inversion H.
simpl in H. destruct H. subst t. simpl. lia. inversion H.
simpl in H. destruct H. subst t. simpl. lia.
apply IHA' with (B:=B) in H. simpl in H. lia. simpl in H.
 inversion H. Qed.


Lemma bMlist_Qty_bid_zero (B A: list order)(w :order) : 
forall b : order,
(id b <> id w) -> Qty_bid (Mlist (Match_bid B A w)) (id b) = 0.
Proof. revert  B w. induction A as [|a A'].
intros. simpl. auto. intros.
simpl. destruct (oprice a - oprice w).
destruct (Compare_dec.lt_eq_lt_dec (oquantity w) (oquantity a)) eqn:Hlr.
destruct s.
simpl. destruct(Nat.eqb (id w) (id b)) eqn:Hw. move /eqP in Hw.
lia. auto. simpl.
destruct(Nat.eqb (id w) (id b)) eqn:Hw. move /eqP in Hw. lia. auto.
simpl. destruct(Nat.eqb (id w) (id b)) eqn:Hw. move /eqP in Hw. lia. 
apply IHA'. simpl. auto. simpl. auto. Qed.


Lemma bMlist_Qty_ask (B A: list order)(b :order) : 
NoDup (ids A) -> NoDup (ids (b::B)) ->
forall t, In t (Mlist (Match_bid B A b)) -> 
Qty_ask (Mlist (Match_bid B A b)) (ida t)<= quant A (ida t).
Proof.
 revert  B b. induction A as [|a A'].
{ intros. simpl in H1. inversion H1. }
{ intros. simpl in H1. simpl. 
  destruct (oprice a - oprice b).
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
     { simpl in H1. destruct H1. 2:{ inversion H1. }
       subst t. simpl.
       destruct (Nat.eqb (id a) (id a)) eqn:Hb.
       lia. lia.
     } 
   { simpl in H1. destruct H1. 2:{ inversion H1. }
       subst t. simpl.
       destruct (Nat.eqb (id a) (id a)) eqn:Hb.
       lia. lia.
   }
 }
 { revert H1. simpl.
        match goal with | [ |- context [ Mlist (Match_bid B A' ?b ) ] ] => 
        set (b0:=b) end.
        intros. 
        destruct H1. 
        { subst t. simpl.
          destruct (Nat.eqb (id a) (id a)) eqn:Hb.
          cut(Qty_ask (Mlist (Match_bid B A' b0)) (id a) = 0).
          lia. apply Qty_ask_t_zero. intro.
          apply bMlist_asks_ids in H1. simpl in H.
          assert (~In (id a) (ids A')). eauto.
          destruct (H2 H1). move /eqP in Hb. destruct Hb. auto.
       }
       { apply IHA' in H1. destruct (Nat.eqb (id a) (ida t)) eqn:Hb.
         { move /eqP in Hb. rewrite <- Hb in H1. replace (quant A' (id a))
           with 0 in H1. rewrite <- Hb. lia. symmetry. 
           apply quant_elim. simpl in H. eauto. }
         {  auto. }
         eauto. simpl. simpl in H0. eauto.
       }
     }
   }

 { simpl in H1. inversion H1. }
} 
Qed.



Lemma bMlist_tradable (B A: list order)(b :order) : forall t, 
In t (Mlist (Match_bid B A b)) -> price A (ida t) <= oprice b.
Proof.  revert  B b. induction A as [|a A'].
intros. simpl in H. inversion H. intros.
simpl in H. destruct (oprice a - oprice b) eqn:Hprice.
destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
destruct s.
simpl in H. destruct H. subst t. simpl. 
destruct (Nat.eqb (id a) (id a) ) eqn:Ht. lia.
 move /eqP in Ht. destruct Ht. auto. inversion H.
simpl in H. destruct H. subst t. simpl. 
destruct(Nat.eqb (id a) (id a)) eqn:Hb.
lia. move /eqP in Hb. destruct Hb. auto. inversion H.
simpl in H. destruct H. subst t. simpl. 
destruct(Nat.eqb (id a) (id a)) eqn:Hb.
lia. move /eqP in Hb. destruct Hb. auto. 
apply IHA' with (B:=B) in H. simpl in H. simpl.
 destruct (Nat.eqb (id a) (ida t) ) eqn:Ht. lia. lia. simpl in H. inversion H.
Qed. 

Lemma b_resident_not_matchable (B A: list order)(b :order):
Sorted acompetitive A ->
~matchable B A -> ~matchable (Blist (Match_bid B A b)) (Alist (Match_bid B A b)).
Proof. 
 revert  B b. induction A as [|a A'].
{ intros. simpl. firstorder. }
{ intros. simpl. 
  destruct (oprice a - oprice b) eqn:Hprice.
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
   { simpl. intro. unfold matchable in H1. simpl in H1.
     destruct H1. destruct H1. destruct H1. destruct H1.
     destruct H2. unfold tradable in H3. subst x0. simpl in H3.
     destruct H0. unfold matchable. exists x. exists a.
     constructor. auto. constructor. auto. auto.
     firstorder.
   }
 {  firstorder. } }
 { simpl.
   match goal with | [ |- context [ Blist (Match_bid B A' ?a ) ] ] => 
   set (b0:=b) end.
        { apply IHA'. eauto. intro. unfold matchable in H1.
          firstorder. 
        }
      }
   }
 {
  simpl. unfold matchable. unfold tradable.
  assert(oprice a > oprice b). lia.
  intro. destruct H0. destruct H2. destruct H0. destruct H0.
  destruct H2. unfold matchable. unfold tradable.
  destruct H0;destruct H2. subst. lia. subst. 
  assert(oprice x >= oprice b). lia. exists x. exists x0.
  split.  auto. split. auto. auto.
  subst.
  assert(acompetitive a x0). eauto.
  unfold acompetitive in H2. move /orP in H2.
  destruct H2. move /ltP in H2. lia.
  move /andP in H2. destruct H2. move /eqP in H2.
  lia. firstorder.
 }
} 
Qed.


Lemma bMlist_hat_A (B A: list order)(b :order) : 
NoDup (ids A) -> (Alist (Match_bid B A b)) = odiff A (asks (Mlist (Match_bid B A b)) A).
Proof. intro NDB. revert B b. induction A as [|a A'].
{ intros. simpl. auto. }
{ intros. simpl. 
  destruct (oprice a - oprice b).
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
    match goal with | [ |- context[Mlist (B ,?a::A', ?m::nil)] ] => 
    set (m0:=m);
    set(a0:=a) end. simpl. 
    assert((quant (asks (m0::nil) (a::A')) (id a)) = 
    (Qty_ask (m0::nil) (id a))) as Hq.
    apply asks_id_quant. eauto. simpl;auto. simpl in Hq. 
    destruct(Nat.eqb (id a) (id a)) eqn: Hb. 
    2:{ move /eqP in Hb. destruct Hb. auto. }
    dlt1. 
    { assert(Hl:=l0). rewrite Hq in Hl. ltqo.
    }
    { match goal with | [|- ?x0::A' = ?y0::odiff A' ?Y0 ] => 
      set(x:=x0);set(y:=y0);set(A0:=Y0) end. 
      assert(odiff A' A0 = A') as HA0. 
      { apply odiff_elim3.  intros. subst A0.
        unfold asks in H. simpl in H. rewrite Hb in H. 
        destruct (Compare_dec.lt_dec (oquantity b + 0) 1) eqn: Ha.
        ltqo. simpl in H. 
        match goal with |[ H: context[if ?X then _ else _] |- _] => 
        destruct X eqn: HX end.
        move /membP in HX. 
        apply In_a_asks_in_ida_Bi in HX.
        simpl in HX. assert(~In (id a) (ids A')). eauto.
        destruct(H0 HX). simpl in H. destruct H. subst i. 
        eauto. replace (asks_aux (m0 :: nil) (a :: A') (ids A'))
        with (asks_aux nil (a::A') (ids A')) in H. 
        assert((asks_aux nil (a :: A') (ids A')) = nil).
        apply asks_aux_nil. rewrite H0 in H. simpl in H.
        inversion H. symmetry. apply asks_aux_elim2.
        subst m0. simpl. eauto. eauto.
      }
      rewrite HA0. f_equal.
      { assert (oquantity x = oquantity y) as Hxyq. subst x;subst y;simpl.
        rewrite Hq. lia.
        assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
        assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
        assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.         
        crushxyorder1. 
      }
     }    
     simpl. 
     match goal with | [ |- context[(?m::nil)] ] => set (m0:=m);
     set(b0:=b) end. dlt1. 
     {
        replace ((asks (m0 :: nil) 
        (a :: A'))) with (a::(asks nil A')). rewrite asks_nil.
        rewrite odiff_elim2. eauto. eauto. rewrite odiff_nil. auto.
        symmetry. apply asks_simplify. eauto. subst m0. simpl. auto.
        subst m0. simpl. auto. simpl. auto.
     }
     { simpl.  assert(Hc:=n). replace ((asks (m0 :: nil) 
        (a :: A'))) with (a::(asks nil A')) in Hc. 
        assert ((asks nil A') = nil) as Hb. 
        apply asks_nil. rewrite Hb in Hc.
        simpl in Hc. destruct(Nat.eqb (id a) (id a)) eqn: Hb1. lia.
        move /eqP in Hb1. destruct Hb1. auto. symmetry. apply asks_simplify.
        eauto. subst m0. simpl. auto.
        subst m0. simpl. auto. simpl. auto.
     }
   }
   { match goal with | [ |- context[(Match_bid B A' ?b)] ] => set (b0:=b) end. 
     match goal with | [ |- context[(Mlist (Blist (Match_bid B A' b0), 
     Alist (Match_bid B A' b0), ?m::Mlist (Match_bid B A' b0)))] ] => 
     set (m0:=m) end.
     simpl.  dlt1.
        { rewrite IHA'. eauto. replace 
          ((asks (m0 :: Mlist (Match_bid B A' b0)) (a :: A')))
          with (a::(asks (Mlist (Match_bid B A' b0)) A')). symmetry. 
          apply odiff_elim2. eauto. eauto. symmetry. apply asks_simplify.
          auto. subst m0. simpl. auto. subst m0. simpl. auto.
          unfold Subset. intros. apply bMlist_asks_ids in H. exact.
        }
        { simpl. rewrite IHA'. eauto. assert(Hl:=n). 
          replace ((asks (m0 :: Mlist (Match_bid B A' b0)) 
          (a :: A'))) with (a::(asks (Mlist (Match_bid B A' b0)) A')) in Hl.
          simpl in Hl. destruct(Nat.eqb (id a) (id a)) eqn: Hb. lia.
          move /eqP in Hb. destruct Hb. auto. symmetry. apply asks_simplify.
          auto. subst m0. simpl. auto. subst m0. simpl. auto.
          unfold Subset. intros. apply bMlist_asks_ids in H. exact. 
        } 
     }
   }
   { simpl. dlt1.
    { assert(Hc:=l). rewrite asks_nil in Hc.  simpl in Hc. ltqo. }
    { assert(2=2) as Hlt. auto. sety. assert (odiff A' nil = A') as H0.
     apply odiff_nil. assert ((asks nil (a :: A')) = nil) as Hb. 
     apply asks_nil. rewrite Hb. rewrite H0. f_equal. 
     assert (oquantity a = oquantity y) as Hxyq. destruct a. subst y;simpl.
     rewrite Hb. simpl. lia.
     assert (id a = id y) as Hxyi. subst y;simpl;auto.
     assert (otime a = otime y) as Hxyt. subst y;simpl;auto.
     assert (oprice a = oprice y) as Hxyp. subst y;simpl;auto. 
     destruct (Nat.eqb (id a) (id a)) eqn: Hp. auto.
     move /eqP in Hp;destruct Hp;auto.
     destruct a as [ix tx qx px blx], y as [iy ty qy py bly]; simpl in Hxyq;
     simpl in Hxyi; simpl in Hxyt; simpl in Hxyp. simpl in n0. simpl in Hcrazy1. 
     revert n0 Hcrazy1 bly. rewrite Hb.
     simpl. intros. rewrite Hxyi. rewrite Hxyp; rewrite Hxyt.
     assert (qx - 0 = qx) as Hq. lia. 
     revert Hcrazy1. revert n0 bly. rewrite Hq.
     revert Hb. intros. clear Hb. simpl in NDB. revert bly. revert blx. 
     rewrite Hxyq. intros; f_equal. 
     rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto.
   }
  }
 }
Qed.



Lemma bMlist_ptp_ask (B A: list order)(b :order):
NoDup (ids A) -> Sorted acompetitive A ->
Condition2b (Mlist (Match_bid B A b)) (A).
Proof.
unfold Condition2b.  intros H H0 a a' H1. destruct H1 as [H1 H2]. 
destruct H2 as [H2 H3]. 
destruct H3 as [H3 H4]. revert B b H1 H4. 
induction A as [|a0 A'].
{ intros. simpl in H1. inversion H1. }
{ intros. destruct H1;destruct H2.
  { subst. destruct H3.
    destruct H2. unfold eqcompetitive.
    apply /andP. split. apply /eqP. auto. apply /eqP. auto. 
  } 
  { subst. revert H4. simpl.
   destruct (oprice a - oprice b) eqn:Hb.
   { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s.
        { simpl. destruct(Nat.eqb (id a) (id a)) eqn: Hbb.
          2:{ move /eqP in Hbb. destruct Hbb;auto. }
          intros. destruct H4. 
          { assert(a = a'). apply nodup_ids_uniq_order with (B:=(a::A')).
          all:auto. subst. apply Sorted_elim4 with(x:=a') in H0. 
          apply acompetitive_contadiction in H0. inversion H0. 
          apply H3. apply H3. auto.
        }
        { inversion H1. }
        }
        { simpl. destruct(Nat.eqb (id a) (id a)) eqn: Hbb.
          2:{ move /eqP in Hbb. destruct Hbb;auto. }
          intros. destruct H4. 
          { assert(a = a'). apply nodup_ids_uniq_order with (B:=(a::A')).
          all:auto. subst. apply Sorted_elim4 with(x:=a') in H0. 
          apply acompetitive_contadiction in H0. inversion H0. 
          apply H3. apply H3. auto.
        }
        { inversion H1. }
        }
      }        
      simpl. intros. destruct H4. 
      { assert(a = a'). apply nodup_ids_uniq_order with (B:=(a::A')).
      all:auto. subst. apply Sorted_elim4 with(x:=a') in H0. 
      apply acompetitive_contadiction in H0. inversion H0. 
      apply H3. apply H3. auto.
      }
      destruct(Nat.eqb (id a) (id a)) eqn: Hbb.
      2:{ move /eqP in Hbb. destruct Hbb;auto. }
      simpl. match goal with |[|- context[Mlist (Match_bid B A' ?x)]] => 
      set(b0:=x) end. assert(Qty_ask (Mlist (Match_bid B A' b0)) (id a) = 0). 
      apply Qty_ask_t_zero. intro. apply bMlist_asks_ids in H4.
      assert(~In (id a) (ids A')). eauto. destruct (H5 H4).
      rewrite H4. lia.
     }
     simpl. auto.
   }
   { subst. apply Sorted_elim4 with(x:=a) in H0. 
     apply acompetitive_contadiction in H0. inversion H0.
     apply H3. apply H3. auto.
   }
   { simpl in H4.
   destruct (oprice a0 - oprice b) eqn:Hb.
   { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a0)) eqn:Hlr.
    { destruct s.
      { simpl in H4. destruct H4. 
       { assert(a0 = a'). apply nodup_ids_uniq_order with (B:=(a0::A')).
          all:auto. subst. apply Sorted_elim4 with(x:=a) in H0. 
          apply acompetitive_contadiction in H0. inversion H0. 
          apply H3. apply H3. auto.
        }
        { inversion H4. }
      }
      { simpl in H4. destruct H4. 
       { assert(a0 = a'). apply nodup_ids_uniq_order with (B:=(a0::A')).
          all:auto. subst. apply Sorted_elim4 with(x:=a) in H0. 
          apply acompetitive_contadiction in H0. inversion H0. 
          apply H3. apply H3. auto.
        }
        { inversion H4. }
      }
    }
    { simpl. simpl in H4. destruct H4. 
      { assert(a0 = a'). apply nodup_ids_uniq_order with (B:=(a0::A')).
      all:auto. subst. apply Sorted_elim4 with(x:=a) in H0. 
      apply acompetitive_contadiction in H0. inversion H0. 
      apply H3. apply H3. auto.
      }
      { simpl in H4. apply IHA' in H4. rewrite Hb. rewrite Hlr. simpl. 
        destruct (Nat.eqb (id a0) (id a)) eqn:Ha.
      { assert(a0 = a). apply nodup_ids_uniq_order with (B:=(a0::A')).
      all:auto. subst. apply ids_intro in H1.
      assert(~ In (id a) (ids A')). eauto. destruct (H5 H1). 
      } 
      { auto. }
      all:auto. eauto. eauto.
    }
  }
 }
 { simpl in H4. inversion H4. }
 }
} Qed. 

Lemma bMlist_Blist_nil (B: list order)(b :order) : 
Blist (Match_bid B nil b)  = b::B.
Proof. intros. simpl. auto. Qed.

Lemma bMlist_Mlist_nil (B: list order)(b :order) : 
Mlist (Match_bid B nil b)  = nil.
Proof. simpl. auto. Qed.

Lemma bMlist_hat_B (B A: list order)(b :order) : 
NoDup (ids A) -> NoDup (ids (b::B))-> 
(Blist (Match_bid B A b)) = odiff (b::B) (bids (Mlist (Match_bid B A b)) (b::B)).
Proof. intro NDA. revert B b. induction A as [|a A'].
{ intros. rewrite bMlist_Blist_nil. rewrite bMlist_Mlist_nil.
  rewrite bids_nil. rewrite odiff_nil. auto.
}
{ intros. simpl. 
  destruct (oprice a - oprice b).
  { destruct (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hlr.
    { destruct s. 
     { simpl. match goal with | [ |- context[(?m::nil)] ] => set (m0:=m) end.
      dlt1. 
        { replace (bids (m0 :: nil) (b :: B) )
          with (b::(bids (nil) (B))). rewrite bids_nil. rewrite odiff_elim3.
          simpl. intros. destruct H0. subst i. eauto. inversion H0. eauto. auto.
          symmetry. apply bids_simplify. eauto. subst m0. simpl. auto.
          subst m0. simpl. auto. simpl. auto.
        }
        {  assert((quant (bids (m0::nil) (b::B)) (id b)) = 
          (Qty_bid (m0::nil) (id b))) as Hq.  apply bids_id_quant. eauto. 
          simpl;auto. simpl in Hq. destruct(Nat.eqb (id b) (id b)) eqn: Ha. 
          2:{ move /eqP in Ha. destruct Ha. auto. } assert(Hq1:=n).
          rewrite Hq in Hq1. lia.
        }
      }
      simpl. match goal with | [ |- context[(?m::nil)] ] => set (m0:=m) end.
      dlt1. 
        { replace (bids (m0 :: nil) (b :: B) )
          with (b::(bids (nil) (B))). rewrite bids_nil. rewrite odiff_elim3.
          simpl. intros. destruct H0. subst i. eauto. inversion H0. eauto. auto.
          symmetry. apply bids_simplify. eauto. subst m0. simpl. auto.
          subst m0. simpl. auto. simpl. auto.
        }
        { assert((quant (bids (m0::nil) (b::B)) (id b)) = 
          (Qty_bid (m0::nil) (id b))) as Hq.  apply bids_id_quant. eauto. 
          simpl;auto. simpl in Hq. destruct(Nat.eqb (id b) (id b)) eqn: Ha. 
          2:{ move /eqP in Ha. destruct Ha. auto. } assert(Hq1:=n).
          rewrite Hq in Hq1. lia.
        }
      } 
      { simpl. match goal with | [ |- context[(Match_bid B A' ?a)] ] => 
        set (b0:=a) end. 
        match goal with | [ |- context[(?m::Mlist ?X)] ] => set (m0:=m) end. 
        dlt1.  
        { rewrite IHA'. eauto. simpl. simpl in H. auto. simpl in l0.  
          assert(quant (bids (m0 :: Mlist (Match_bid B A' b0)) (b :: B)) (id b) 
          >= oquantity b). lia. assert(Hq:=H0).
          rewrite bids_id_quant in H0.
          eauto. simpl;auto. simpl in H0. destruct(Nat.eqb (id b) (id b)) eqn:Ha.
          2:{ move /eqP in Ha. destruct Ha. auto. } 
          assert(Qty_bid (Mlist (Match_bid B A' b0)) 
          (id b)>=oquantity b - oquantity a).
          lia. rewrite <- bids_id_quant with (B:=b0::B) in H1.
          assert(odiff (b0 :: B) (bids (Mlist (Match_bid B A' b0)) (b0 :: B)) = 
          odiff B (bids (Mlist (Match_bid B A' b0)) (b0 :: B))). apply odiff_elim4.
          subst b0;simpl;lia. eauto. rewrite H2. replace 
          (odiff B (bids (Mlist (Match_bid B A' b0)) (b0 :: B))) with B.
          symmetry. apply odiff_elim3. intros. 
          { apply id_In_ids_bids2 in H3. simpl in H3.
            destruct H3. subst i. eauto. apply bid_id_is_b_id in H3. subst b0.
            simpl in H3. subst i. eauto. 
          } 
          eauto. symmetry.
          apply odiff_elim3. intros. { apply id_In_ids_bids2 in H3.
          apply bid_id_is_b_id in H3. subst b0.
          simpl in H3. subst i. eauto. } eauto. eauto. subst b0. 
          simpl. auto.
        }
        { rewrite IHA'. eauto. simpl. simpl in H. auto. simpl.
          destruct(Compare_dec.lt_dec (oquantity a + 
          Qty_bid (Mlist (Match_bid B A' b0)) (id b)) 1) eqn:Hlr2.
          { ltqo. }
          {  
          assert(quant (bids (m0 :: Mlist (Match_bid B A' b0)) (b :: B)) (id b) = 
          Qty_bid (m0 :: Mlist (Match_bid B A' b0)) (id b)). 
          { apply bids_id_quant. eauto. simpl. auto. } 
          simpl in H0. destruct(Nat.eqb (id b) (id b)) eqn: Ha.
          2:{ move /eqP in Ha. destruct Ha;auto. } 
          assert(Qty_bid (Mlist (Match_bid B A' b0)) (id b) = 
          quant (bids (Mlist (Match_bid B A' b0))  (b0 :: B)) (id b)). 
          symmetry;apply bids_id_quant. auto. simpl;auto.
          rewrite H1 in H0.
          dlt2. assert(Hn:=n). rewrite H0 in Hn. lia. 
          assert(odiff B (bids (Mlist (Match_bid B A' b0)) (b0 :: B)) = B). 
          apply odiff_elim3. intros. { apply id_In_ids_bids2 in H2.
          apply bid_id_is_b_id in H2. subst b0.
          simpl in H2. subst i. eauto. } eauto.
          rewrite H2. 
          assert(odiff B (bids (m0 :: Mlist (Match_bid B A' b0)) (b :: B)) = B).
          apply odiff_elim3. intros.
          { apply id_In_ids_bids2 in H3. simpl in H3.
            destruct H3. subst i. eauto. apply bid_id_is_b_id in H3. subst b0.
            simpl in H3. subst i. eauto. 
          } 
          eauto. rewrite H3.  f_equal. setxy. 
          assert (oquantity x = oquantity y) as Hxyq.
          subst x;subst y;simpl. lia.
          assert (id x = id y) as Hxyi. subst x;subst y;simpl;auto.
          assert (otime x = otime y) as Hxyt. subst x;subst y;simpl;auto.
          assert (oprice x = oprice y) as Hxyp. subst x;subst y;simpl;auto.
          crushxyorder1. 
          } 
     }
   }
 }
 { dlt1. 
   { simpl in l. assert(Hl:=l). rewrite bids_nil in Hl. simpl in Hl. ltqo. }
   { simpl. assert((bids nil (b :: B)) = nil). rewrite bids_nil. auto.  
     replace (odiff B (bids nil (b :: B))) with B. f_equal.
      match goal with | [ |- b= ?x0 ] =>set(y:=x0) end.
      assert (oquantity b = oquantity y) as Hxyq. subst y;simpl. 
      rewrite H0. simpl. lia.
      assert (id b = id y) as Hxyi. subst y;simpl;auto.
      assert (otime b = otime y) as Hxyt. subst y;simpl;auto.
      assert (oprice b = oprice y) as Hxyp. subst y;simpl;auto.
      destruct (Nat.eqb (id b) (id b)) eqn:Ha. auto. move /eqP in Ha.
      destruct Ha. auto. destruct b as [ix tx qx px blx], y as [iy ty qy py bly].
      simpl in Hxyq;  clear H H0 n0 Hcrazy1 n. 
      simpl in Hxyi; simpl in Hxyt; simpl in Hxyp;
      revert blx bly; rewrite Hxyi; rewrite Hxyq; rewrite Hxyp; rewrite Hxyt;
      intros; f_equal; rewrite (BoolDecidableEqDepSet.UIP _ _ blx bly); auto.
      rewrite H0. symmetry;apply odiff_elim3. simpl. auto. eauto. }
 }
} Qed.

End Match_bid.


(*--------------------Program and it's properties for Del_order*)

Section Match_del.

Definition Del_order (B A:list order)(i:nat):((list order)*(list order)*(list transaction)):= 
(delete_order B i, delete_order A i, nil).


End Match_del.


(*--------------------Main Program and it's properties-----------------*)

Definition Process_instruction (B A:list order)(tau: instruction):((list order)*(list order)*(list transaction)):=
match (cmd tau) with
|del => Del_order B A (id (ord tau))
|buy => Match_bid B (sort acompetitive A) (ord tau)
|sell => Match_ask (sort bcompetitive B) A (ord tau)
end.

Theorem Process_correct :
Properties Process_instruction.
Proof. unfold Properties. unfold Condition1. unfold Condition2a. unfold Condition2b.
unfold Condition3a. unfold Condition3b. unfold Condition3c.
intros. assert(~ matchable B A). apply H.
destruct (cmd tau) eqn:Hc. 
{
  unfold Legal_input in H. unfold admissible in H.
  unfold Absorb. unfold Absorb in H. rewrite Hc in H.  simpl in H.
  unfold Process_instruction. rewrite Hc. repeat split. 
  { simpl. apply b_resident_not_matchable. apply sort_correct.
    apply acompetitive_P. apply acompetitive_P. unfold Legal_input in H.
    apply not_matchable_perm_invariance with (B':=B)(A':=(sort acompetitive A)) in H0.
    auto. auto. eauto.
  }
  { simpl. intros. destruct H1.  destruct H2. destruct H3. apply bid_id_is_b_id in H4 as H5.
    destruct H3. destruct H1;destruct H2. 
    { subst. apply bcompetitive_contadiction in H3. inversion H3. auto. auto. }
    { subst. apply nodup_ids_uniq_order with (B:=(ord tau)::B) in H5. subst.
      apply bcompetitive_contadiction in H3. inversion H3. auto. auto. 
      destruct H. destruct H. destruct H7. eauto. auto. auto. }
    { subst b'. apply nodup_ids_uniq_order with (B:=(ord tau)::B) in H5.
      apply ids_bid_aux_intro1 in H4 as H7. destruct H7 as [t H7].
      destruct H7. apply bMlist_tradable in H2 as Hp.
      apply ids_ask_intro1 in H2. unfold fun_ids_ask in H2.
      apply uniq_intro_elim in H2.  apply bMlist_asks_ids in H2.
      apply ids_elim in H2. destruct H2 as [a H2]. destruct H2.
      rewrite <- H8 in Hp. rewrite price_elim1 in Hp.
      split. eauto. apply perm_nodup with (l:=ids A).
      apply ids_perm. eauto. apply H. assert(oprice (ord tau) <= oprice b).
      unfold bcompetitive in H3. move /orP in H3.
      destruct H3. move /ltP in H3. lia. move /andP in H3.
      destruct H3. move /eqP in H3. lia. destruct H0. unfold matchable.
      unfold tradable. exists b. exists a. repeat split. eauto.
      auto. lia. apply H. auto. auto.
    }
    { destruct H. destruct H. destruct H8. assert(~In (id (ord tau)) (ids B)). eauto.
      apply ids_intro in H2. rewrite H5 in H2. destruct (H10 H2).
    }
  }
  { simpl. intros. destruct H1.  destruct H2.  destruct H3.
    assert(Condition2b (Mlist (Match_bid B (sort acompetitive A) (ord tau)))
    (sort acompetitive A)).
    apply bMlist_ptp_ask. apply perm_nodup with (l:=ids A).
    apply ids_perm. eauto. apply H. 
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
    unfold Condition2b in H5. apply H5 with (a':=a').
    repeat split. eauto. eauto. apply H3. apply H3. auto.
  }
  { simpl. unfold Tvalid. intros. unfold valid. apply bMlist_t_valid in H1 as Hv.
    exists (ord tau). apply ids_ask_intro1 in H1 as Hia.
    unfold fun_ids_ask in Hia. apply uniq_intro_elim in Hia.
    apply bMlist_asks_ids in Hia.
    apply ids_elim in Hia. destruct Hia as [a H2]. destruct H2.
    exists a. repeat split. eauto. auto. apply bMlist_bid_ids in H1.
    auto. auto.  unfold tradable. apply bMlist_tradable in H1.
    rewrite <- H3 in H1. rewrite price_elim1 in H1.
    split. eauto. apply perm_nodup with (l:=ids A).
    apply ids_perm. eauto. apply H. lia. auto. assert(Ht:=H1).
    apply bMlist_Qty_ask in H1.
    rewrite <- H3 in H1. rewrite quant_elim1 in H1.
    split. eauto. apply perm_nodup with (l:=ids A).
    apply ids_perm. eauto. apply H.
    rewrite H3 in H1. assert( tquantity t <= 
    Qty_ask (Mlist (Match_bid B (sort acompetitive A) (ord tau))) (ida t)).
    apply Qty_ask1. auto. lia. 
    apply perm_nodup with (l:=ids A).
    apply ids_perm. eauto. apply H. apply H.
  }
  { simpl. intros. destruct H1. subst. assert(Vol (Mlist 
    (Match_bid B (sort acompetitive A) (ord tau))) >= 
    Qty_bid (Mlist (Match_bid B (sort acompetitive A) (ord tau))) (id (ord tau))).
    apply Q_vs_Qty_bid. 
    assert(Vol (Mlist (Match_bid B (sort acompetitive A) (ord tau))) <= 
    oquantity (ord tau)). apply bMlist_Q. lia. 
    assert(NoDup (id (ord tau) :: ids B)). apply H.
    apply ids_intro in H1. assert(id b <> id (ord tau)). intro. rewrite H3 in H1.
    assert(~In (id (ord tau)) (ids B)). eauto. destruct(H4 H1).
    apply bMlist_Qty_bid_zero with (A:=(sort acompetitive A))(B:=B) in H3.
    lia.
  }


  { simpl. intros. assert(Qty_ask (Mlist (Match_bid B 
    (sort acompetitive A) (ord tau))) (id a)=0
    \/Qty_ask (Mlist (Match_bid B (sort acompetitive A) (ord tau))) (id a)>0). lia.
    destruct H2. lia. apply Qty_ask_elim in H2. destruct H2 as [t H2].
    destruct H2. apply bMlist_Qty_ask in H2. rewrite H3 in H2. 
    rewrite quant_elim1 in H2. split. eauto. apply perm_nodup with (l:=ids A). 
    apply ids_perm. eauto. apply H. auto. apply perm_nodup with (l:=ids A).
    apply ids_perm. eauto. apply H. apply H.
  }
  { unfold Process_instruction. unfold Absorb. unfold fst.
    rewrite bMlist_hat_B. 
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. apply H.
    apply H. auto.
  }
  { unfold Process_instruction. unfold Absorb. unfold snd.
    rewrite bMlist_hat_A. 
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. apply H.
    set(M0:=(Mlist (Match_bid B (sort acompetitive A) (ord tau)))).
    apply odiff_perm.  apply perm_nodup with (l:=ids A). 
    apply ids_perm. eauto. apply H.
    all:auto. apply nodup_ids_asks. 
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. apply H.
    apply asks_perm with (T:=M0)(B1:=(sort acompetitive A))(B2:=A). 
    destruct tau. auto. 
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. apply H.
    apply H. eauto.  }
}
{
  unfold Legal_input in H. unfold Absorb. unfold Absorb in H. 
  rewrite Hc in H.  simpl in H.
  unfold Process_instruction. rewrite Hc. repeat split.
  { simpl. apply a_resident_not_matchable. apply sort_correct.
    apply bcompetitive_P. apply bcompetitive_P. unfold Legal_input in H.
    apply not_matchable_perm_invariance with (B':=(sort bcompetitive B))(A':=A) in H0.
    auto. auto. eauto.
  }
  { simpl. intros. destruct H1.  destruct H2.  destruct H3.
    assert(Condition2a (Mlist (Match_ask (sort bcompetitive B) A (ord tau))) 
    (sort bcompetitive B)).
    apply aMlist_ptp_bid. apply perm_nodup with (l:=ids B).
    apply ids_perm. eauto. apply H. 
    apply sort_correct. apply bcompetitive_P. apply bcompetitive_P.
    unfold Condition2a in H5. apply H5 with (b':=b').
    repeat split. eauto. eauto. apply H3. apply H3. auto.
  }
  { simpl. intros. destruct H1. destruct H2. destruct H3. 
    apply ask_id_is_a_id in H4 as H5.
    destruct H3. destruct H1;destruct H2. 
    { subst. apply acompetitive_contadiction in H3. inversion H3. auto. auto. }
    { subst. apply nodup_ids_uniq_order with (B:=(ord tau)::A) in H5. subst.
      apply acompetitive_contadiction in H3. inversion H3. auto. auto. 
      destruct H. destruct H. destruct H7. simpl. apply H7. 
      eauto. auto. }
    { subst a'. apply ids_ask_aux_intro1 in H4 as H7.
      destruct H7 as [t H7]. destruct H7. apply aMlist_tradable in H2 as Hp.
      apply ids_bid_intro1 in H2. unfold fun_ids_bid in H2.
      apply uniq_intro_elim in H2. apply aMlist_bids_ids in H2.
      apply ids_elim in H2. destruct H2 as [b H2]. destruct H2.
      rewrite <- H8 in Hp. rewrite price_elim1 in Hp.
      split. eauto. apply perm_nodup with (l:=ids B).
      apply ids_perm. eauto. apply H. assert(oprice (ord tau) >= oprice a).
      unfold acompetitive in H3. move /orP in H3.
      destruct H3. move /ltP in H3. lia. move /andP in H3.
      destruct H3. move /eqP in H3. lia. destruct H0. unfold matchable.
      unfold tradable. exists b. exists a. repeat split. auto. eauto. lia.
    }
    { destruct H. destruct H. destruct H8. destruct H9.
     assert(~In (id (ord tau)) (ids A)). eauto. 
     apply ids_intro in H2. rewrite H5 in H2. destruct (H11 H2).
    }
  }
  { simpl. unfold Tvalid. intros. unfold valid. apply aMlist_t_valid in H1 as Hv.
    apply ids_bid_intro1 in H1 as Hia.
    unfold fun_ids_bid in Hia. apply uniq_intro_elim in Hia.
    apply aMlist_bids_ids in Hia.
    apply ids_elim in Hia. destruct Hia as [b H2]. destruct H2.
    exists b. exists (ord tau). repeat split. eauto. eauto. auto.
    apply aMlist_ask_ids in H1.
    auto. unfold tradable. apply aMlist_tradable in H1.
    rewrite <- H3 in H1. rewrite price_elim1 in H1.
    split. eauto. apply perm_nodup with (l:=ids B).
    apply ids_perm. eauto. apply H. lia. assert(Ht:=H1).
    apply aMlist_Qty_bid in H1.
    rewrite <- H3 in H1. rewrite quant_elim1 in H1.
    split. eauto. apply perm_nodup with (l:=ids B).
    apply ids_perm. eauto. apply H.
    rewrite H3 in H1. 
    assert( tquantity t <= Qty_bid (Mlist (Match_ask
    (sort bcompetitive B) A (ord tau))) (idb t)).
    apply Qty_bid1. auto. lia. 
    apply perm_nodup with (l:=ids B).
    apply ids_perm. eauto. apply H. apply H. auto.
  }
  { simpl. intros. assert(Qty_bid (Mlist (Match_ask (sort bcompetitive B) 
    A (ord tau))) (id b)=0
    \/Qty_bid (Mlist (Match_ask (sort bcompetitive B) A (ord tau))) (id b)>0). lia.
    destruct H2. lia. apply Qty_bid_elim in H2. destruct H2 as [t H2].
    destruct H2. apply aMlist_Qty_bid in H2. rewrite H3 in H2.
    rewrite quant_elim1 in H2.
    split. eauto. apply perm_nodup with (l:=ids B). apply ids_perm. eauto. 
    apply H. auto. apply perm_nodup with (l:=ids B). 
    apply ids_perm. eauto. apply H. apply H.
  }
  { simpl. intros. destruct H1. subst. assert(Vol (Mlist 
    (Match_ask (sort bcompetitive B) A (ord tau))) >= 
    Qty_ask (Mlist (Match_ask (sort bcompetitive B) A (ord tau))) 
    (id (ord tau))). apply Q_vs_Qty_ask. 
    assert(Vol (Mlist (Match_ask (sort bcompetitive B) A (ord tau))) 
    <= oquantity (ord tau)). 
    apply aMlist_Q. lia. assert(NoDup (id (ord tau) :: ids A)). apply H.
    apply ids_intro in H1. assert(id a <> id (ord tau)). intro. rewrite H3 in H1.
    assert(~In (id (ord tau)) (ids A)). eauto. destruct(H4 H1).
    apply aMlist_Qty_ask_zero with (B:=(sort bcompetitive B))(A:=A) in H3.
    lia.
  }
  { unfold Process_instruction. unfold Absorb. unfold fst.
    rewrite aMlist_hat_B. 
    apply perm_nodup with (l:=ids B). apply ids_perm. eauto. apply H.
    set(M0:=(Mlist (Match_ask (sort acompetitive B) A (ord tau)))).
    apply odiff_perm.  apply perm_nodup with (l:=ids B). apply ids_perm. 
    eauto. apply H.
    all:auto. apply nodup_ids_bids. 
    apply perm_nodup with (l:=ids B). apply ids_perm. eauto. apply H.
    apply bids_perm. destruct tau;auto. destruct H.    
    apply perm_nodup with (l:=ids B). apply ids_perm. eauto. apply H.
    apply H. eauto.
  }
  { unfold Process_instruction. unfold Absorb. unfold snd.
    rewrite aMlist_hat_A. 
    apply perm_nodup with (l:=ids B). apply ids_perm. eauto. apply H.
    apply H. auto.
  }
}
{
  simpl. unfold Absorb. rewrite Hc. unfold Del_order.
  unfold Process_instruction. rewrite Hc.
  repeat split. simpl. apply not_matchable_delete. all:auto.
  simpl. intros. firstorder. simpl. intros. firstorder.  
  unfold Tvalid. simpl. intros. inversion H1. simpl. lia. simpl.
  lia. simpl. rewrite bids_nil. rewrite odiff_nil. auto.
  simpl. rewrite asks_nil. rewrite odiff_nil. auto.
} Qed.




Definition main (I:list instruction)(k:nat):((list order)*(list order)*(list transaction)):= iterated Process_instruction I k.
 
End Programs.


Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant Nat.sub =>  "fun n m -> if m>n then 0 else n-m".
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant Nat.eqb => "( = )".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Inductive prod => "(*)" [ "(,)" ]. 
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "fun n m -> if n>m then None else Some (n<m)".

Extraction Language OCaml.
Require ExtrOcamlBasic.
Extraction "../application/Extracted.ml" cform main.
