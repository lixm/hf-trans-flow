
(* Utilities for the upate of functions and mappings *)

Require Import SfLib.
Require Import Logic.FunctionalExtensionality.

Definition func_upd
           `(key_tp : Type) `(val_tp : Type) 
           (dec : forall (k1 k2 : key_tp), {k1 = k2} + {k1 <> k2}) 
           (mp : key_tp -> val_tp)
           (k : key_tp) (v : val_tp) : key_tp -> val_tp :=
  (fun k' => if dec k' k then v else mp k'). 

Lemma func_upd_eq :
  forall k_tp v_tp dec mp k v,
    (func_upd k_tp v_tp dec mp k v) k = v.
Proof.
  unfold func_upd; simpl.
  intros; destruct (dec k k); [auto | apply ex_falso_quodlibet; apply n; auto].
Qed.

Lemma func_upd_neq :
  forall k_tp v_tp dec mp k v k',
    k <> k' -> (func_upd k_tp v_tp dec mp k v) k' = mp k'. 
Proof.
  unfold func_upd; simpl.
  intros; destruct (dec k k).
  destruct (dec k' k). congruence. auto. apply ex_falso_quodlibet; apply n; auto.
Qed.

Definition mp_tp (key_tp : Type) (val_tp : Type) := key_tp -> option val_tp.

Definition mp_upd
           `(key_tp : Type) `(val_tp : Type) 
           (dec : forall (k1 k2 : key_tp), {k1 = k2} + {k1 <> k2}) 
           (mp : mp_tp key_tp val_tp)
           (k : key_tp) (v : val_tp) : mp_tp key_tp val_tp :=
  func_upd key_tp (option val_tp) dec mp k (Some v). 

Lemma mp_upd_eq :
  forall k_tp v_tp dec mp k v, (mp_upd k_tp v_tp dec mp k v) k = Some v.
Proof. unfold mp_upd. intros. apply func_upd_eq. Qed. 

Lemma mp_upd_neq :
  forall k_tp v_tp dec mp k v k',
    k <> k' -> (mp_upd k_tp v_tp dec mp k v) k' = mp k'.
Proof. unfold mp_upd. intros. apply func_upd_neq. auto. Qed.

Lemma func_upd_func_upd_eq :
  forall k_tp v_tp dec mp k v v',
    func_upd k_tp v_tp dec (func_upd k_tp v_tp dec mp k v) k v' =
    func_upd k_tp v_tp dec mp k v'.
Proof.
  intros.
  unfold func_upd.
  apply functional_extensionality.
  intro k'.
  destruct (dec k' k); auto.
Qed. 

Lemma func_upd_mp_upd_eq :
  forall k_tp v_tp dec mp k v v',
    func_upd k_tp (option v_tp) dec (mp_upd k_tp v_tp dec mp k v) k v'
    = func_upd k_tp (option v_tp) dec mp k v'. 
Proof. unfold mp_upd. intros. apply func_upd_func_upd_eq. Qed. 

Lemma mp_upd_func_upd_eq : 
  forall k_tp v_tp dec mp k v v',
    mp_upd k_tp v_tp dec (func_upd k_tp (option v_tp) dec mp k v') k v
    = mp_upd k_tp v_tp dec mp k v.
Proof. unfold mp_upd. intros. apply func_upd_func_upd_eq. Qed. 

Lemma mp_upd_mp_upd_eq :
  forall k_tp v_tp dec mp k v v',
    mp_upd k_tp v_tp dec (mp_upd k_tp v_tp dec mp k v) k v'
    = mp_upd k_tp v_tp dec mp k v'.
Proof. unfold mp_upd. intros. apply func_upd_func_upd_eq. Qed. 
  
Lemma func_upd_switch :
  forall k_tp v_tp dec mp k1 k2 v1 v2, 
         k1 <> k2 ->
         func_upd k_tp v_tp dec (func_upd k_tp v_tp dec mp k1 v1) k2 v2
         = func_upd k_tp v_tp dec (func_upd k_tp v_tp dec mp k2 v2) k1 v1.
Proof.
  intros. unfold func_upd.
  apply functional_extensionality. intro k.
  destruct (dec k k1); destruct (dec k k2); congruence. 
Qed.   
    
Hint Resolve
     mp_upd_eq mp_upd_neq func_upd_eq func_upd_neq func_upd_mp_upd_eq mp_upd_func_upd_eq
     mp_upd_mp_upd_eq 
  : mp_tp_tacs.

Hint Rewrite
     mp_upd_eq mp_upd_neq func_upd_eq func_upd_neq func_upd_mp_upd_eq mp_upd_func_upd_eq
     mp_upd_mp_upd_eq
  : mp_tp_rewrites. 
