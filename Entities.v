
(* Formalization of the entities involved in the transaction flow *)

Require Import Bool.
Require Import List.
Require Import MyUtils. 

Inductive key : Type :=
  Key : nat -> key.

Inductive val : Type :=
  PrimVal : nat -> val
| CompVal : (mp_tp key val) -> val. 

Inductive ver : Type :=
  Ver : nat -> ver.

Definition world_state := mp_tp key (prod val ver).

Inductive operation : Type :=
  Oper : nat -> operation. 

Inductive client_id : Type :=
  ClId : nat -> client_id.

Inductive peer_id : Type :=
  PrId : nat -> peer_id.

Inductive orderer_id : Type :=
  OdId : nat -> orderer_id. 

Inductive chaincode_id : Type :=
  CcId : nat -> chaincode_id.

Inductive time_stamp : Type :=
  TS : nat -> time_stamp.

Inductive hash : Set := Hash : nat -> hash. 

Inductive private_key : Type := PriK : nat -> private_key. 
Inductive public_key : Type := PubK : nat -> public_key.

Inductive sig : Type := Sig : public_key -> hash -> sig.

Theorem beq_nat_dec : forall (n1 n2 : nat), {n1 = n2} + {n1 <> n2}.
Proof. intros; repeat decide equality. Qed.   

Theorem beq_cli_id_dec : forall (id1 id2 : client_id), {id1 = id2} + {id1 <> id2}.
Proof. intros; repeat decide equality. Qed. 

Theorem beq_peer_id_dec : forall (id1 id2 : peer_id), {id1 = id2} + {id1 <> id2}.
Proof. intros; repeat decide equality. Qed.

Theorem beq_hash_dec : forall (hs1 hs2 : hash), {hs1 = hs2} + {hs1 <> hs2}.
Proof. intros; repeat decide equality. Qed.

Theorem beq_key_dec : forall (k1 k2 : key), {k1 = k2} + {k1 <> k2}.
Proof. intros; repeat decide equality. Qed.

Theorem beq_ver_dec : forall (v1 v2 : ver), {v1 = v2} + {v1 <> v2}.
Proof. intros; repeat decide equality. Qed. 

Theorem beq_cc_id_dec : forall (id1 id2 : chaincode_id), {id1 = id2} + {id1 <> id2}.
Proof. intros; repeat decide equality. Qed.

Inductive channel_config : Type := CConf : nat -> channel_config.

Inductive network_config : Type := NConf : nat -> network_config.

(* an endorsement policy takes a list of signatures by the 
   endorsing peers and returns the result of the policy evaluation *) 
Definition endorsement_pol : Type := list sig -> bool.

(* the core of a transaction proposal *)
Inductive tx_field : Type :=
  TxField : client_id -> chaincode_id ->
            operation -> time_stamp -> tx_field. 
    
(* trans proposal from a client to peers *) 
Inductive trans_propose_msg : Type := 
  ProposeMsg : tx_field -> trans_propose_msg. 

(* either a value or a delete marker *)
Inductive val_or_del : Type :=
  Val_or_del1 : val -> val_or_del
| Val_or_del2 : val_or_del. 

Definition read_set : Type := mp_tp key ver.
Definition write_set : Type := mp_tp key val_or_del. 

(* the hash is used to identify the transaction proposal, 
   it is the hash value of tx_field in the proposal *) 
Inductive tx_proposal_field : Type :=
  TxProposal : peer_id -> hash -> 
               chaincode_id -> operation ->
               read_set -> write_set -> 
               tx_proposal_field. 

(* sig is the peer's signature on tx_proposal_field *) 
Inductive trans_endorsed_msg : Type :=
  Trans_endorsed_msg : tx_proposal_field -> sig -> trans_endorsed_msg.
  
(* hash is on tx_field in trans_propose_msg *) 
Inductive trans_invalid_msg : Type :=
  Trans_invalid_msg : hash -> trans_invalid_msg.  

Definition hash_func := forall (data_tp: Type), data_tp -> hash. 
  
(* transactions in a block; 
   "operation" encompasses the operation invoked together 
   with the input parameters used *)  
Inductive transaction : Type :=
  Trans : chaincode_id -> operation ->
          (prod read_set write_set) -> list trans_endorsed_msg -> transaction.

Definition tx_ccid trans : chaincode_id :=
  match trans with Trans cc_id _ _ _ => cc_id end. 

(* args: block number, hash of transactions, hash for previous block *) 
Inductive block_header : Type :=
  Blk_header : nat -> hash -> hash -> block_header. 

Inductive block : Type :=
  Blk : block_header -> list transaction -> list bool -> block.  

Definition blk_hdr blk : block_header :=
  match blk with Blk hdr _ _ => hdr end.
  
Definition blk_hash blk : hash :=
  match blk_hdr blk with (Blk_header _ hs _) => hs end. 

Definition blk_no blk : nat :=
  match blk_hdr blk with (Blk_header no _ _) => no end. 

Definition blk_prev_hash blk : hash :=
  match blk_hdr blk with (Blk_header _ _ phs) => phs end.

Definition blk0 : block :=
  Blk (Blk_header 0 (Hash 0) (Hash 0)) nil nil. 

Inductive blockchain : Type := 
  BC : list block -> blockchain.

Inductive ledger : Type :=
  Ledger : blockchain -> (chaincode_id -> (option world_state)) -> ledger.

Inductive chaincode : Type :=
  Chaincode : list operation -> chaincode.

Record peer_node : Type :=
  mkPeer_node
    {
      (* public key of the peer *)
      peer_public_key : public_key;
      (* endorsement policy and list of chaincode operations 
         for each chaincode *)
      peer_ep_cc : mp_tp chaincode_id (prod endorsement_pol chaincode);
      (* the ledger containing the blockchain and the local record of 
         the world state *) 
      peer_ledger : ledger;
      (* list of pending transaction proposals to be processed *)
      peer_pmsgs : list trans_propose_msg;
      (* semantic function for the chaincode operations *) 
      peer_interp_oper : operation -> world_state -> (prod read_set write_set) 
    }.

Definition pn0 :=
  {| peer_public_key := PubK 0; 
     peer_ep_cc := fun _ => None;
     peer_ledger := Ledger (BC nil) (fun _ => None);
     peer_pmsgs := nil; 
     peer_interp_oper := (fun _ => fun _ => ((fun _ => None), (fun _ => None)))
  |}.

Definition upd_peer_pmsgs pn pmsgs : peer_node :=
  {| peer_public_key := pn.(peer_public_key);
     peer_ep_cc := pn.(peer_ep_cc);
     peer_ledger := pn.(peer_ledger);
     peer_pmsgs := pmsgs;
     peer_interp_oper := pn.(peer_interp_oper) 
  |}.

Definition upd_peer_ledger pn lgr : peer_node :=
  {| peer_public_key := pn.(peer_public_key);
     peer_ep_cc := pn.(peer_ep_cc);
     peer_ledger := lgr;
     peer_pmsgs := pn.(peer_pmsgs);
     peer_interp_oper := pn.(peer_interp_oper) 
  |}. 

Record client : Type :=
  mkClient
    {
      cli_timestamp : time_stamp;
      (* a list of transaction proposals on which endorsements 
         are being awaited *) 
      cli_pending_proposals : list trans_propose_msg;
      (* a list of currently received endorsements
         for each proposal identified by its hash value *) 
      cli_received_eds : hash -> list trans_endorsed_msg 
    }.

Definition inc_cli_timestamp cli : client :=
  {| cli_timestamp := 
       match cli.(cli_timestamp) with
         TS i => TS (S i)
       end; 
     cli_pending_proposals := cli.(cli_pending_proposals);
     cli_received_eds := cli.(cli_received_eds) |}.

Definition upd_cli_pending_proposals cli (pmsgs : list trans_propose_msg)
  : client :=
  {| cli_timestamp := cli.(cli_timestamp);
     cli_pending_proposals := pmsgs;
     cli_received_eds := cli.(cli_received_eds)
  |}.

Definition upd_cli_received_eds cli (rcv_eds : hash -> list trans_endorsed_msg)
  : client :=
  {| cli_timestamp := cli.(cli_timestamp);
     cli_pending_proposals := cli.(cli_pending_proposals);
     cli_received_eds := rcv_eds 
  |}. 

Record ordering_service : Type :=
  mkOrderer
    { (* number of transactions contained in a block *)
      os_blk_size : nat;
      (* block number of the last block *)
      os_last_blk_num : nat;
      (* hash of the list of transactions in the last block *)
      os_last_blk_hash : hash;
      (* pending transactions to be assembled into blocks *)
      os_pending_trans : list transaction;
      (* mapping of block numbers to the already created blocks *)
      os_blks_created : nat -> option block
    }.

Definition inc_os_blk_num os : ordering_service :=
  {| os_blk_size := os.(os_blk_size);
     os_last_blk_num := S (os.(os_last_blk_num));  
     os_last_blk_hash := os.(os_last_blk_hash);
     os_pending_trans := os.(os_pending_trans);
     os_blks_created := os.(os_blks_created)
  |}.

Definition upd_os_last_blk_hash os hsh : ordering_service :=
  {| os_blk_size := os.(os_blk_size);
     os_last_blk_num := os.(os_last_blk_num);
     os_last_blk_hash := hsh; 
     os_pending_trans := os.(os_pending_trans);
     os_blks_created := os.(os_blks_created)
  |}. 

Definition upd_os_pending_trans os pd_trxs :=
  {| os_blk_size := os.(os_blk_size);
     os_last_blk_num := os.(os_last_blk_num);
     os_last_blk_hash := os.(os_last_blk_hash);
     os_pending_trans := pd_trxs;
     os_blks_created := os.(os_blks_created)
  |}.
  
Definition upd_os_blks_created os blks_crt :=
  {| os_blk_size := os.(os_blk_size);
     os_last_blk_num := os.(os_last_blk_num);
     os_last_blk_hash := os.(os_last_blk_hash); 
     os_pending_trans := os.(os_pending_trans);
     os_blks_created := blks_crt
  |}. 
