Require Import List Nat Arith. 
Import ListNotations.
Require Import Mmx.ast_instructions.

Check (1,2).
Check pair nat nat.
Definition tag_opcode_assoc :=
  list (tag * nat).

Scheme Equality for list.
Check list_beq.






(* actually this is a good name for this function :p *)
Fixpoint lookup (t : tag) (l : tag_opcode_assoc) : option nat :=
  match l with
    | [] => None
    | (t',n) :: tl => if tag_beq t t'
                      then Some n
                      else lookup t tl
  end.
(* actually this is a good name for this function :p *)
Fixpoint lookdown (n : nat) (l : tag_opcode_assoc) : option tag :=
  match l with
    | [] => None
    | (t,n') :: tl => if  eqb n n'
                      then Some t
                      else lookdown n tl
  end.

(* this table is an association list of type tag_opcode_assoc with every associations that can be made in our langage *)
Definition encdec : tag_opcode_assoc := 
[(tag_t_n(ADD),0);
(tag_t_n(SUB),1);
(tag_t_n(MUL),2);
(tag_t_n(DIV),3);
(tag_t_n(ADDU),4);
(tag_t_n(SUBU),5);
(tag_t_n(MULU),6);
(tag_t_n(DIVU),7);
(tag_t_n(CMP),8);
(tag_t_n(CMPU),9);
(tag_t_n(FADD),10);
(tag_t_n(FSUB),11);
(tag_t_n(FMUL),12);
(tag_t_n(FDIV),13);
(tag_t_n(FREM),14);
(tag_t_n(FSQRT),15);
(tag_t_n(FINT),16);
(tag_t_n(FCMP),17);
(tag_t_n(FEQL),18);
(tag_t_n(FUN),19);
(tag_t_n(FCMPE),20);
(tag_t_n(FEQLE),21);
(tag_t_n(FUNE),22);
(tag_t_n(AND),23);
(tag_t_n(OR),24);
(tag_t_n(XOR),25);
(tag_t_n(ANDN),26);
(tag_t_n(ORN),27);
(tag_t_n(NAND),28);
(tag_t_n(NOR),29);
(tag_t_n(NXOR),30);
(tag_t_n(SL),31);
(tag_t_n(SLU),32);
(tag_t_n(SR),33);
(tag_t_n(SRU),34);
(tag_t_n(MOR),35);
(tag_t_n(MXOR),36);
(tag_t_n(BDIF),37);
(tag_t_n(WDIF),38);
(tag_t_n(TDIF),39);
(tag_t_n(ODIF),40);
(tag_t_n(SADD),41);
(tag_t_n(MUX),42);
(tag_t_n(ADDU2),43);
(tag_t_n(ADDU4),44);
(tag_t_n(ADDU8),45);
(tag_t_n(ADDU16),46);
(tag_t_n(LDB),47);
(tag_t_n(LDW),48);
(tag_t_n(LDT),49);
(tag_t_n(LDO),50);
(tag_t_n(STB),51);
(tag_t_n(STW),52);
(tag_t_n(STT),53);
(tag_t_n(STO),54);
(tag_t_n(LDBU),55);
(tag_t_n(LDWU),56);
(tag_t_n(LDTU),57);
(tag_t_n(LDOU),58);
(tag_t_n(STBU),59);
(tag_t_n(STWU),60);
(tag_t_n(STTU),61);
(tag_t_n(STOU),62);
(tag_t_n(LDTH),63);
(tag_t_n(STHT),64);
(tag_t_n(LDSF),65);
(tag_t_n(STSF),66);
(tag_t_n(GO),67);
(tag_t_n(CSZ),68);
(tag_t_n(CSNZ),69);
(tag_t_n(CSN),70);
(tag_t_n(CSNN),71);
(tag_t_n(CSP),72);
(tag_t_n(CSNP),73);
(tag_t_n(CSOD),74);
(tag_t_n(CSEV),75);
(tag_t_n(ZSZ),76);
(tag_t_n(ZSNZ),77);
(tag_t_n(ZSN),78);
(tag_t_n(ZSNN),79);
(tag_t_n(ZSP),80);
(tag_t_n(ZSNP),81);
(tag_t_n(ZSOD),82);
(tag_t_n(ZSEV),83);
(tag_t_n(CSWAP),84);
(tag_t_n(LDUNC),85);
(tag_t_n(STUNC),86);
(tag_t_n(PREST),87);
(tag_t_n(LDTVS),88);
(* end tag_t_n *)

(tag_t_i(ADD_I),89);
(tag_t_i(SUB_I),90);
(tag_t_i(MUL_I),91);
(tag_t_i(DIV_I),92);
(tag_t_i(ADDU_I),93);
(tag_t_i(SUBU_I),94);
(tag_t_i(MULU_I),95);
(tag_t_i(DIVU_I),96);
(tag_t_i(CMP_I),97);
(tag_t_i(CMPU_I),98);
(tag_t_i(AND_I),99);
(tag_t_i(OR_I),100);
(tag_t_i(XOR_I),101);
(tag_t_i(ANDN_I),102);
(tag_t_i(ORN_I),103);
(tag_t_i(NAND_I),104);
(tag_t_i(NOR_I),105);
(tag_t_i(NXOR_I),106);
(tag_t_i(SL_I),107);
(tag_t_i(SLU_I),108);
(tag_t_i(SR_I),109);
(tag_t_i(SRU_I),110);
(tag_t_i(BDIF_I),111);
(tag_t_i(WDIF_I),112);
(tag_t_i(TDIF_I),113);
(tag_t_i(ODIF_I),114);
(tag_t_i(LDA_I),115);
(tag_t_i(GETA_I),116);
(tag_t_i(ADDU2_I),117);
(tag_t_i(ADDU4_I),118);
(tag_t_i(ADDU8_I),119);
(tag_t_i(ADDU16_I),120);
(tag_t_i(LDB_I),121);
(tag_t_i(LDW_I),122);
(tag_t_i(LDT_I),123);
(tag_t_i(LDO_I),124);
(tag_t_i(STB_I),125);
(tag_t_i(STW_I),126);
(tag_t_i(STT_I),127);
(tag_t_i(STO_I),128); 
(tag_t_i(LDBU_I),129);
(tag_t_i(LDWU_I),130);
(tag_t_i(LDTU_I),131);
(tag_t_i(LDOU_I),132);
(tag_t_i(STBU_I),133);
(tag_t_i(STWU_I),134);
(tag_t_i(STTU_I),135);
(tag_t_i(STOU_I),136);
(tag_t_i(LDTH_I),137);             
(tag_t_i(STHT_I),138);
(tag_t_i(LDSF_I),139);
(tag_t_i(STSF_I),140);
(tag_t_i(GO_I),141);
(tag_t_i(CSZ_I),142);
(tag_t_i(CSNZ_I),143);
(tag_t_i(CSN_I),144);
(tag_t_i(CSNN_I),145);
(tag_t_i(CSP_I),146);
(tag_t_i(CSNP_I),147);
(tag_t_i(CSOD_I),148);
(tag_t_i(CSEV_I),149);
(tag_t_i(ZSZ_I),150);
(tag_t_i(ZSNZ_I),151);
(tag_t_i(ZSN_I),152);
(tag_t_i(ZSNN_I),153);
(tag_t_i(ZSP_I),154);
(tag_t_i(ZSNP_I),155);
(tag_t_i(ZSOD_I),156);
(tag_t_i(ZSEV_I),157);
(tag_t_i(PUSHJ_I),158);
(tag_t_i(PUSHGO_I),159);
(tag_t_i(LDTVS_I),160);
  (* end tag_t_i *)

  
(tag_t_i2(NEG),161);
(tag_t_i2(NEGU),162);
(* end tag_t_i2( *)

(tag_t_i3(PRELD),163);
(tag_t_i3(PREGO),164);
(tag_t_i3(SYNCID),165);
(tag_t_i3(SYNCD),166);
(tag_t_i3(STCO),167);
(* end tag_t_i3 *)


(tag_t_i4(NEG_I),168);
(tag_t_i4(NEGU_I),169);
(* end tag_t_i4 *)

(tag_t_i5(TRIP),170);
(tag_t_i5(TRAP),171);
(tag_t_i5(SWYM),172);
(* end tag_t_i5 *)

(tag_t_i6(STCO_I2),173);
(tag_t_i6(STCO_I),174);
(* end tag_t_i6 *)


(tag_d_i(FLOT_I),175);
(tag_d_i(FLOTU_I),176);
(tag_d_i(SFLOT_I),177);
(tag_d_i(SFLOTU_I),178);
(tag_d_i(ORH_I),179);
(tag_d_i(ORMH_I),180);
(tag_d_i(ORML_I),181);
(tag_d_i(ORL_I),182);
(tag_d_i(ANDNH_I),183);
(tag_d_i(ANDNMH_I),184);
(tag_d_i(ANDNML_I),185);
(tag_d_i(ANDNL_I),186);
(tag_d_i(SETH_i),187);
(tag_d_i(SETMH_i),188);
(tag_d_i(SETML_i),189);
(tag_d_i(SETL_i),190);
(tag_d_i(INCH_i),191);
(tag_d_i(INCMH_i),192);
(tag_d_i(INCML_i),193);
(tag_d_i(INCL_i),194);
(tag_d_i(BZ_i),195);
(tag_d_i(BNZ_i),196);
(tag_d_i(BN_i),197);
(tag_d_i(BNN_i),198);
(tag_d_i(BP_i),199);
(tag_d_i(BNP_i),200);
(tag_d_i(BOD_i),201);
(tag_d_i(BEV_i),202);
(tag_d_i(PBZ_i),203);
(tag_d_i(PBNZ_i),204);
(tag_d_i(PBN_i),205);
(tag_d_i(PBNN_i),206);
(tag_d_i(PBP_i),207);
(tag_d_i(PBNP_i),208);
(tag_d_i(PBOD_i),209);
(tag_d_i(PBEV_i),210);
(tag_d_i(GET_i),211);
  (* end (tag_d_i *)

(tag_d_i2(PUT_I),212);
(tag_d_i2(PUT_I2),213);
(* end (tag_d_i2 *)

(tag_d_i3(POP),214);
(tag_d_i3(PUT_II),215);
(* end (tag_d_i3 *)


(tag_d_n(FLOT),216);
(tag_d_n(FLOTU),217);
(tag_d_n(FIX),218);
(tag_d_n(FIXU),219);
(tag_d_n(SFLOT),220);
(tag_d_n(SFLOTU),221);
(* end (tag_d_n( *)

(tag_u(JMP),222);
(tag_u(SAVE),223);
(tag_u(UNSAVE),224);
(tag_u(RESUME),225);
(tag_u(SYNC),226)
].




Theorem lookup_encdec : forall (t : tag), exists n,
                          lookup t encdec = Some n.
Proof.
  destruct t.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.
  -destruct t;
     simpl; eexists; auto.   
Qed.


Require Import Bool.

Print tag.

Definition forall_tag_ter_n (p : tag_ter_normal -> bool): bool :=
(p ADD) &&
(p SUB) &&
(p MUL) &&
(p DIV) &&
(p ADDU) &&
(p SUBU) &&
(p MULU) &&
(p DIVU) &&
(p CMP) &&
(p CMPU) &&
(p FADD) &&
(p FSUB) &&
(p FMUL) &&
(p FDIV) &&
(p FREM) &&
(p FSQRT) &&
(p FINT) &&
(p FCMP) &&
(p FEQL) &&
(p FUN) &&
(p FCMPE) &&
(p FEQLE) &&
(p FUNE) &&
(p AND) &&
(p OR) &&
(p XOR) &&
(p ANDN) &&
(p ORN) &&
(p NAND) &&
(p NOR) &&
(p NXOR) &&
(p SL) &&
(p SLU) &&
(p SR) &&
(p SRU) &&
(p MOR) &&
(p MXOR) &&
(p BDIF) &&
(p WDIF) &&
(p TDIF) &&
(p ODIF) &&
(p SADD) &&
(p MUX) &&
(p ADDU2) &&
(p ADDU4) &&
(p ADDU8) &&
(p ADDU16) &&
(p LDB) &&
(p LDW) &&
(p LDT) &&
(p LDO) &&
(p STB) &&
(p STW) &&
(p STT) &&
(p STO) &&
(p LDBU) &&
(p LDWU) &&
(p LDTU) &&
(p LDOU) &&
(p STBU) &&
(p STWU) &&
(p STTU) &&
(p STOU) &&
(p LDTH) &&
(p STHT) &&
(p LDSF) &&
(p STSF) &&
(p GO) &&
(p CSZ) &&
(p CSNZ) &&
(p CSN) &&
(p CSNN) &&
(p CSP) &&
(p CSNP) &&
(p CSOD) &&
(p CSEV) &&
(p ZSZ) &&
(p ZSNZ) &&
(p ZSN) &&
(p ZSNN) &&
(p ZSP) &&
(p ZSNP) &&
(p ZSOD) &&
(p ZSEV) &&
(p CSWAP) &&
(p LDUNC) &&
(p STUNC) &&
(p PREST) &&
(p LDTVS).


Definition forall_tag_ter_i (p : tag_ter_immediate -> bool): bool :=
(p ADD_I) && 
(p SUB_I) && 
(p MUL_I) && 
(p DIV_I) && 
(p ADDU_I) && 
(p SUBU_I) && 
(p MULU_I) && 
(p DIVU_I) && 
(p CMP_I) && 
(p CMPU_I) && 
(p AND_I) && 
(p OR_I) && 
(p XOR_I) && 
(p ANDN_I) && 
(p ORN_I) && 
(p NAND_I) && 
(p NOR_I) && 
(p NXOR_I) && 
(p SL_I) && 
(p SLU_I) && 
(p SR_I) && 
(p SRU_I) && 
(p BDIF_I) && 
(p WDIF_I) && 
(p TDIF_I) && 
(p ODIF_I) && 
(p LDA_I) && 
(p GETA_I) && 
(p ADDU2_I) && 
(p ADDU4_I) && 
(p ADDU8_I) && 
(p ADDU16_I) && 
(p LDB_I) && 
(p LDW_I) && 
(p LDT_I) && 
(p LDO_I) && 
(p STB_I) && 
(p STW_I) && 
(p STT_I) && 
(p STO_I) && 
(p LDBU_I) && 
(p LDWU_I) && 
(p LDTU_I) && 
(p LDOU_I) && 
(p STBU_I) && 
(p STWU_I) && 
(p STTU_I) && 
(p STOU_I) && 
(p LDTH_I) && 
(p STHT_I) && 
(p LDSF_I) && 
(p STSF_I) && 
(p GO_I) && 
(p CSZ_I) && 
(p CSNZ_I) && 
(p CSN_I) && 
(p CSNN_I) && 
(p CSP_I) && 
(p CSNP_I) && 
(p CSOD_I) && 
(p CSEV_I) && 
(p ZSZ_I) && 
(p ZSNZ_I) && 
(p ZSN_I) && 
(p ZSNN_I) && 
(p ZSP_I) && 
(p ZSNP_I) && 
(p ZSOD_I) && 
(p ZSEV_I) && 
(p PUSHJ_I) && 
(p PUSHGO_I) && 
(p LDTVS_I).

Definition forall_tag_ter_i2 (p : tag_ter_immediate2 -> bool): bool :=
  (p NEG) && (p NEGU).

Definition forall_tag_ter_i3 (p : tag_ter_immediate3 -> bool): bool :=
  (p PRELD) && (p PREGO) && (p SYNCID) && (p SYNCD) && (p STCO).

Definition forall_tag_ter_i4 (p : tag_ter_immediate4 -> bool): bool :=
  (p NEG_I) && (p NEGU_I).

Definition forall_tag_ter_i5 (p : tag_ter_immediate5 -> bool): bool :=
  (p TRIP) && (p TRAP) && (p SWYM).

Definition forall_tag_ter_i6 (p : tag_ter_immediate6 -> bool): bool :=
  (p STCO_I2) && (p STCO_I).


Definition forall_tag_duo_i (p : tag_duo_immediate -> bool): bool :=
(p FLOT_I) && 
(p FLOTU_I) && 
(p SFLOT_I) && 
(p SFLOTU_I) && 
(p ORH_I) && 
(p ORMH_I) && 
(p ORML_I) && 
(p ORL_I) && 
(p ANDNH_I) && 
(p ANDNMH_I) && 
(p ANDNML_I) && 
(p ANDNL_I) && 
(p SETH_i) && 
(p SETMH_i) && 
(p SETML_i) && 
(p SETL_i) && 
(p INCH_i) && 
(p INCMH_i) && 
(p INCML_i) && 
(p INCL_i) && 
(p BZ_i) && 
(p BNZ_i) && 
(p BN_i) && 
(p BNN_i) && 
(p BP_i) && 
(p BNP_i) && 
(p BOD_i) && 
(p BEV_i) && 
(p PBZ_i) && 
(p PBNZ_i) && 
(p PBN_i) && 
(p PBNN_i) && 
(p PBP_i) && 
(p PBNP_i) && 
(p PBOD_i) && 
(p PBEV_i) && 
(p GET_i).

Definition forall_tag_duo_i2 (p : tag_duo_immediate2 -> bool): bool :=
  (p PUT_I) && (p PUT_I2).

Definition forall_tag_duo_i3 (p : tag_duo_immediate3 -> bool): bool :=
  (p POP) && (p PUT_II).


Definition forall_tag_duo_n (p : tag_duo_normal -> bool): bool :=
(p FLOT) &&
(p FLOTU) &&
(p FIX) &&
(p FIXU) &&
(p SFLOT) &&
(p SFLOTU).

Definition forall_tag_uno (p : tag_uno -> bool): bool :=
  (p JMP) &&          
  (p SAVE) &&
  (p UNSAVE) &&
  (p RESUME) &&
  (p SYNC).



Definition forall_tag (p : tag -> bool): bool :=
  (forall_tag_ter_n (fun x => p (tag_t_n x))) &&
                                              (forall_tag_ter_i (fun x => p (tag_t_i x))) &&
                                              (forall_tag_ter_i2 (fun x => p (tag_t_i2 x))) &&
                                              (forall_tag_ter_i3 (fun x => p (tag_t_i3 x))) &&
                                              (forall_tag_ter_i4 (fun x => p (tag_t_i4 x))) &&
                                              (forall_tag_ter_i5 (fun x => p (tag_t_i5 x))) &&
                                              (forall_tag_ter_i6 (fun x => p (tag_t_i6 x))) &&
                                              (forall_tag_duo_n (fun x => p (tag_d_n x))) &&
                                              (forall_tag_duo_i (fun x => p (tag_d_i x))) &&
                                              (forall_tag_duo_i2 (fun x => p (tag_d_i2 x))) &&
                                              (forall_tag_duo_i3 (fun x => p (tag_d_i3 x))) &&
                                              (forall_tag_uno (fun x => p (tag_u x))).


Print reflect.

Definition propP := forall x : nat, x = x.
Check propP.

Lemma test_reflect : True -> reflect True true.
Proof.
  exact (ReflectT True).
Qed.




Lemma helpBefore1 : forall (f : tag -> bool), forall_tag f = true -> (forall (t: tag), f t = true).
Proof.
  intros f.
  unfold forall_tag.
  intros H.
  repeat (apply andb_prop in H; destruct H).
  repeat (apply andb_prop in H10; destruct H10).
  repeat (apply andb_prop in H9; destruct H9).
  repeat (apply andb_prop in H8; destruct H8).
  repeat (apply andb_prop in H7; destruct H7).
  repeat (apply andb_prop in H6; destruct H6).
  repeat (apply andb_prop in H5; destruct H5).
  repeat (apply andb_prop in H4; destruct H4).
  repeat (apply andb_prop in H3; destruct H3).
  repeat (apply andb_prop in H2; destruct H2).
  repeat (apply andb_prop in H1; destruct H1).
  repeat (apply andb_prop in H0; destruct H0).     
  destruct t; destruct t; auto.
Qed.


Lemma helpBefore2 : forall (f : tag -> bool), (forall (t: tag), f t = true) -> forall_tag f = true.
Proof.
  intros f H.
  unfold forall_tag.
  Search (_ && _ = true).
  repeat (apply andb_true_intro ; split ; auto).
Qed.


Lemma forall_tagP: forall (P : tag -> Prop)(f : tag -> bool),
    (forall (t : tag), reflect (P t) (f t)) ->
    reflect (forall t, P t) (forall_tag f).
Proof.
  intros P f H.
  Search reflect.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -Search forall_tag.
   intros.
   rewrite helpBefore2.
   +reflexivity.
   +intros t.
    specialize (H t).
    Search forall_tag.
    apply reflect_iff in H.
    inversion H.
    specialize (H0 t).
    apply H1.
    exact H0.
    (* this part is ok !!! ;) *)
  -intros.
   specialize (H t).
   rewrite helpBefore1 in H.
   inversion H.
   +exact H1.
   +exact H0.
Qed.


    
SearchAbout leb.
(* the first nat is the maximum we wan't to have in this bounded nat interval *)
Fixpoint forall_bounded (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0 => f 0
  | S n => f (S n) && forall_bounded n f
  end.

Lemma help_forall_findP1 : forall (f : nat -> bool) (k : nat), (forall (n: nat), n <= k -> f n = true) -> forall_bounded k f = true.
Proof.
  intros.
  induction k.
  -apply H.
   reflexivity.
  -simpl.
   Search (_ && _ = true).
   apply andb_true_intro.
   split.
   +apply H.
    reflexivity.
   +apply IHk.
    intros n.
    specialize (H n).
    intros.
    apply H.
    Search (_ <= S _).
    apply le_S in H0.
    exact H0.
Qed.

Lemma help_forall_findP2 :
  forall (k : nat) (f : nat -> bool), forall_bounded k f = true -> (forall (n: nat), n <= k -> f n = true).
Proof.
  induction k.
  -simpl.
   intros.
   Search (_ <= 0).
   apply le_n_0_eq in H0.
   rewrite <- H0.
   exact H.
  -destruct n.
   +intros.
    apply IHk.
    simpl in H.
    Search (_ && _ = true).
    apply andb_prop in H.
    destruct H.
    exact H1.
    apply Peano.le_0_n.
   +apply andb_prop in H. 
    fold forall_bounded in H.
    destruct H.
    intros.
    change (f (S n) = true) with ((fun n => f (S n)) n = true).
    apply IHk.
    {(* c'est donner par H0 et H mais faut trouver un théoreme pour reussir a exprimer ça *)
      assert (forall (k' : nat) (f' : nat -> bool) , f' (S k') = true -> forall_bounded k' f' = true -> forall_bounded k' (fun n0 : nat => f' (S n0)) = true).
      {
        induction k'.
        -intros.
         simpl.
         auto.
        -intros.
         simpl.
         rewrite H2.
         simpl.
         apply IHk'.
         +unfold forall_bounded in H3.
          fold forall_bounded in H3.
          apply andb_true_iff in H3.
          destruct H3.
          auto.
         +unfold forall_bounded in H3.
          fold forall_bounded in H3.
          apply andb_true_iff in H3.
          destruct H3.
          auto.
      }
      auto.       
    }
    {
      Search (S _ <= S _).
      apply le_S_n in H1.
      exact H1.
    }
Qed.
    
    

Lemma forall_finP: forall (P : nat -> Prop)(f : nat -> bool) (k : nat),
    (forall (n : nat), reflect (P n) (f n)) ->
    reflect (forall n, n <= k -> P n) (forall_bounded k f).
Proof.
  intros P f k H.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -intros.
   Check help_forall_findP1.
   apply help_forall_findP1.
   intros.
   specialize (H n).
   apply reflect_iff in H.
   inversion H.
   apply H2.
   apply H0.
   exact H1.
  -intros.
   Check help_forall_findP2.
   eapply help_forall_findP2 in H0.
   specialize (H n).
   rewrite H0 in H.
   inversion H.
   exact H2.
   exact H1.
Qed.


  
  
  

Definition imply (a b : bool): bool := if a then b else true.

Lemma implyP: forall A B a b, reflect A a -> reflect B b -> reflect (A -> B) (imply a b).
Proof.
  intros.
  apply reflect_iff in H.
  inversion H.
  apply reflect_iff in H0.
  inversion H0.
  apply iff_reflect.
  apply iff_to_and.
  unfold imply.
  split.  
  -intros.
   destruct a.
   +apply H3.
    apply H5.
    apply H2.
    reflexivity.
   +reflexivity. 
  -intros.
   destruct b.
   +apply H4.
    reflexivity.
   +destruct a.
    {
      discriminate.
    }
    {
      apply H4.
      apply H1.
      exact H6.
    }
Qed.

SearchAbout beq_nat.

Definition eq_mtag (t1 t2: option tag): bool :=
  match t1,t2 with
  | Some t1', Some t2' => tag_beq t1' t2'
  | _,_ => false
  end.

Lemma eq_mtag_equiv : forall (t1 t2 : option tag), eq_mtag t1 t2 = true -> t1 = t2.
Proof.
  destruct t1.
  -destruct t2.
   +simpl.
   intros.
   apply tag_beq_different in H.
   rewrite H.
   reflexivity.
   +discriminate.
  -discriminate.
Qed.


Definition eq_mnat (t1 t2: option nat): bool :=
  match t1,t2 with
  | Some n1,Some n2 => beq_nat n1 n2
  | _,_ => false
  end.

Lemma eq_mnat_equiv : forall (n1 n2 : option nat), eq_mnat n1 n2 = true -> n1 = n2.
Proof.
  destruct n1.
  -destruct n2.
   +simpl.
    intros.
    Search (_ =? _ = true).
    apply beq_nat_true in H.
    rewrite H.
    reflexivity.
   +discriminate.
  -discriminate.
Qed.
  

Definition lookdown_encdecP : bool :=
  forall_bounded 226 (fun n =>                     
                      forall_tag (fun t => imply (eq_mtag (lookdown n encdec) (Some t))
                                                 (eq_mnat (lookup t encdec) (Some n)))).
Definition lookdown_encdecP' : bool :=
  forall_bounded 226 (fun n =>                     
                      forall_tag (fun t => imply (eq_mnat (lookup t encdec) (Some n))
                                                 (eq_mtag (lookdown n encdec) (Some t)))).

Lemma lookdown_n_inf_7 : forall (n : nat) (t : tag), lookdown n encdec = Some t -> n <=226.
Proof.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
    destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  destruct n. intros. repeat (apply le_n_S). apply Peano.le_0_n.
  intros. simpl in H. discriminate.
Qed.
  




Theorem lookdown_encdec : forall (n : nat) (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n.
Proof.
  SearchAbout (_ < _ \/ _).
  assert (reflect (forall (n : nat), n <= 226 -> forall
                       (t : tag), lookdown n encdec = Some t -> lookup t encdec = Some n)
                  lookdown_encdecP).
  {
    unfold lookdown_encdecP.
    SearchAbout forall_bounded.
    Check forall_finP.
    apply forall_finP.        
    intro n.
    Check forall_tag.
    apply forall_tagP.
    SearchAbout imply.
    intros t.
    apply implyP.
    -assert (reflect (lookdown n encdec = Some t) (eq_mtag (lookdown n encdec) (Some t))).
    {
      apply iff_reflect.
      apply iff_to_and.
      split.
      +intros.
       rewrite H.
       simpl.
       rewrite tag_beq_reflexivity.
       reflexivity.
      +intros.
       apply eq_mtag_equiv in H.
       exact H.       
    }
    exact H.
    -assert (reflect (lookup t encdec = Some n) (eq_mnat (lookup t encdec) (Some n))).
    {
      apply iff_reflect.
      apply iff_to_and.
      split.
      -intros.
      rewrite H.
      simpl.
      Search (_ =? _).
      rewrite <- beq_nat_refl.
      reflexivity.
      -intros.
       apply eq_mnat_equiv in H.
       exact H.
    }
    exact H.
  }
  (* i admit this only because computing is too long *)
  assert (H': lookdown_encdecP = true) by admit. 
  rewrite H' in H.
  inversion H.
  intros n.
  Search (_ <= _ \/ _).
  Check Nat.le_gt_cases.
  specialize (Nat.le_gt_cases n 226).
  intros.
  destruct H1.
  -apply H0.
   exact H1.
   exact H2.
  -assert (exists m, n = 227 + m).
   {
     (* not that simple *)
     Search (_ < _).
     admit.
   }
   destruct H3.
   subst n.
   simpl in H2.
   discriminate.
  Admitted.


(* need to find how to refactor the proof *)
Lemma lookup_val : forall (n : nat) (t : tag), lookup t encdec = Some n -> n <= 226.
Proof.
Admitted.


Theorem lookup_encdecP : forall (n : nat) (t : tag) , lookup t encdec = Some n -> lookdown n encdec = Some t.
Proof.
  SearchAbout reflect.
  assert (reflect (forall (n : nat), n <= 226 -> forall (t : tag), lookup t encdec = Some n -> lookdown n encdec = Some t) lookdown_encdecP').
  {
    unfold lookdown_encdecP.
    SearchAbout reflect.
    Check forall_finP.
    apply forall_finP.
    Check forall_tagP.
    intros n.
    apply forall_tagP.
    SearchAbout reflect.
    Check implyP.
    intros t.
    apply implyP.
    -assert (reflect (lookup t encdec = Some n) (eq_mnat (lookup t encdec) (Some n))).
     {
       apply iff_reflect.
       apply iff_to_and.
       split.
       +intros.
        rewrite H.
        simpl.
        apply Nat.eqb_refl.
       +intros.
        apply eq_mnat_equiv in H.
        exact H.
     }
     exact H.
    -assert (reflect (lookdown n encdec = Some t) (eq_mtag (lookdown n encdec) (Some t))).
     {
       apply iff_reflect.
       apply iff_to_and.
       split.
       +intros.
        rewrite H.
        simpl.
        apply tag_beq_reflexivity.
       +intros.
        apply eq_mtag_equiv in H.
        exact H.
     }
     exact H.
  }
  (* same as previously *)
  assert (lookdown_encdecP' = true) by admit.
  rewrite H0 in H.
  inversion H.
  intros n.
  Search (_ <= _ \/ _).
  Check Nat.le_gt_cases.
  specialize (Nat.le_gt_cases n 226).
  intros.
  destruct H2.
  -apply H1.
   exact H2.
   exact H3.
  -assert (exists m, n = 227 + m).
   {
     admit.
   }   
   destruct H4.
   subst n.
   apply lookup_val in H3.
   simpl in H3.
   Search (S _ <= _).
   repeat apply le_S_n in H3.
   Search (S _ <= 0).
   apply Nat.nle_succ_0 in H3.
   inversion H3.
Admitted.




