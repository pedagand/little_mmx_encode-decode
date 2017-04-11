Require Import List.
 
(* tag definition *)
Inductive tag_ter_normal :=
(* Integer arithmetic *)
| ADD : tag_ter_normal
| SUB : tag_ter_normal
| MUL : tag_ter_normal
| DIV : tag_ter_normal
(* unsigned arithmetic *)
| ADDU : tag_ter_normal
| SUBU : tag_ter_normal
| MULU : tag_ter_normal
| DIVU : tag_ter_normal
(* compare instructions *)
| CMP : tag_ter_normal
| CMPU : tag_ter_normal
(* floating point arithmetic *)
| FADD : tag_ter_normal
| FSUB : tag_ter_normal
| FMUL : tag_ter_normal
| FDIV : tag_ter_normal
| FREM : tag_ter_normal
| FSQRT : tag_ter_normal
| FINT : tag_ter_normal
(* comparing float number *)
| FCMP : tag_ter_normal
| FEQL : tag_ter_normal
| FUN : tag_ter_normal
| FCMPE : tag_ter_normal
| FEQLE : tag_ter_normal
| FUNE : tag_ter_normal
(* Bits and Bytes *)
| AND : tag_ter_normal
| OR : tag_ter_normal
| XOR : tag_ter_normal
| ANDN : tag_ter_normal
| ORN : tag_ter_normal
| NAND : tag_ter_normal
| NOR : tag_ter_normal
| NXOR : tag_ter_normal
(* shifting bit patterns *)
| SL : tag_ter_normal
| SLU : tag_ter_normal
| SR : tag_ter_normal
| SRU : tag_ter_normal
(* mix and match *)
| MOR : tag_ter_normal
| MXOR : tag_ter_normal
(* bytewise operation *)
| BDIF : tag_ter_normal
| WDIF : tag_ter_normal
| TDIF : tag_ter_normal
| ODIF : tag_ter_normal
(* the sadd instruction *)
| SADD : tag_ter_normal
(* the mux instruction *)
| MUX : tag_ter_normal
(* 2ADDU ,  4ADDU , 8ADDU , 16ADDU *)
| ADDU2 : tag_ter_normal
| ADDU4 : tag_ter_normal
| ADDU8 : tag_ter_normal
| ADDU16 : tag_ter_normal
(* load and store *)
| LDB : tag_ter_normal
| LDW : tag_ter_normal
| LDT : tag_ter_normal
| LDO : tag_ter_normal
          (* storing signd integers *)
| STB : tag_ter_normal
| STW : tag_ter_normal
| STT : tag_ter_normal
| STO : tag_ter_normal
           (* loading unsigned data *)
| LDBU : tag_ter_normal
| LDWU : tag_ter_normal
| LDTU : tag_ter_normal
| LDOU : tag_ter_normal
(* storing  unsigned data *)
| STBU : tag_ter_normal
| STWU : tag_ter_normal
| STTU : tag_ter_normal
| STOU : tag_ter_normal
           (* LDTH instruction *)
| LDTH : tag_ter_normal           
(* STHT instruction *)             
| STHT : tag_ter_normal
           (* loading and storing short float *)
| LDSF : tag_ter_normal
| STSF : tag_ter_normal
(* jump with absolute adress *)             
| GO : tag_ter_normal
         (* Conditional assigments *)
| CSZ : tag_ter_normal
| CSNZ : tag_ter_normal
| CSN : tag_ter_normal
| CSNN : tag_ter_normal
| CSP : tag_ter_normal
| CSNP : tag_ter_normal
| CSOD : tag_ter_normal
| CSEV : tag_ter_normal
| ZSZ : tag_ter_normal
| ZSNZ : tag_ter_normal
| ZSN : tag_ter_normal
| ZSNN : tag_ter_normal
| ZSP : tag_ter_normal
| ZSNP : tag_ter_normal
| ZSOD : tag_ter_normal
| ZSEV : tag_ter_normal
           (* CSWAP *)
| CSWAP : tag_ter_normal 
            (* ldunc and stunc *)
| LDUNC : tag_ter_normal
| STUNC : tag_ter_normal
            (* preld prest prego *)
| PREST : tag_ter_normal
            (* LDTVS *)
| LDTVS : tag_ter_normal.
             
(* this is tag for instructions with the form (tag reg reg imm) *)
Inductive tag_ter_immediate :=
(* Integer arithmetic *)
| ADD_I : tag_ter_immediate
| SUB_I : tag_ter_immediate
| MUL_I : tag_ter_immediate
| DIV_I : tag_ter_immediate
(* Unsigned arithmetic *)
| ADDU_I : tag_ter_immediate
| SUBU_I : tag_ter_immediate
| MULU_I : tag_ter_immediate
| DIVU_I : tag_ter_immediate
(* compare instructions *)
| CMP_I : tag_ter_immediate
| CMPU_I : tag_ter_immediate
(* Bits and Bytes *)
| AND_I : tag_ter_immediate
| OR_I : tag_ter_immediate
| XOR_I : tag_ter_immediate
| ANDN_I : tag_ter_immediate
| ORN_I : tag_ter_immediate
| NAND_I : tag_ter_immediate
| NOR_I : tag_ter_immediate
| NXOR_I : tag_ter_immediate
(* shifting bit patterns *)
| SL_I : tag_ter_immediate
| SLU_I : tag_ter_immediate
| SR_I : tag_ter_immediate
| SRU_I : tag_ter_immediate             
(* bytewise operation *)
| BDIF_I : tag_ter_immediate
| WDIF_I : tag_ter_immediate
| TDIF_I : tag_ter_immediate
| ODIF_I : tag_ter_immediate             
             (* adress computation *)
| LDA_I : tag_ter_immediate
          (* get adress *)
| GETA_I : tag_ter_immediate
           (* 2ADDU ,  4ADDU , 8ADDU , 16ADDU *)
| ADDU2_I : tag_ter_immediate
| ADDU4_I : tag_ter_immediate
| ADDU8_I : tag_ter_immediate
| ADDU16_I : tag_ter_immediate
             (* load and store *)
| LDB_I : tag_ter_immediate
| LDW_I : tag_ter_immediate
| LDT_I : tag_ter_immediate
| LDO_I : tag_ter_immediate
          (* storing signd integers *)
| STB_I : tag_ter_immediate
| STW_I : tag_ter_immediate
| STT_I : tag_ter_immediate
| STO_I : tag_ter_immediate
           (* loading unsigned data *)
| LDBU_I : tag_ter_immediate
| LDWU_I : tag_ter_immediate
| LDTU_I : tag_ter_immediate
| LDOU_I : tag_ter_immediate
           (* storing unsigned data *)
| STBU_I : tag_ter_immediate
| STWU_I : tag_ter_immediate
| STTU_I : tag_ter_immediate
| STOU_I : tag_ter_immediate
           (* LDTH instruction *)
| LDTH_I : tag_ter_immediate
(* STHT instruction *)             
| STHT_I : tag_ter_immediate
           (* loading and storing short float *)
| LDSF_I : tag_ter_immediate
| STSF_I : tag_ter_immediate
(* jump with absolute adress *)             
| GO_I : tag_ter_immediate
         (* Conditional assigments *)
| CSZ_I : tag_ter_immediate
| CSNZ_I : tag_ter_immediate
| CSN_I : tag_ter_immediate
| CSNN_I : tag_ter_immediate
| CSP_I : tag_ter_immediate
| CSNP_I : tag_ter_immediate
| CSOD_I : tag_ter_immediate
| CSEV_I : tag_ter_immediate
| ZSZ_I : tag_ter_immediate
| ZSNZ_I : tag_ter_immediate
| ZSN_I : tag_ter_immediate
| ZSNN_I : tag_ter_immediate
| ZSP_I : tag_ter_immediate
| ZSNP_I : tag_ter_immediate
| ZSOD_I : tag_ter_immediate
| ZSEV_I : tag_ter_immediate
(*push_j and pushgo *)
| PUSHJ_I : tag_ter_immediate
| PUSHGO_I : tag_ter_immediate
            (* LDTVS *)
| LDTVS_I : tag_ter_immediate.
               
(* this is tag for instructions with the form (tag reg imm reg) *) 
Inductive tag_ter_immediate2 :=
(* NEG and NEGU *)
| NEG : tag_ter_immediate2
| NEGU : tag_ter_immediate2.

(* this is tag for instructions with the form (tag imm reg reg) *) 
Inductive tag_ter_immediate3 :=
(* preld prest prego *)
| PRELD : tag_ter_immediate3
| PREGO : tag_ter_immediate3
(* syncid *)
| SYNCID : tag_ter_immediate3
(* syncd *)
| SYNCD : tag_ter_immediate3
(* stco instructions *)            
| STCO : tag_ter_immediate3.

(* this is tag for instructions with the form (tag reg imm imm) *) 
Inductive tag_ter_immediate4 :=
(* NEG and NEGU *)
| NEG_I : tag_ter_immediate4
| NEGU_I : tag_ter_immediate4.

(* this is tag for instructions with the form (tag imm imm imm) *) 
Inductive tag_ter_immediate5 :=
  (* trip *)
| TRIP : tag_ter_immediate5
(* trap *)
| TRAP : tag_ter_immediate5
(* swym *)
| SWYM : tag_ter_immediate5.

(* this is tag for instructions with the form (tag imm reg imm) *) 
Inductive tag_ter_immediate6 :=
(* stco *)
| STCO_I2 : tag_ter_immediate6
| STCO_I : tag_ter_immediate6.
  




(* this is tag for instructions with the form (tag reg imm) *) 
Inductive tag_duo_immediate :=
(* floating point arithmetic *)
| FLOT_I : tag_duo_immediate
| FLOTU_I : tag_duo_immediate
(* Converstion of short float *)
| SFLOT_I : tag_duo_immediate
| SFLOTU_I : tag_duo_immediate
(* bitwise operation with 16 bit immediates value *)
| ORH_I : tag_duo_immediate
| ORMH_I : tag_duo_immediate
| ORML_I : tag_duo_immediate
| ORL_I : tag_duo_immediate
| ANDNH_I : tag_duo_immediate
| ANDNMH_I : tag_duo_immediate
| ANDNML_I : tag_duo_immediate
| ANDNL_I : tag_duo_immediate
(* SET ect... *)
| SETH_i : tag_duo_immediate
| SETMH_i : tag_duo_immediate
| SETML_i : tag_duo_immediate
| SETL_i : tag_duo_immediate
(* INCH ect.. *)
| INCH_i : tag_duo_immediate
| INCMH_i : tag_duo_immediate
| INCML_i : tag_duo_immediate
| INCL_i : tag_duo_immediate
(* BRANCHES *)
| BZ_i : tag_duo_immediate
| BNZ_i : tag_duo_immediate         
| BN_i : tag_duo_immediate
| BNN_i : tag_duo_immediate
| BP_i : tag_duo_immediate
| BNP_i : tag_duo_immediate
| BOD_i : tag_duo_immediate
| BEV_i : tag_duo_immediate
| PBZ_i : tag_duo_immediate
| PBNZ_i : tag_duo_immediate         
| PBN_i : tag_duo_immediate
| PBNN_i : tag_duo_immediate
| PBP_i : tag_duo_immediate
| PBNP_i : tag_duo_immediate
| PBOD_i : tag_duo_immediate
| PBEV_i : tag_duo_immediate
(* put and get *)
| GET_i : tag_duo_immediate.
         
         
(* this is tag for instructions with the form (tag imm reg) *)
(* TODO :: delete theese duplicate stuffs just for the scheme equality *)
Inductive tag_duo_immediate2 :=
(* put and get *)
| PUT_I : tag_duo_immediate2
| PUT_I2 : tag_duo_immediate2.

(* this is tag for instructions with the form (tag imm imm) *) 
Inductive tag_duo_immediate3 :=
| POP : tag_duo_immediate3
          (* put and get *)
| PUT_II : tag_duo_immediate3.  

(* this is tag for instructions with the form (tag reg reg) *) 
Inductive tag_duo_normal :=
(* floating point arithmetic *)
| FLOT : tag_duo_normal
| FLOTU : tag_duo_normal
| FIX : tag_duo_normal
| FIXU : tag_duo_normal
(* Converstion of short float *)
| SFLOT : tag_duo_normal
| SFLOTU : tag_duo_normal.


Inductive tag_uno :=
  (* jumps with relative adress *)
| JMP : tag_uno
          (* save unsave *)
| SAVE : tag_uno
| UNSAVE : tag_uno
             (* resume *)
| RESUME : tag_uno
(* sync *)
| SYNC : tag_uno.         


Inductive tag :=
| tag_t_n : tag_ter_normal -> tag
| tag_t_i : tag_ter_immediate -> tag
| tag_t_i2 : tag_ter_immediate2 -> tag
| tag_t_i3 : tag_ter_immediate3 -> tag
| tag_t_i4 : tag_ter_immediate4 -> tag
| tag_t_i5 : tag_ter_immediate5 -> tag
| tag_t_i6 : tag_ter_immediate6 -> tag                                     
| tag_d_i : tag_duo_immediate -> tag
| tag_d_i2 : tag_duo_immediate2 -> tag
| tag_d_i3 : tag_duo_immediate3 -> tag
| tag_d_n : tag_duo_normal -> tag
| tag_u : tag_uno -> tag.


Scheme Equality for tag.


Lemma tag_beq_reflexivity : forall (t :tag), tag_beq t t = true.
Proof.
  destruct t ; destruct t ; reflexivity.
Qed.
  
Lemma tag_beq_different : forall (t1 t2 : tag), tag_beq t1 t2 = true -> t1 = t2.
Proof.
Admitted.
    

(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)


Inductive  imediate :=
  imm : nat -> imediate.
Inductive register :=
  reg : nat -> register.

Inductive operande :=
  | imm_o : imediate -> operande
  | reg_o : register -> operande.
 

(* instruction definition *)
Record instruction_tern_n :=
  mk_instr_t_n { instr_opcode_t_n : tag_ter_normal; 
             instr_operande1_t_n : register ; 
             instr_operande2_t_n : register ; 
             instr_operande3_t_n : register }.

Record instruction_tern_i :=
  mk_instr_t_i { instr_opcode_t_i : tag_ter_immediate; 
             instr_operande1_t_i : register ; 
             instr_operande2_t_i : register ; 
             instr_operande3_t_i : imediate }.

Record instruction_tern_i2 :=
  mk_instr_t_i2 { instr_opcode_t_i2 : tag_ter_immediate2; 
             instr_operande1_t_i2 : register ; 
             instr_operande2_t_i2 : imediate ; 
             instr_operande3_t_i2 : register }.

Record instruction_tern_i3 :=
  mk_instr_t_i3 { instr_opcode_t_i3 : tag_ter_immediate3; 
             instr_operande1_t_i3 : imediate ; 
             instr_operande2_t_i3 : register ; 
             instr_operande3_t_i3 : register }.

Record instruction_tern_i4 :=
  mk_instr_t_i4 { instr_opcode_t_i4 : tag_ter_immediate4; 
             instr_operande1_t_i4 : register ; 
             instr_operande2_t_i4 : imediate ; 
             instr_operande3_t_i4 : imediate }.

Record instruction_tern_i5 :=
  mk_instr_t_i5 { instr_opcode_t_i5 : tag_ter_immediate5; 
             instr_operande1_t_i5 : imediate ; 
             instr_operande2_t_i5 : imediate ; 
             instr_operande3_t_i5 : imediate }.

Record instruction_tern_i6 :=
  mk_instr_t_i6 { instr_opcode_t_i6 : tag_ter_immediate6; 
             instr_operande1_t_i6 : imediate ; 
             instr_operande2_t_i6 : register ; 
             instr_operande3_t_i6 : imediate }.


Record instruction_duo_n :=
  mk_instr_d_n { instr_opcode_d_n : tag_duo_normal; 
             instr_operande1_d_n : register ; 
             instr_operande2_d_n : register }.

Record instruction_duo_i :=
  mk_instr_d_i { instr_opcode_d_i : tag_duo_immediate; 
             instr_operande1_d_i : register ; 
             instr_operande2_d_i : imediate }.

Record instruction_duo_i2 :=
  mk_instr_d_i2 { instr_opcode_d_i2 : tag_duo_immediate2; 
             instr_operande1_d_i2 : imediate ; 
             instr_operande2_d_i2 : register }.

Record instruction_duo_i3 :=
  mk_instr_d_i3 { instr_opcode_d_i3 : tag_duo_immediate3; 
             instr_operande1_d_i3 : imediate ; 
             instr_operande2_d_i3 : imediate }.

Record instruction_uno :=
  mk_instr_uno { instr_opcode_s : tag_uno;
                 instr_operande : imediate }.




Inductive instruction :=
| instr_t_n : instruction_tern_n -> instruction
| instr_t_i : instruction_tern_i -> instruction
| instr_t_i2 : instruction_tern_i2 -> instruction
| instr_t_i3 : instruction_tern_i3 -> instruction
| instr_t_i4 : instruction_tern_i4 -> instruction
| instr_t_i5 : instruction_tern_i5 -> instruction
| instr_t_i6 : instruction_tern_i6 -> instruction
| instr_d_n : instruction_duo_n -> instruction
| instr_d_i : instruction_duo_i -> instruction
| instr_d_n2 : instruction_duo_i2 -> instruction
| instr_d_n3 : instruction_duo_i3 -> instruction
| instr_u : instruction_uno -> instruction.
(* binary instruction definition *)
Definition binary_instruction := list bool.


(* some example to test the record structure *)
(* Example my_instr := mk_instr_t_i (tag_t_i ADD_I) (reg 10) (reg 11) (imm 12). *)

(* Example first_field_instr := my_instr.(instr_opcode_t_i).  *)


