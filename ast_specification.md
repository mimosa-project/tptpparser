# 方針
* 基本的に子が一つしかなく記号などを含んでいない場合は飛ばす
* 子が二つ以上あるものは基本的に残す
    * 子が二つ以上ある場合の内、ノードA : ノードB "," ノードAのように再帰されているものは飛ばすそれ以外は残す
* ノード名 | "(" ノード名 ")" or "[" ノード名 "]"の場合は"(" ノード名 ")" or "[" ノード名 "]"場合のときのみ残す
    * thf_atom_typing      : UNTYPED_ATOM ":" thf_top_level_type | "(" thf_atom_typing ")"のように文法のノード名と"(" ノード名 ")"のノード名が同じなら飛ばす
    * tf1_quantified_type  : "!>" "[" tff_variable_list "]" ":" tff_monotypeや、tcf_quantified_formula : "!" "[" tff_variable_list "]" ":" cnf_formulaのように文字列"[" ノード名 "]" ":" ノード名となっている場合は、文字列に書き換えて、"[" ノード名 "]"のノード名は飛ばさないようにする
* ノード名 トークン(二項演算子)or記号(@など) ノード名となっている場合はそのノードを二項演算子、記号に書き換える(例：thf_unit_formula "@" thf_unit_formulaの場合は@に書き換える)
* 文字列"("ノード名...")" or トークン"("ノード名...")" or ~などの文字列もしくはトークン ノード名となっている場合は、文字列、トークンに書き換える(例："\$ite(" thf_logic_formula "," thf_logic_formula "," thf_logic_formula ")"のときは\$iteに書き換える)
* 子が一つしかないかつ子がすべてトークンならそのノードをトークンにする
* 葉になる場合は残す("[]" などの場合)

# 方針に従った際の処理
単に飛ばす
``` lark
tptp_input           : annotated_formula | include
annotated_formula    : thf_annotated | tff_annotated | tcf_annotated | fof_annotated | cnf_annotated | tpi_annotated
thf_formula          : thf_logic_formula | thf_atom_typing | thf_subtype | thf_sequent
tff_formula          : tff_logic_formula | tff_atom_typing | tff_subtype | tfx_sequent
tcf_formula          : tcf_logic_formula | tff_atom_typing
fof_formula          : fof_logic_formula | fof_sequent
fof_unit_formula     : fof_unitary_formula | fof_unary_formula
tpi_formula          : fof_formula
thf_logic_formula    : thf_unitary_formula | thf_unary_formula | thf_binary_formula | thf_defined_infix
thf_binary_formula   : thf_binary_nonassoc | thf_binary_assoc | thf_binary_type
thf_binary_assoc     : thf_or_formula | thf_and_formula | thf_apply_formula

thf_unit_formula     : thf_unitary_formula | thf_unary_formula | thf_defined_infix
thf_preunit_formula  : thf_unitary_formula | thf_prefix_unary

thf_quantified_formula : thf_quantification thf_unit_formula

thf_unary_formula    : thf_prefix_unary | thf_infix_unary
thf_atomic_formula   : thf_plain_atomic | thf_defined_atomic | thf_system_atomic | thf_fof_function
thf_plain_atomic     : CONSTANT | thf_tuple 

thf_arguments        : thf_formula_list

thf_top_level_type   : thf_unitary_type | thf_mapping_type | thf_apply_type

thf_unitary_type     : thf_unitary_formula

thf_apply_type       : thf_apply_formula
thf_binary_type      : thf_mapping_type | thf_xprod_type | thf_union_type
tff_logic_formula    : tff_unitary_formula | tff_unary_formula | tff_binary_formula | tff_defined_infix

tff_binary_formula   : tff_binary_nonassoc | tff_binary_assoc
tff_binary_assoc     : tff_or_formula | tff_and_formula
tff_unit_formula     : tff_unitary_formula | tff_unary_formula | tff_defined_infix
tff_preunit_formula  : tff_unitary_formula | tff_prefix_unary


tff_variable         : tff_typed_variable | VARIABLE
tff_unary_formula    : tff_prefix_unary | tff_infix_unary
tff_atomic_formula   : tff_plain_atomic | tff_defined_atomic | tff_system_atomic
tff_defined_atomic   : tff_defined_plain 


tfx_let_lhs          : tff_plain_atomic | tfx_tuple


tff_term             : tff_logic_formula | DEFINED_TERM | tfx_tuple


tff_top_level_type   : tff_atomic_type | tff_non_atomic_type
tff_non_atomic_type  : tff_mapping_type | tf1_quantified_type | "(" tff_non_atomic_type ")"


tcf_logic_formula    : tcf_quantified_formula | cnf_formula

fof_logic_formula    : fof_binary_formula | fof_unary_formula | fof_unitary_formula

fof_binary_formula   : fof_binary_nonassoc | fof_binary_assoc
fof_binary_assoc     : fof_or_formula | fof_and_formula


fof_atomic_formula   : fof_plain_atomic_formula | fof_defined_atomic_formula | fof_system_atomic_formula
fof_plain_atomic_formula : fof_plain_term

fof_defined_atomic_formula : fof_defined_plain_formula | fof_defined_infix_formula
fof_defined_plain_formula : fof_defined_plain_term


fof_system_atomic_formula : fof_system_term
fof_defined_term     : DEFINED_TERM | fof_defined_atomic_term
fof_defined_atomic_term  : fof_defined_plain_term

fof_term             : fof_function_term | VARIABLE
fof_function_term    : fof_plain_term | fof_defined_term | fof_system_term

source               : general_term

useful_info          : general_list

general_data         : ATOMIC_WORD | general_function | VARIABLE | NUMBER | DISTINCT_OBJECT | formula_data
null                 :
```

飛ばす（再帰）
``` lark
thf_variable_list    : thf_typed_variable | thf_typed_variable "," thf_variable_list
thf_atom_typing_list : thf_atom_typing | thf_atom_typing "," thf_atom_typing_list
thf_let_defn_list    : thf_let_defn | thf_let_defn "," thf_let_defn_list
thf_formula_list     : thf_logic_formula | thf_logic_formula "," thf_formula_list
tff_variable_list    : tff_variable | tff_variable "," tff_variable_list
tff_atom_typing_list : tff_atom_typing | tff_atom_typing "," tff_atom_typing_list
tfx_let_defn_list    : tfx_let_defn | tfx_let_defn "," tfx_let_defn_list
tff_arguments        : tff_term | tff_term "," tff_arguments
tff_type_arguments   : tff_atomic_type | tff_atomic_type "," tff_type_arguments
tff_type_list        : tff_top_level_type | tff_top_level_type "," tff_type_list
fof_variable_list    : VARIABLE | VARIABLE "," fof_variable_list
fof_arguments        : fof_term | fof_term "," fof_arguments
fof_formula_tuple_list : fof_logic_formula |  fof_logic_formula "," fof_formula_tuple_list
name_list            : NAME | NAME name_list
general_terms        : general_term | general_term "," general_terms
```

"(" disjunction ")"なら残す、それ以外は飛ばす
``` lark
cnf_formula          : disjunction | "(" disjunction ")"
```

@に書き換える
``` lark
thf_apply_formula    : thf_unit_formula "@" thf_unit_formula | thf_apply_formula "@" thf_unit_formula
```

"(" thf_logic_formula ")"の場合は残す、それ以外は飛ばす
``` lark
thf_unitary_formula  : thf_quantified_formula | thf_atomic_formula | VARIABLE | "(" thf_logic_formula ")"
```

:に書き換える
``` lark
thf_typed_variable   : VARIABLE ":" thf_top_level_type
```

"(" thf_conn_term ")"の場合は残す、それ以外は飛ばす
``` lark
thf_defined_atomic   : DEFINED_CONSTANT | thf_conditional | thf_let | "(" thf_conn_term ")" | thf_defined_term
```

$iteに書き換える
``` lark
thf_conditional      : "$ite(" thf_logic_formula "," thf_logic_formula "," thf_logic_formula ")"
```

$letに書き換える
``` lark
thf_let              : "$let(" thf_let_types "," thf_let_defns "," thf_formula ")"
```

"[" thf_let_defn_list "]"の場合は残す、それ以外は飛ばす
``` lark
thf_let_defns        : thf_let_defn | "[" thf_let_defn_list "]"
```

"[" thf_atom_typing_list "]"の場合は残す、それ以外は飛ばす
``` lark
thf_let_types        : thf_atom_typing | "[" thf_atom_typing_list "]"
```

"(" thf_logic_formula ")"の場合は残す、それ以外は飛ばす
``` lark
thf_unitary_term     : thf_atomic_formula | VARIABLE | "(" thf_logic_formula ")"
```

UNTYPED_ATOM ":" thf_top_level_typeなら":"に書き換える、"(" thf_atom_typing ")"なら飛ばす
``` lark
thf_atom_typing      : UNTYPED_ATOM ":" thf_top_level_type | "(" thf_atom_typing ")"
```

"(" tff_logic_formula ")"の場合は残す、それ以外は飛ばす
``` lark
tff_unitary_formula  : tff_quantified_formula | tff_atomic_formula | tfx_unitary_formula | "(" tff_logic_formula ")"
```

:に書き換える
``` lark
tff_typed_variable   : VARIABLE ":" tff_atomic_type
```

$iteに書き換える
``` lark
tfx_conditional      : "$ite(" tff_logic_formula "," tff_term "," tff_term ")"
```

$letに書き換える
``` lark
tfx_let              : "$let(" tfx_let_types "," tfx_let_defns "," tff_term ")"
```

"[" tff_atom_typing_list "]"なら残す、それ以外は飛ばす
``` lark
tfx_let_types        : tff_atom_typing | "[" tff_atom_typing_list "]"
```

"[" tfx_let_defn_list "]"なら残す、それ以外は飛ばす
``` lark
tfx_let_defns        : tfx_let_defn | "[" tfx_let_defn_list "]"
```

"(" tff_logic_formula ")"の場合は残す、それ以外は飛ばす
``` lark
tff_unitary_term     : tff_atomic_formula | DEFINED_TERM | tfx_tuple | VARIABLE | "(" tff_logic_formula ")"
```

UNTYPED_ATOM ":" tff_top_level_typeなら:に書き換える、"("tff_atom_typing")"なら飛ばす
``` lark
tff_atom_typing      : UNTYPED_ATOM ":" tff_top_level_type | "("tff_atom_typing")"
```

!>に書き換える、tff_variable_listは残す
``` lark
tf1_quantified_type  : "!>" "[" tff_variable_list "]" ":" tff_monotype
```

"(" tff_mapping_type ")"の場合は残す、それ以外は飛ばす
``` lark
tff_monotype         : tff_atomic_type | "(" tff_mapping_type ")" | tf1_quantified_type
```

"(" tff_xprod_type ")"の場合は残す、それ以外は飛ばす
``` lark
tff_unitary_type     : tff_atomic_type | "(" tff_xprod_type ")"
```

!に書き換え、tff_variable_listは残す
``` lark
tcf_quantified_formula : "!" "[" tff_variable_list "]" ":" cnf_formula
```

defined_infix_predに書き換える
``` lark
fof_defined_infix_formula : fof_term defined_infix_pred fof_term
```

UNARY_CONNECTIVE fof_unit_formulaならUNARY_CONNECTIVEに書き換える、それ以外は飛ばす
``` lark
fof_unary_formula    : UNARY_CONNECTIVE fof_unit_formula | fof_infix_unary
```

"(" fof_logic_formula ")"なら残す、それ以外は飛ばす
``` lark
fof_unitary_formula  : fof_quantified_formula | fof_atomic_formula | "(" fof_logic_formula ")"
```

"~" fof_atomic_formulaなら"~"に書き換える、それ以外は飛ばす
``` lark
literal              : fof_atomic_formula | "~" fof_atomic_formula | fof_infix_unary
```

general_data ":" general_termなら:に書き換える、それ以外は飛ばす
``` lark
general_term         : general_data | general_data ":" general_term | general_list
```

それぞれ\$thf、\$tff、\$fof、\$cnf、\$fotに書き換える
``` lark
formula_data         : "$thf(" thf_formula ")" | "$tff(" tff_formula ")" | "$fof(" fof_formula ")" | "$cnf(" cnf_formula ")" | "$fot(" fof_term ")"
```

飛ばすがNONASSOC_CONNECTIVEに書き換える
``` lark
thf_binary_nonassoc  : thf_unit_formula NONASSOC_CONNECTIVE thf_unit_formula
```

飛ばすがVLINEに書き換える
``` lark
thf_or_formula       : thf_unit_formula VLINE thf_unit_formula | thf_or_formula VLINE thf_unit_formula
```

飛ばすがAND_CONNECTIVEに書き換える
``` lark
thf_and_formula      : thf_unit_formula AND_CONNECTIVE thf_unit_formula | thf_and_formula AND_CONNECTIVE thf_unit_formula
```

飛ばすがTHF_QUANTIFIERに書き換える
``` lark
thf_quantification   : THF_QUANTIFIER "[" thf_variable_list "]" ":"
```

飛ばすがUNARY_CONNECTIVEに書き換える
``` lark
thf_prefix_unary     : UNARY_CONNECTIVE thf_preunit_formula
```

飛ばすがINFIX_INEQUALITYに書き換える
``` lark
thf_infix_unary      : thf_unitary_term INFIX_INEQUALITY thf_unitary_term
```

飛ばすがdefined_infix_predに書き換える
``` lark
thf_defined_infix    : thf_unitary_term defined_infix_pred thf_unitary_term
```

飛ばすがFUNCTOR、 DEFINED_FUNCTOR、SYSTEM_FUNCTORに書き換える
``` lark
thf_fof_function     : FUNCTOR "(" thf_arguments ")" | DEFINED_FUNCTOR "(" thf_arguments ")" | SYSTEM_FUNCTOR "(" thf_arguments ")"
```

飛ばすがASSIGNMENTに書き換える
``` lark
thf_let_defn         : thf_logic_formula ASSIGNMENT thf_logic_formula
```

飛ばすがARROWに書き換える
``` lark
thf_mapping_type     : thf_unitary_type ARROW thf_unitary_type | thf_unitary_type ARROW thf_mapping_type
```

飛ばすがSTARに書き換える
``` lark
thf_xprod_type       : thf_unitary_type STAR thf_unitary_type | thf_xprod_type STAR thf_unitary_type
```

飛ばすがPLUSに書き換える
``` lark
thf_union_type       : thf_unitary_type PLUS thf_unitary_type | thf_union_type PLUS thf_unitary_type
```

飛ばすがGENTZEN_ARROWに書き換える
``` lark
thf_sequent          : thf_tuple GENTZEN_ARROW thf_tuple | "(" thf_sequent ")"
```

飛ばすがNONASSOC_CONNECTIVEに書き換える
``` lark
tff_binary_nonassoc  : tff_unit_formula NONASSOC_CONNECTIVE tff_unit_formula
```

飛ばすがVLINEに書き換える
``` lark
tff_or_formula       : tff_unit_formula VLINE tff_unit_formula | tff_or_formula VLINE tff_unit_formula
```

飛ばすがAND_CONNECTIVEに書き換える
``` lark
tff_and_formula      : tff_unit_formula AND_CONNECTIVE tff_unit_formula | tff_and_formula AND_CONNECTIVE tff_unit_formula
```

飛ばすがFOF_QUANTIFIERに書き換える
``` lark
tff_quantified_formula : FOF_QUANTIFIER "[" tff_variable_list "]" ":" tff_unit_formula
```

飛ばすがUNARY_CONNECTIVEに書き換える
``` lark
tff_prefix_unary     : UNARY_CONNECTIVE tff_preunit_formula
```

飛ばすがINFIX_INEQUALITYに書き換える
``` lark
tff_infix_unary      : tff_unitary_term INFIX_INEQUALITY tff_unitary_term
```

飛ばすがFUNCTOR"("tff_arguments")"の場合はFUNCTORに書き換える
``` lark
tff_plain_atomic     : CONSTANT | FUNCTOR"("tff_arguments")"
```

飛ばすがDEFINED_FUNCTOR "(" tff_arguments ")"ならDEFINED_FUNCTORに書き換える
``` lark
tff_defined_plain    : DEFINED_CONSTANT | DEFINED_FUNCTOR "(" tff_arguments ")" | tfx_conditional | tfx_let
```

飛ばすがdefined_infix_predに書き換える
``` lark
tff_defined_infix    : tff_unitary_term defined_infix_pred tff_unitary_term
```

飛ばすがSYSTEM_FUNCTOR "(" tff_arguments ")"ならSYSTEM_FUNCTORに書き換える
``` lark
tff_system_atomic    : SYSTEM_CONSTANT | SYSTEM_FUNCTOR "(" tff_arguments ")"
```

飛ばすがASSIGNMENTに書き換える
``` lark
tfx_let_defn         : tfx_let_lhs ASSIGNMENT tff_term
```

飛ばすがTYPE_FUNCTOR "(" tff_type_arguments ")"の場合はTYPE_FUNCTORに書き換え、tff_type_argumentsは残す、"(" tff_atomic_type ")"なら残す、それ以外は飛ばす
``` lark
tff_atomic_type      : TYPE_CONSTANT | DEFINED_TYPE | VARIABLE | TYPE_FUNCTOR "(" tff_type_arguments ")" | "(" tff_atomic_type ")" | tfx_tuple_type
```

飛ばすがARROWに書き換える
``` lark
tff_mapping_type     : tff_unitary_type ARROW tff_atomic_type
```

飛ばすがSTARに書き換える
``` lark
tff_xprod_type       : tff_unitary_type STAR tff_atomic_type | tff_xprod_type STAR tff_atomic_type
```

飛ばすがSUBTYPE_SIGNに書き換える
``` lark
tff_subtype          : UNTYPED_ATOM SUBTYPE_SIGN ATOM 
```

飛ばすがtfx_tuple GENTZEN_ARROW tfx_tupleの場合はGENTZEN_ARROWに書き換える
``` lark
tfx_sequent          : tfx_tuple GENTZEN_ARROW tfx_tuple | "(" tfx_sequent ")"
```

飛ばすがNONASSOC_CONNECTIVEに書き換える
``` lark
fof_binary_nonassoc  : fof_unit_formula NONASSOC_CONNECTIVE fof_unit_formula
```

飛ばすがVLINEに書き換える
``` lark
fof_or_formula       : fof_unit_formula VLINE fof_unit_formula | fof_or_formula VLINE fof_unit_formula
```

飛ばすがAND_CONNECTIVEに書き換える
``` lark
fof_and_formula      : fof_unit_formula AND_CONNECTIVE fof_unit_formula | fof_and_formula AND_CONNECTIVE fof_unit_formula
```

飛ばすがINFIX_INEQUALITYに書き換える
``` lark
fof_infix_unary      : fof_term INFIX_INEQUALITY fof_term
```

飛ばすがFOF_QUANTIFIERに書き換える
``` lark
fof_quantified_formula : FOF_QUANTIFIER "[" fof_variable_list "]" ":" fof_unit_formula
```

飛ばすがFUNCTOR "(" fof_arguments ")"の場合はFUNCTORに書き換える
``` lark
fof_plain_term       : CONSTANT | FUNCTOR "(" fof_arguments ")"
```

飛ばすがDEFINED_FUNCTOR "(" fof_arguments ")"の場合はDEFINED_FUNCTORに書き換える
``` lark
fof_defined_plain_term   : DEFINED_CONSTANT | DEFINED_FUNCTOR "(" fof_arguments ")"
```

飛ばすがSYSTEM_FUNCTOR "(" fof_arguments ")"のときはSYSTEM_FUNCTORに書き換える
``` lark
fof_system_term      : SYSTEM_CONSTANT | SYSTEM_FUNCTOR "(" fof_arguments ")"
```

飛ばすがATOMIC_WORDに変更する
``` lark
general_function     : ATOMIC_WORD "(" general_terms ")"
```

飛ばすがdisjunction VLINE literalの場合はVLINEに書き換える
``` lark
disjunction          : literal | disjunction VLINE literal
```

飛ばすがfof_formula_tuple GENTZEN_ARROW fof_formula_tupleの場合はGENTZEN_ARROWに書き換える
``` lark
fof_sequent          : fof_formula_tuple GENTZEN_ARROW fof_formula_tuple | "(" fof_sequent ")"
```

tpiに書き換える
``` lark
tpi_annotated        : "tpi" "(" NAME "," formula_role "," tpi_formula annotations ")" "."
```

thfに書き換える
``` lark
thf_annotated        : "thf" "(" NAME "," formula_role "," thf_formula annotations ")" "."
```

tffに書き換える
``` lark
tff_annotated        : "tff" "(" NAME "," formula_role "," tff_formula annotations ")" "."
```

tchに書き換える
``` lark
tcf_annotated        : "tcf" "(" NAME "," formula_role "," tcf_formula annotations ")" "."
```

fofに書き換える
``` lark
fof_annotated        : "fof" "(" NAME "," formula_role "," fof_formula annotations ")" "."
```

cnfに書き換える
``` lark
cnf_annotated        : "cnf" "(" NAME "," formula_role "," cnf_formula annotations ")" "."
```

includeに書き換える(ノード名と文字列が等しい為、必要ない)
``` lark
include              : "include" "(" FILE_NAME formula_selection ")" "."
```

飛ばさない
``` lark
tptp_root            : tptp_input*
annotations          :  "," source optional_info | null
optional_info        : "," useful_info | null
thf_tuple            : "[]" | "[" thf_formula_list "]"
tfx_tuple            : "[]" | "[" tff_arguments "]"
tfx_tuple_type       : "[" tff_type_list "]"
fof_formula_tuple    : "{}" | "{" fof_formula_tuple_list "}"
formula_selection    : "," "[" name_list "]" | null
general_list         : "[]" | "[" general_terms "]"
thf_subtype          : UNTYPED_ATOM SUBTYPE_SIGN ATOM
```

トークンにする
``` lark
formula_role         : LOWER_WORD
thf_defined_term     : DEFINED_TERM | TH1_DEFINED_TERM
thf_system_atomic    : SYSTEM_CONSTANT
thf_conn_term        : NONASSOC_CONNECTIVE | ASSOC_CONNECTIVE |INFIX_EQUALITY | INFIX_INEQUALITY | UNARY_CONNECTIVE
tfx_unitary_formula  : VARIABLE
defined_infix_pred   : INFIX_EQUALITY
```