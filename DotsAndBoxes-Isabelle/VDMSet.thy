theory VDMSet
imports VDMToolKit
begin

section {* VDM set operators *}

text{*
VDM set operators have a direct correspondence in Isabelle. TODO? 
*}

text {* set comprehension *}

(* { expr | var . filter }, { var \<in> type . filter }, { var . filter } *)

(*declare [[show_types]]*)
value "{ x+x | x . x \<in> {(1::nat),2,3} }"

value "{ x+x | x . x \<in> {(1::nat),2,3} }"

(*value "{ x+x | x . x \<in> {(1::nat)..3} }" --"not always work"*)

lemma "{ x . x \<in> {1,(2::nat), 3} | x \<le> 2} = { x \<in> {1,2,3} . x \<le> 2 }"
find_theorems "_ = (_::'a set)" intro
apply (rule equalityI)
apply (rule subsetI, simp)
defer
apply (rule subsetI, simp, elim disjE, simp_all) oops


value "{ [A,B,C,D,E,F] ! i | i . i \<in> {0,2,4} }"

(* { s(i) | i in set inds s & i mod 2 = 0 } *)

text{* Sequences may have invariants within their inner type. *}

type_synonym 'a VDMSet = "'a set"

definition 
  inv_SetElems :: "('a \<Rightarrow> \<bool>) \<Rightarrow> 'a VDMSet \<Rightarrow> \<bool>"
where
  "inv_SetElems einv s \<equiv> \<forall> e \<in> s . einv e"

lemma l_inv_SetElems_Cons: "(inv_SetElems f (insert a s)) = (f a \<and> (inv_SetElems f s))"
unfolding inv_SetElems_def
by auto

(*
text {* Useful example for XO if you use set comprehension *}

type_synonym Pos = "(\<nat> \<times> \<nat>)"
type_synonym Line = "Pos set"

abbreviation SIZE :: \<nat> where "SIZE \<equiv> 3"

abbreviation
  BOARD :: "\<nat> set"
where
  "BOARD \<equiv> {1 .. 3}"

definition
  inv_Pos :: "Pos \<Rightarrow> bool"
where
  "inv_Pos z \<equiv> let (x,y) = z in  
                  nat1 x \<and> x \<le> SIZE \<and> 
                  nat1 y \<and> y \<le> SIZE"

definition
  row :: "nat \<Rightarrow> Line"
where
  "row rr \<equiv> { (rr, c) | c . c \<in> BOARD \<and> inv_Pos (rr, c) }"

lemma "row 1 = A"
unfolding row_def inv_Pos_def nat1G0
apply simp
oops

definition
  col :: "nat \<Rightarrow> Line"
where
  "col cc \<equiv> { (r,cc) | r . r \<in> BOARD \<and> inv_Pos (r, cc) }"

lemma "row 1 = A" unfolding row_def inv_Pos_def apply simp oops

abbreviation
  allRows0 :: "Line set"
where
  "allRows0 \<equiv> { row 1, row 2, row 3 }"

abbreviation
  allRows :: "Line set"
where
  "allRows \<equiv> \<Union> r \<in> BOARD . { row r }"
 
abbreviation
  allCols :: "Line set"
where
  "allCols \<equiv> \<Union> c \<in> BOARD . { col c }"

abbreviation
  downwardDiag :: "Line"
where
  "downwardDiag \<equiv> { (x,x)| x . x \<in> BOARD }"

abbreviation
  upwardDiag :: "Line"
where
  "upwardDiag \<equiv> { (x,y) . x \<in> BOARD \<and> y = SIZE-x+(1::nat) }"

(* Use definition to tame unfolding *)
definition
  winningLines :: "Line set"
where
   "winningLines \<equiv> allRows \<union> allCols \<union> {downwardDiag, upwardDiag}"

abbreviation
  explicitWinningLines :: "Line set"
where
  "explicitWinningLines \<equiv> 
          { {(1, 1), (1, 2), (1, 3)}, 
					 	{(2, 1), (2, 2), (2, 3)}, 
					  {(3, 1), (3, 2), (3, 3)},  

					  {(1, 1), (2, 1), (3, 1)}, 
					  {(1, 2), (2, 2), (3, 2)}, 
					  {(1, 3), (2, 3), (3, 3)}, 

					  {(1, 1), (2, 2), (3, 3)},
 
					  {(1, 3), (2, 2), (3, 1)}
				  }"	
*)

end
