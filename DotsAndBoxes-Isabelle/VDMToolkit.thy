theory VDMToolkit
imports Main
begin

type_notation bool ("\<bool>")
type_notation nat ("\<nat>")
type_notation int ("\<int>")

(*****************************************************************)      
section {* Basic types *}  
  
type_synonym VDMNat  = \<int>
type_synonym VDMNat1 = \<int>
type_synonym VDMInt  = \<int>

definition
  inv_VDMNat :: "\<int> \<Rightarrow> \<bool>"
where
  (*<*) [intro!]: (*>*) 
  "inv_VDMNat n \<equiv> n \<ge> 0"

definition
  inv_VDMNat1 :: "\<int> \<Rightarrow> \<bool>"
where
  (*<*)[intro!]: (*>*) 
  "inv_VDMNat1 n \<equiv> n > 0"

(*****************************************************************)      
section {* Sets *}
  
type_synonym 'a VDMSet = "'a set"

definition 
  inv_SetElems :: "('a \<Rightarrow> \<bool>) \<Rightarrow> 'a VDMSet \<Rightarrow> \<bool>"
where
  "inv_SetElems einv s \<equiv> \<forall> e \<in> s . einv e"

lemma l_inv_SetElems_Cons: "(inv_SetElems f (insert a s)) = (f a \<and> (inv_SetElems f s))"
unfolding inv_SetElems_def
by auto

definition
  inv_VDMSet :: "'a VDMSet \<Rightarrow> \<bool>"
  where
   [intro!]:  "inv_VDMSet v \<equiv> finite v"

definition
  vdm_card :: "'a VDMSet \<Rightarrow> VDMNat"
  where
    "vdm_card s \<equiv> (if finite s then int (card s) else undefined)"

definition
  pre_vdm_card :: "'a VDMSet \<Rightarrow> \<bool>"
  where
  [intro!]:  "pre_vdm_card s \<equiv> inv_VDMSet s"

definition
  post_vdm_card :: "'a VDMSet \<Rightarrow> VDMNat \<Rightarrow> \<bool>"
  where
  [intro!]:  "post_vdm_card s RESULT \<equiv> inv_VDMNat RESULT"
  
lemma "vdm_card {0,1,(2::int)} = 3"
  unfolding vdm_card_def by simp 

lemma l_vdm_card_finite[simp]: "finite s \<Longrightarrow> vdm_card s = int (card s)"
  unfolding vdm_card_def by simp

lemma l_vdm_card_range[simp]: "x \<le> y \<Longrightarrow> vdm_card {x .. y} = y - x + 1"
  unfolding vdm_card_def by simp 

lemma l_vdm_card_positive: 
  "finite s \<Longrightarrow> vdm_card s \<ge> 0"
  by simp
    
lemma l_vdm_card_non_negative:
  "finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> vdm_card s > 0"
  by (simp add: card_gt_0_iff)
    
theorem PO_feas_vdm_card:
  "pre_vdm_card s \<Longrightarrow> post_vdm_card s (vdm_card s)"
  by (simp add: inv_VDMNat_def inv_VDMSet_def post_vdm_card_def pre_vdm_card_def)
    
(*****************************************************************)      
section {* Sequences *}

type_synonym 'a VDMSeq = "'a list"

text{* Isabelle's list @{term hd} and @{term tl} functions have the
same name as VDM. Nevertheless, their results is defined for empty lists.
We need to rule them out.
*}

definition
  pre_hd :: "'a VDMSeq \<Rightarrow> \<bool>"
where
  "pre_hd s \<equiv> s \<noteq> []"

definition
  pre_tl :: "'a VDMSeq \<Rightarrow> \<bool>"
where
  "pre_tl s \<equiv> s \<noteq> []"

definition
   len :: "'a VDMSeq \<Rightarrow> VDMNat"
where
   "len l \<equiv> int (length l)"

definition
  inv_VDMSeq1 :: "'a VDMSeq \<Rightarrow> \<bool>"
where
  "inv_VDMSeq1 s \<equiv> len s \<ge> 1"

lemma l_len_append: "len(xs @ [x]) = 1 + len xs"
apply (induct xs)
apply simp_all
unfolding len_def by simp_all

lemma l_len_empty: "len [] = 0" unfolding len_def by simp

lemma l_len_cons[simp]: "len(x # xs) = 1 + len xs"
apply (induct xs)
unfolding len_def by simp_all

definition 
  elems :: "'a VDMSeq \<Rightarrow> 'a set"
where
  "elems l \<equiv> set l"

lemma l_elems_append: "elems (xs @ [x]) = insert x (elems xs)"
unfolding elems_def by simp

lemma l_elems_cons: "elems (x # xs) = insert x (elems xs)"
unfolding elems_def by simp

lemma l_elems_empty[simp]: "elems [] = {}" unfolding elems_def by simp

lemma l_inj_seq: "distinct s \<Longrightarrow> nat (len s) = card (elems s)"
by (induct s) (simp_all add: l_elems_cons  elems_def len_def)

text{* Be careful with representation differences 
   VDM lists are 1-based, whereas Isabelle list 
   are 0-based. This function returns {0,1,2}
   for sequence [A, B, C] instead of {1,2,3} *}

definition
   inds0 :: "'a VDMSeq \<Rightarrow> VDMNat set"
where
  "inds0 l \<equiv> {0 ..< len l}"

value "inds0 [A, B, C]"
(* indexes are 0, 1, 2; VDM would give 1, 2, 3 *)

definition
   inds :: "'a VDMSeq \<Rightarrow> VDMNat1 set"
where
  "inds l \<equiv> {1 .. len l}"

lemma l_inds_append: "inds (xs @ [x]) = insert (len (xs @ [x])) (inds xs)"
unfolding inds_def  
by (simp add: atLeastAtMostPlus1_int_conv len_def)

lemma l_len_within_inds[simp]: "s \<noteq> [] \<Longrightarrow> len s \<in> inds s"
unfolding len_def inds_def
apply (induct s)
by simp_all

definition
   inds_as_nat :: "'a VDMSeq \<Rightarrow> \<nat> set"
where
  "inds_as_nat l \<equiv> {1 .. nat (len l)}"

lemma l_inds_as_nat_append: "inds_as_nat (xs @ [x]) = insert (length (xs @ [x])) (inds_as_nat xs)"
unfolding inds_as_nat_def len_def by auto 

text{* Sequences may have invariants within their inner type. *}

definition 
  inv_SeqElems0 :: "('a \<Rightarrow> \<bool>) \<Rightarrow> 'a VDMSeq \<Rightarrow> \<bool>"
where
  "inv_SeqElems0 einv s \<equiv> \<forall> e \<in> (elems s) . einv e"

definition 
  inv_SeqElems :: "('a \<Rightarrow> \<bool>) \<Rightarrow> 'a VDMSeq \<Rightarrow> \<bool>"
where
  "inv_SeqElems einv s \<equiv> list_all einv s"

lemma l_inv_SeqElems_alt: "inv_SeqElems einv s = inv_SeqElems0 einv s"  
by (simp add: elems_def inv_SeqElems0_def inv_SeqElems_def list_all_iff)

lemma l_inv_SeqElems_Cons: "(inv_SeqElems f (a#s)) = (f a \<and> (inv_SeqElems f s))"
unfolding inv_SeqElems_def elems_def by auto

lemma l_inv_SeqElems_append: "(inv_SeqElems f (xs @ [x])) = (f x \<and> (inv_SeqElems f xs))"
unfolding inv_SeqElems_def elems_def by auto

definition
  applyList :: "'a list \<Rightarrow> \<nat> \<Rightarrow> 'a option" 
where
 "applyList l n \<equiv> (if (n > 0 \<and> int n \<le> len l) then 
                      Some(l ! (n - (1::nat))) 
                   else 
                      None)"
 
definition
  applyVDMSeq :: "'a VDMSeq \<Rightarrow> \<int> \<Rightarrow> 'a" (infixl "$" 100)
where
 "applyVDMSeq l n \<equiv> (if (n > 0 \<and> n \<le> len l) then 
                      (l ! nat (n - 1)) 
                   else 
                      undefined)"

lemma applyVDM_len1: "applyVDMSeq s (len s + 1) = undefined"
unfolding applyVDMSeq_def len_def
apply simp
done

(* this goal is too specific; they are useful in specific situations *)
lemma applyVDM1: "(x # xs) $ 1 = x" 
by (simp add: applyVDMSeq_def len_def)

lemma applyVDM2: "(x # xs) $ 2 = xs $ 1" 
by (simp add: applyVDMSeq_def len_def)

(* generalise previous failure for a better matching goal: trade $ for ! *)
lemma applyVDM1_gen[simp]: "s \<noteq> [] \<Longrightarrow> s $ 1 = s ! 0"
apply (induct s)
apply (simp_all add: applyVDMSeq_def len_def)
done

(* combine repeated uses *)
lemmas applyVDMSeq_defs =  len_def applyVDMSeq_def

lemma applyVDM_cons_gt1empty: "i > 1 \<Longrightarrow> (x # []) $ i = undefined"
by (simp add: applyVDMSeq_defs)

lemma applyVDM_cons_gt1: "len xs > 0 \<Longrightarrow> i > 1 \<Longrightarrow> (x # xs) $ i = xs $ (i - 1)"
apply (simp add: applyVDMSeq_defs) (* again too complex; try avoiding the trade $ for ! again *)
apply (intro impI)
find_theorems name:induct name:List
apply (induct xs rule: length_induct)
apply simp_all
by (smt nat_1 nat_diff_distrib)

lemma applyVDM_zero[simp]: "applyVDMSeq s 0 = undefined"
unfolding applyVDMSeq_def len_def
apply simp
done

lemmas VDMSeq_def = elems_def inds_def len_def applyVDMSeq_def

lemma l_len_nat1: "s \<noteq> [] \<Longrightarrow> 0 < len s"
unfolding len_def by simp

lemma l_applyVDMSeq_defined: "s \<noteq> [] \<Longrightarrow> inv_SeqElems (\<lambda> x . x \<noteq> undefined) s \<Longrightarrow> applyVDMSeq s (len s) \<noteq> undefined"
unfolding applyVDMSeq_def  len_def
apply (simp add: l_len_nat1)
apply (cases "nat (int (length s) - 1)")
apply simp_all
apply (cases s)
apply simp_all
(*thm ssubst[OF l_inv_SeqElems_alt]
apply (subst ssubst[OF l_inv_SeqElems_alt])*)
apply (simp_all add: l_inv_SeqElems_alt)
unfolding inv_SeqElems0_def elems_def
apply (erule ballE)
apply simp_all
by simp

lemma l_applyVDMSeq_append_last: 
  "applyVDMSeq (ms @ [m]) (len (ms @ [m])) = m"
unfolding applyVDMSeq_def len_def
by (simp add: l_len_append)

lemma l_applyVDMSeq_cons_last: 
  "applyVDMSeq (m # ms) (len (m # ms)) = (if ms = [] then m else applyVDMSeq ms (len ms))"
apply (simp)
unfolding applyVDMSeq_def len_def
by (simp add: nat_diff_distrib')

(*****************************************************************)      
section {* Maps *}
  
(*type_synonym ('a, 'b) "VDMMap" = "'a \<rightharpoonup> 'b" (infixr "\<rightharpoonup>" 0)*)
  
definition
  inv_Map :: "('a \<Rightarrow> \<bool>) \<Rightarrow> ('b \<Rightarrow> \<bool>) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow>\<bool>"
where
  "inv_Map inv_Dom inv_Rng m \<equiv> 
      inv_SetElems inv_Dom (dom m) \<and> 
      inv_SetElems inv_Rng (ran m)"

(*****************************************************************)  
section {* Some useful examples *}
  
(* { expr | var . filter }, { var \<in> type . filter }, { var . filter } *)
value "{ x+x | x . x \<in> {(1::nat),2,3} }"
value "{ x+x | x . x \<in> {(1::nat),2,3} }"
(*value "{ x+x | x . x \<in> {(1::nat)..3} }" --"not always work"*)
  

value "{ [A,B,C,D,E,F] ! i | i . i \<in> {0,2,4} }"
(* { s(i) | i in set inds s & i mod 2 = 0 } *)

  (* List application (i.e. s(x)) is available in Isabelle *)

value "[A, B, C] ! 0"
value "[A, B, C] ! 1"
value "[A, B, C] ! 2"
value "[A, B, C] ! 3"
value "nth [A, B, C] 0"

(* List comprehension *)
value "{ [A,B,C] ! i | i . i \<in> {0,1,2} }"
value "[ x . x \<leftarrow> [0,1,(2::int)] ]" (*avoid if possible... *)
value "[ x . x \<leftarrow> [0 .. 3] ]"

value "len [A, B, C]"
value "elems [A, B, C, A, B]"
value "elems [(0::nat), 1, 2]"
value "inds [A,B,C]"
value "inds_as_nat [A,B,C]"
value "card (elems [10, 20, 30, 1, 2, 3, 4, (5::nat), 10])"
value "len [10, 20, 30, 1, 2, 3, 4, (5::nat), 10]"
  
value "applyList [A, B] 0" --"out of range"
value "applyList [A, B] 1"
value "applyList [A, B] 2"
value "applyList [A, B] 3" --"out of range"

value "applyVDMSeq [a] (len [a])"
value "applyVDMSeq [A, B] 0" --"out of range"
value "[A,B]$1"
value "applyVDMSeq [A, B] 1"
value "applyVDMSeq [A, B] 2"
value "applyVDMSeq [A, B] 3" --"out of range"

(* MySeq = seq of nat1
   inv s == len s \<le> 9 and card(elem s) = len s and (forall i in set elems s . i \<le> 9)*)
type_synonym MySeq = "VDMNat1 list"
definition
   inv_MySeq :: "MySeq \<Rightarrow> \<bool>"
where
   "inv_MySeq s \<equiv> (inv_SeqElems inv_VDMNat1 s) \<and> 
                  len s \<le> 9 \<and> int (card (elems s)) = len s \<and>
                  (\<forall> i \<in> elems s . i > 0 \<and> i \<le> 9)"

value "inv_MySeq [1, 2, 3]"

  text {* VDM maps auxiliary functions *}

(*
type_synonym ('a,'b) "map" = "'a \<Rightarrow> 'b option" (infixr "~=>" 0)
*)

(* dom exists already *)
thm dom_def
find_theorems "dom _"

(* map values are given as *)
value "[ (0::nat) \<mapsto> 7, 1  \<mapsto> 5 ]"

value "[ (0::nat) \<mapsto> (0::nat), 1  \<mapsto> 5 ] 0"

value "the ([ (0::nat) \<mapsto> (0::nat), 1  \<mapsto> 5 ] 4)"

value "the (Some b)"
value "the None"

value "empty(A \<mapsto> 0)"
value "empty(A := Some 0)"
value "[A \<mapsto> 0]"
value "[A \<mapsto> 0, B \<mapsto> 1]"
  
lemma "dom [ A \<mapsto> 0, B \<mapsto> 1] = LOOK_HERE" apply simp oops
lemma "ran [ A \<mapsto> (0::nat), B \<mapsto> 1] = {0,1}" apply simp oops

end