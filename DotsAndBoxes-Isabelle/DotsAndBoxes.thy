theory Habbouly160503144
imports VDMToolkit VDMSet VDMRecord

begin

text {*  NAME   STD-NO *}


(*=========================================================================================*)
section {* Introduction *}


text {* Write here your design decisions as text.

        It is a good idea to structure your Isabelle model per VDM construct 
        in (sub)sections. We add section snipets for you below.

        Key features of Isabelle syntax needed in the definitions are given as 
        comments. 
      *}

(*=========================================================================================*)
section {* VDM values *}

text {* Write here values you might have declared in Overture. Remember that in Isabelle
        you must declare before you can use! VDM values can be given as Isabelle @{term abbreviation}.
      *}

(* In VDM it would look like: 
        SIZE : nat = 3;

   In Isabelle:
        abbreviation name :: "TYPE" where "name \<equiv> EXPR"

--{* abbreviation name :: "TYPE" where "name \<equiv> EXPR" *}
*)


abbreviation 
    SIZE :: "VDMNat1"
where
    "SIZE \<equiv> 4"

abbreviation 
    BOXN :: "VDMNat1"
where
    "BOXN \<equiv> 2*SIZE + 1"

abbreviation 
    DOTN :: "VDMNat1"
where
    "DOTN \<equiv> SIZE * SIZE"


(*=========================================================================================*)
section {* VDM types and their invariants *}

text {* VDM enumerations can be Isabelle data type. For example *}

(*--{* datatype name :: name = VALUE1 | VALUEN *}*)
(*datatype Player = NOUGHT | CROSS*)

print_theorems  (*--"curiosity: Player type has loads of useful facts in Isabelle!"*)

text {* VDM types like pairs can be constructed with @{term type_synonym}. 
        VDM type invariants are functions from the type to boolean. Remember 
        that you need to define and check type invariants manually in Isabelle!

        As in VDM, you can write pattern matching (let) expressions to simplify models.
        For example, we use a let expression below in the invariant definition for type Pos. 
      *}

(*  In VDM it would look like:
  
      Pos = nat * nat
      inv mk_(x,y) == x <= SIZE and y <= SIZE

      inv_Pos : nat * nat -> bool
      inv_Pos(x,y) == x <= SIZE and y <= SIZE
*)

(*{* type_synonym name = "TYPE_EXPR" *}*)
type_synonym Dot = VDMNat1

(*{* definition name :: "TYPE1 \<Rightarrow> TYPN \<Rightarrow> RES_TYPE" where "name \<equiv> DEF" *}*)
definition 
  inv_Dot :: "VDMNat1 \<Rightarrow> bool"
where
  "inv_Dot dot \<equiv>  inv_VDMNat1 dot  \<and> dot \<le> SIZE"


record Move = 
  dot1field:: Dot
  dot2field:: Dot
print_theorems 

definition 
  inv_Move :: "Move \<Rightarrow> bool"
  where
  "inv_Move m \<equiv> (let x=(dot1field m); s=(dot2field m) in 
                    inv_Dot x \<and>
                    inv_Dot s \<and>
                    x < s \<and>
                    s \<le> DOTN \<and>
                    (if x mod SIZE = 0 then
                    s = x+1 
                    else
                    s = x+SIZE \<or> s = x+1 ))" 


record Player = 
  boxesfield:: "VDMNat VDMSet" 
  movelistfield:: "Move VDMSet"
print_theorems

record Box =
  nofield:: VDMNat1
  movesfield:: "Move VDMSet"

definition 
  inv_Box :: "Box \<Rightarrow> bool"
  where 
  "inv_Box b \<equiv> (let x=(nofield b); y=(movesfield b) in 
                   inv_VDMNat1 x \<and>     
                  inv_VDMSet y\<and>
                  vdm_card  y < 4)"


type_synonym Boxs = "Box VDMSet"

definition 
  inv_Boxs :: "Boxs \<Rightarrow> bool"
  where 
  "inv_Boxs b \<equiv> vdm_card b \<le> BOXN"

datatype result = P1HASWON | P2HASWON | DRAW

abbreviation 
    p1 :: "Player"
    where 
    "p1 \<equiv> \<lparr> boxesfield = {} , movelistfield = {}\<rparr>"

abbreviation 
    p2 :: "Player"
    where 
    "p2 \<equiv> \<lparr> boxesfield = {} , movelistfield = {}\<rparr>"

abbreviation 
    q :: "VDMNat1 VDMSet"
    where 
    "q \<equiv> {1 .. (DOTN-SIZE)}"

abbreviation 
    BoxList :: "Boxs"
    where 
    "BoxList \<equiv> { \<lparr>nofield = s , movesfield = { \<lparr>dot1field = s, dot2field = s+1\<rparr>,
                                               \<lparr>dot1field = s, dot2field = s+SIZE\<rparr>,
                                               \<lparr>dot1field = s+1, dot2field = s+1+SIZE\<rparr>,
                                               \<lparr>dot1field = s+SIZE, dot2field = s+1+SIZE\<rparr>}\<rparr> 
                                               | s . s \<in> q \<and> s mod SIZE \<noteq> 0}"



(*=========================================================================================*)
section {* VDM functions *}

text {* VDM functions can be described using Isabelle @{term definition} 
        (e.g. predicates, or basic functions) or @{term fun} (e.g. recursive definitions). 
     *}

(*-----------------------------------------------------------------------------------------*)
subsection {* Explicitly defined functions *}

text {* Encode here your explicitly defined VDM functions. Remember that you need to define
        and check type invariants, as well as VDM pre/post conditions manually in Isabelle!

        For every VDM function, you need to define three entities: function itself, and
        its pre and post conditions. 

        Precondition definitions go from function parameters to bool, whereas
        postcondition definitions go from function parameters and result to bool.
      *}
(* In VDM these look like:
        myFun: nat * nat -> nat
        myFun(t1,t2) == t1 + t2
          pre t1 > 0 and t2 > 0
          post RESULT >= t1+t2;

        pre_myFun: nat * nat -> bool
        pre_myFun(t1,t2) == t1 > 0 and t2 > 0
        
        post_myFun: nat * nat * nat -> bool
        post_myFun(t1,t2,RESULT) == RESULT >= t1+t2

    Pre/Pos are optional in VDM explicit functions.
*)

definition 
  removeFromBoxes :: " Move \<Rightarrow> Boxs \<Rightarrow> Boxs "
  where
  "removeFromBoxes m b \<equiv> {\<lparr>nofield = nofield x , movesfield = movesfield x\<rparr> 
                                        | x . x \<in> b \<and> movesfield x \<noteq> {m}} "

definition 
  pre_removeFromBoxes :: " Move \<Rightarrow> Boxs \<Rightarrow> bool "
  where 
  "pre_removeFromBoxes m b \<equiv> b \<noteq> {}"


print_theorems

definition 
  chooseMove :: " Move \<Rightarrow> Player \<Rightarrow> Boxs \<Rightarrow> Player "
  where 
  "chooseMove m p b \<equiv> if \<exists> x .(x \<in> b \<and> movesfield x = {m} )then 
                               \<lparr>boxesfield = boxesfield p \<union> {nofield x |x . x \<in> b \<and> movesfield  x = {m}} 
                                                                   ,movelistfield = movelistfield p\<rparr> 
                      else 
                               \<lparr>boxesfield = boxesfield p,movelistfield = movelistfield p \<union> {m}\<rparr>"


definition 
  pre_chooseMove :: " Move \<Rightarrow> Player \<Rightarrow> Boxs \<Rightarrow> bool "
  where
  "pre_chooseMove m p b \<equiv> \<exists> x . (x \<in> b \<and> m \<in> movesfield x)"


definition 
  post_chooseMove :: " Move \<Rightarrow> Player \<Rightarrow> Boxs \<Rightarrow> bool "
  where 
  "post_chooseMove m p b \<equiv> \<exists> x . ( x \<in> movelistfield p \<and> x = m)"

definition 
  switchPlayers :: "bool \<Rightarrow> bool"
  where
  "switchPlayers p1plays \<equiv> if p1plays then False else True"


definition 
  isTurnPl1 :: "Move \<Rightarrow> Boxs \<Rightarrow> bool \<Rightarrow> bool"
  where
  "isTurnPl1 m b bo \<equiv> if \<exists> x . (x \<in> b \<and> movesfield x = {m}) then bo 
                      else switchPlayers(bo)" 

definition 
  isTurnPl1_pre :: "Move \<Rightarrow> Boxs \<Rightarrow> bool \<Rightarrow> bool"
  where
  "isTurnPl1_pre m b bo \<equiv> \<exists> x . (x \<in> b \<and> m \<in> movesfield x)"

definition 
  tally :: "Player \<Rightarrow> Player \<Rightarrow> result"
  where
  "tally pl1 pl2 \<equiv> if vdm_card (movelistfield pl1) > vdm_card (movelistfield pl2 )then 
                       P1HASWON 
                    else 
                    (if vdm_card (movelistfield pl1) < vdm_card (movelistfield pl2) then 
                        P2HASWON
                        else 
                        DRAW)"

definition 
  tally_pre :: "Player \<Rightarrow> Player \<Rightarrow> bool" 
  where
  "tally_pre pl1 pl2 \<equiv> pl1 \<noteq> pl2"
(*
definition
  myFun :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "myFun t1 t2 \<equiv> t1 + t2"

print_theorems (*--"what Isabelle knows about @{term myFun}?"*)

definition
  pre_myFun :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "pre_myFun t1 t2 \<equiv> t1 > 0 \<and> t2 > 0"

definition 
  post_myFun :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "post_myFun t1 t2 RESULT \<equiv> RESULT \<ge> t1+t2"
*)

(*-----------------------------------------------------------------------------------------*)
subsection {* Implicitly defined functions *}

text {* Encode here your implicitly defined VDM functions. Remember that you need to check
        type invariants, as well as VDM pre/post conditions manually in Isabelle!
      *}
(* In VDM these look like:
        myFun(T1 * T2) r: T3
          [pre PRED]
          post PRED;

   Pre is optional; Post is mandatory in VDM implicit functions 
*)

(*=========================================================================================*)
section {* VDM state *}

record DBGame =
  P1field :: Player
  P2field :: Player
  p1playsfield :: bool
  BoxListfield :: Boxs

definition 
  inv_DBGame_flat :: "Player \<Rightarrow> Player \<Rightarrow> bool \<Rightarrow> Boxs \<Rightarrow> bool"
  where
  "inv_DBGame_flat pl1 pl2 pl1pl b \<equiv> \<forall> x .( x \<in> movelistfield pl1 \<and>
                                     (\<forall> i .(i \<in> movelistfield pl2 \<and>
                                     i \<noteq> x \<and> 
                                     (\<forall> y .(y \<in> b  \<and> 
                                     (\<forall> z . (z \<in> movesfield y \<and>
                                     z \<noteq> i \<and> z \<noteq> x  )))))))"


definition 
  inv_DBGame :: "DBGame \<Rightarrow> bool "
  where
  "inv_DBGame state \<equiv> inv_DBGame_flat (P1field state) 
                                      (P2field state) 
                                      (p1playsfield state) 
                                      (BoxListfield state)"

definition 
  init_DBGame :: "DBGame"
  where
  "init_DBGame \<equiv> \<lparr> P1field = p1, P2field = p2, p1playsfield = True , BoxListfield = BoxList\<rparr>"

definition 
  post_init_DBGame :: "bool"
  where
  "post_init_DBGame \<equiv> inv_DBGame (init_DBGame)"

(*=========================================================================================*)
section {* VDM operations (over the state) *}



definition 
  pre_play_move :: "Move \<Rightarrow> DBGame \<Rightarrow> bool"
  where
  "pre_play_move m DB \<equiv> \<exists> x . (x \<in> BoxListfield DB \<and> m \<in> movesfield x)"

definition 
  post_play_move :: "Move \<Rightarrow> DBGame \<Rightarrow> DBGame \<Rightarrow> bool"
  where
  "post_play_move m preDB postDB \<equiv> \<forall> x . (x \<in> BoxListfield postDB \<and> 
                                (\<forall> y . (y \<in> movesfield x \<and> m \<noteq> y \<and>
                                 BoxListfield postDB \<noteq> BoxListfield preDB \<and>
                                 (P1field preDB \<noteq> P1field postDB \<or> 
                                  P2field preDB \<noteq> P2field postDB))))"

definition 
  play_move :: "Move \<Rightarrow> DBGame \<Rightarrow> DBGame"
  where 
  "play_move m DB \<equiv> if p1playsfield DB then 
                       \<lparr>P1field = chooseMove(m)(P1field DB)(BoxListfield DB),
                       P2field = P2field DB,
                       p1playsfield = isTurnPl1 (m)(BoxListfield DB)(p1playsfield DB) ,
                       BoxListfield = removeFromBoxes(m)(BoxListfield DB)\<rparr>
                     else 
                      \<lparr>P1field = P1field DB,
                       P2field =chooseMove(m)(P2field DB)(BoxListfield DB),
                       p1playsfield = isTurnPl1 (m)(BoxListfield DB)(p1playsfield DB) ,
                       BoxListfield = removeFromBoxes(m)(BoxListfield DB)\<rparr>"           
(*=========================================================================================*)
section {* VDM proof obligations *}

text {* If you use Overture, generate proof obligation text and write it using Isabelle.
        You can name your goals with the same name as the Overture PO for my reference.
      *}
(*-----------------------------------------------------------------------------------------*)
subsection {* Well formedness (if any) *}

(*{* lemma goal_name : "predicate" proof_script *}*)
lemma myFun_subtype: "P = NP" 
oops

(*-----------------------------------------------------------------------------------------*)
subsection {* Satisfiability (of each VDM operation) *}

lemma myFun_satisfiability: "P = NP"
oops

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
subsubsection {* Operation1 .. N *}

lemma "P = NP"
oops

(*-----------------------------------------------------------------------------------------*)
subsection {* Sanity checks *}

lemma "P = NP"
oops

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
subsubsection {* Single winner or draw *}

lemma "P = NP"
oops

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
subsubsection {* Moves within board maximum size *}

lemma "P = NP"
oops

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
subsubsection {* Moves fairness (i.e. one player move per round) *}

lemma "P = NP"
oops

end
