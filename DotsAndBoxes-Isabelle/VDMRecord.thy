theory VDMRecord
imports VDMToolKit
begin

(* record definition: careful with field names as they become selector functions

  ex: xcoord :: nat \<Rightarrow> Coord
      ycoord :: nat \<Rightarrow> Coord

   notice that if you name fields carelessly, you end up with confusing selector function names
 *)
record Coord =
  xcoord :: VDMNat
  ycoord :: VDMNat

(* record value; brackets are '(' + '|' and '|' + ')' *)
value "\<lparr>xcoord = 10, ycoord = 20\<rparr>" 
(* record enumeration and update *)
value "\<lparr>xcoord = 10, ycoord = 20\<rparr>\<lparr>ycoord := 30\<rparr>"

(* various properties on records, useful ones: 

  given a c :: Coord = \<lparr> xcoord = 10, ycoord = 20 \<rparr>, x, y :: VDMNat

  selector  : xcoord c = 10, ycoord c = 20
  selector  : xcoord \<lparr> xcoord = x, ycoord = y \<rparr> = x
  surjective: c = \<lparr> xcoord = xcoord c, ycoord c \<rparr>
  update    : c \<lparr> xcoord := x \<rparr> = \<lparr> xcoord = x, ycoord = ycoord c \<rparr> 
*)
print_theorems

(* record extension *)
datatype MType = V | H
record DCoord = Coord +
  direction :: MType

value "\<lparr>xcoord = 1, ycoord = 2, direction = H\<rparr>"

(* record constant *)
definition
  test_d1 :: Coord
where
  "test_d1 \<equiv> \<lparr>xcoord = 10, ycoord = 20\<rparr>"

(* record field selection *)
definition
  test_d1_x :: VDMNat
where
  "test_d1_x \<equiv> (xcoord test_d1)"

(* record invariant *)
definition
  inv_Grid :: "VDMNat \<Rightarrow> \<bool>"
where
  "inv_Grid d \<equiv> inv_VDMNat d \<and> d \<le> 3" 
definition
  inv_Coord :: "Coord \<Rightarrow> \<bool>"
where
  "inv_Coord c \<equiv> inv_Grid (xcoord c) \<and> inv_Grid (ycoord c) \<and> (xcoord c) \<le> (ycoord c)"

find_theorems (100) name:Coord -name:DCoord

end