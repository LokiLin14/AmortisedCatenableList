import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- ## Part 1. Defining the problem

inductive CatenableList' (A : Type _) where
  | ccons : A -> List (CatenableList' A) -> CatenableList' A
deriving Repr, Hashable, BEq

inductive CatenableList (A : Type _) where
  | nil : CatenableList A
  | catList : CatenableList' A -> CatenableList A
deriving Repr, Hashable, BEq

namespace CatenableList
open CatenableList'

def snoc (cl : CatenableList A) (x : A) : CatenableList A :=
  match cl with
  | nil => catList (ccons x [])
  | catList (ccons a cls) => catList (ccons a (cls ++ [ccons x []]))

def cons (x : A) (cl : CatenableList A) : CatenableList A :=
  match cl with
  | nil => catList (ccons x [])
  | catList cl' => catList (ccons x [cl'])

def append (cl cl' : CatenableList A) : CatenableList A :=
  match (cl, cl') with
  | (nil, _) => cl'
  | (_, nil) => cl
  | (catList (ccons a ncls), catList ncl') => catList (ccons a (ncls ++ [ncl']))

def tail {A : Type _} (cl : CatenableList A) : CatenableList A :=
  match cl with
  | nil => nil
  | catList (ccons _ ncls) => ncls.map catList |> List.foldr append nil

-- greedy algorithm that calculates n - maximum debits
def potential (cl :  CatenableList A) : Nat :=
  match cl with
  | nil => 0
  | catList ncl => go 0 ncl
    where
      go (acc : Nat) (ncl : CatenableList' A) : Nat :=
        let (ccons _ ncls) := ncl;
        let contrib := if acc >= 0 then min acc ncls.length else 0;
          (ncls.foldl go (acc + 2 - contrib)) - 1

def tailCost : CatenableList A -> Nat
  | nil => 0
  | catList (ccons _ ncls) => ncls.length

-- Checking potential function is valid by applying a random sequence of operations
inductive AmortisationOp where
  | consOp : AmortisationOp
  | snocOp : AmortisationOp
  | tailOp : AmortisationOp
deriving Repr
open AmortisationOp

def stressPotential (numOperations : Nat) (seed : Nat := 0) : IO Unit := do
  let maxAmortisedCost := 3
  let mut clist : CatenableList Nat := nil
  let mut rng := mkStdGen seed
  for iteration in [1:numOperations] do
    let (opNum, rng') := stdNext rng
    rng := rng'
    let op := match opNum % 3 with
      | 0 => consOp
      | 1 => snocOp
      | _ => tailOp
    let (clist', opCost) := match op with
      | consOp => (cons 0 clist, 1)
      | snocOp => (snoc clist 0, 1)
      | tailOp => (tail clist,
        match clist with
        | nil => 1
        | catList (.ccons _ ncls) => ncls.length)
    if !(opCost <= maxAmortisedCost - ((potential clist' : Int) - (potential clist : Int))) then
      println! s!"Amortisation failed when applying {repr op}!!! :/"
      println! s!"Equation does not hold: ({opCost} <= {maxAmortisedCost} - ({potential clist'} - {potential clist}))"
      println! s!"clist: {repr clist}"
      println! s!"clist': {repr clist'}"
      return
    if !(potential clist' >= 0) then
      println! s!"Amortisation failed!!! :/"
      println! s!"Potential function is negative: {potential clist'}"
      println! s!"clist': {repr clist'}"
      return
    if (iteration % (numOperations / 100)) == 0 then
      println! s!"Finished {iteration} / {numOperations}"
    clist := clist'
  println! s!"Stress failed to break amortisation :)"

end CatenableList

-- ## Part 2. Beginning of proofs

-- ### Part 2.2 Defining DebitList to mirror CatenableList

structure DebitList' where
  ccons :: (debits : Nat) (childs : List DebitList')

def DebitList'.distanceFromBound (acc : Nat) (dl : DebitList') : Nat :=
  let (DebitList'.ccons debits children) := dl
  children.foldl distanceFromBound (acc - dl.debits + 2) - 1

mutual
inductive ListValidDebitList' : (acc : Nat) -> (dl : List DebitList') -> Type where
  | nil {n : Nat} : ListValidDebitList' n []
  | cons {acc : Nat} {dl : DebitList'} {dls : List DebitList'} :
      ValidDebitList' acc dl ->
      (ListValidDebitList' (DebitList'.distanceFromBound acc dl) dls) ->
      ListValidDebitList' acc (dl :: dls)

inductive ValidDebitList' : (acc : Nat) → (dl : DebitList') → Type where
  | proofs {acc : Nat} {dl : DebitList'}
    (debitsLeAcc : dl.debits ≤ acc)
    (debitsLeChildren : dl.debits ≤ dl.childs.length)
    (validChilds : ListValidDebitList' (acc - dl.debits + 2) dl.childs) :
    ValidDebitList' acc dl
end

inductive DebitList where
  | nil : DebitList
  | debitList : (dl : DebitList') -> ValidDebitList' 0 dl -> DebitList

def DebitList.sizeSubDebits : (dl : DebitList) -> Nat
  | .nil => 0
  | .debitList dl _ => dl.distanceFromBound 0

def DebitList.tailCost : DebitList -> Nat
  | .nil => 0
  | .debitList (.ccons _ dls) _ => dls.length

-- ### Part 2.3 Defining ShapeEquals and some lemmas about them

mutual
inductive ListShapeEquals' {A : Type _} : List (CatenableList' A) -> List DebitList' -> Type _ where
  | nil : ListShapeEquals' [] []
  | cons : (c : CatenableList' A) -> (d : DebitList') ->
          (crest : List (CatenableList' A)) -> (drest : List DebitList') ->
          ShapeEquals' c d ->
          ListShapeEquals' crest drest ->
          ListShapeEquals' (c :: crest) (d :: drest)

inductive ShapeEquals' {A : Type _} : CatenableList' A -> DebitList' -> Type _ where
    | ccons : (a : A) -> (cls : List (CatenableList' A)) -> (n : Nat) -> (dls : List DebitList') ->
        ListShapeEquals' cls dls ->
        ShapeEquals' (CatenableList'.ccons a cls) (DebitList'.ccons n dls)
end

inductive ShapeEquals {A : Type _} : CatenableList A → DebitList → Type _ where
  | nil : ShapeEquals CatenableList.nil DebitList.nil
  | succ : {cl : CatenableList' A} -> {dl : DebitList'} -> {p : ValidDebitList' 0 dl} ->
      ShapeEquals' cl dl ->
      ShapeEquals (CatenableList.catList cl) (DebitList.debitList dl p)

theorem listShapeEqualsImpLenEquals (p : ListShapeEquals' cls dls) : cls.length = dls.length := by
  refine ListShapeEquals'.rec
    (motive_1 := fun cls dls _ => cls.length = dls.length)
    (motive_2 := fun c d _ => True)
    ?_
    ?_
    ?_
    p
  · simp
  . simp
  . simp

theorem shapeEqualsImpTailCostEq {A : Type _} {cl : CatenableList A} {dl : DebitList}
    (p : ShapeEquals cl dl): cl.tailCost = dl.tailCost := by
  cases' p with cl dl _ p
  · simp [CatenableList.tailCost, DebitList.tailCost]
  · cases cl
    cases dl
    cases p
    rename_i p
    simp [CatenableList.tailCost, DebitList.tailCost]
    exact listShapeEqualsImpLenEquals p

-- ### Part 2.4 Lemmas about the CatenableList potential function in relation to DebitList potential function
-- in particular this section shows that the CatenablieList potential function is the minimum of the
-- DebitList potential function given that the CatenableList ShapeEquals the DebitList

-- TODO rename the is increasing lemmas to follow mathlib naming convention
-- some equational lemmas about the CatenableList potential function to make reasoning with them easier
namespace CatenableList

mutual
theorem potentialGoIsIncreasing (acc : Nat) (cl : CatenableList' A) :
    acc + 1 ≤ potential.go acc cl := by
  cases' cl with _ cls
  simp [potential.go]
  have ineq0 : (acc + 2 - min acc cls.length) + cls.length - 1
      ≤ List.foldl potential.go (acc + 2 - min acc cls.length) cls - 1 := by
    apply Nat.sub_le_sub_right
    exact lengthLeFoldlPotentialGo _ _
  apply le_trans ?_ ineq0
  omega

theorem lengthLeFoldlPotentialGo (acc : Nat) (cls : List (CatenableList' A)) :
    acc + cls.length ≤ List.foldl potential.go acc cls := by
  cases' cls with h t
  · simp
  simp
  ring_nf
  apply le_trans ?_ (lengthLeFoldlPotentialGo _ _)
  rewrite [Nat.add_le_add_iff_right]
  rewrite [Nat.add_comm]
  exact potentialGoIsIncreasing _ _
end

mutual
theorem potentialGoIsMonotonic {A : Type _} {a b : Nat} (p : a ≤ b) (cl : CatenableList' A) :
    potential.go a cl ≤ potential.go b cl := by
  cases' cl with _ cls
  simp [potential.go]
  cases' cls with cl' cls
  · simp [p]
  · simp
    rewrite [Nat.sub_add_cancel ?_]
    rotate_left -- prove the inequality to cancel out the a -1 + 1
    · apply le_trans ?_ (lengthLeFoldlPotentialGo _ _)
      apply le_add_right
      apply le_trans ?_ (potentialGoIsIncreasing _ cl')
      omega
    apply foldlPotentialGoIsMonotonic
    apply potentialGoIsMonotonic
    omega

theorem foldlPotentialGoIsMonotonic {A : Type _} {a b : Nat} (p : a ≤ b) (ncls : List (CatenableList' A)):
    List.foldl potential.go a ncls ≤ List.foldl potential.go b ncls := by
  cases ncls with
  | nil => simp [p]
  | cons h t =>
    simp
    apply foldlPotentialGoIsMonotonic
    apply potentialGoIsMonotonic
    assumption
end

end CatenableList

-- some equational lemmas about the DebitList potential function to make reasoning with them easier
namespace DebitList

mutual
theorem accAddOneSubDebitsIsIncreasing {dl : DebitList'} {acc : Nat} (p : ValidDebitList' acc dl) :
    acc + 1 ≤ dl.distanceFromBound acc := by
  cases' dl with debits dls
  cases' p with _ _ debitsLeAcc debitsLeLength validChilds
  simp at debitsLeLength
  simp at debitsLeAcc
  simp at validChilds
  simp [DebitList'.distanceFromBound]
  have ineq0 := Nat.sub_le_sub_right (accAddLengthLeFoldlSizeSubDebits validChilds) 1
  apply Nat.le_trans ?_ ineq0
  omega

theorem accAddLengthLeFoldlSizeSubDebits {dls : List DebitList'} {acc : Nat} (p : ListValidDebitList' acc dls) :
    acc + dls.length ≤ List.foldl DebitList'.distanceFromBound acc dls := by
  cases' p with _ _ dl dls vdl vdls
  · simp
  cases' dl with debits dlChilds
  simp
  apply Nat.le_trans ?_ (accAddLengthLeFoldlSizeSubDebits vdls)
  have h := accAddOneSubDebitsIsIncreasing vdl
  apply Nat.le_trans ?_ (Nat.add_le_add_iff_right.mpr h)
  omega
end

-- TODO prove that distanceFromBound is monotonic too like potentialGo

end DebitList

mutual
theorem potentialGoLeDistanceFromBound (eq : ShapeEquals' cl dl) (vdl : ValidDebitList' acc dl) :
  CatenableList.potential.go acc cl ≤ DebitList'.distanceFromBound acc dl := by
  cases' eq with _ ncls debits ndls eq

  simp [CatenableList.potential.go, DebitList'.distanceFromBound]

  have debitLeMin : debits ≤ min acc ncls.length := by
    cases' vdl with a b debitsLeAcc debitsLeLength e _
    simp only [le_inf_iff]
    constructor
    · simp at debitsLeAcc
      exact debitsLeAcc
    · rw [listShapeEqualsImpLenEquals eq]
      simp at debitsLeLength
      exact debitsLeLength
  have potentialDecLeDebitDec : (acc + 2 - min acc ncls.length) ≤ (acc - debits + 2) := by
    omega
  apply Nat.le_trans (CatenableList.foldlPotentialGoIsMonotonic potentialDecLeDebitDec ncls)

  cases' vdl with _ _ debitsLeAcc debitsLeLength vdls
  simp at debitsLeAcc; simp at debitsLeLength;
  rewrite [Nat.sub_add_cancel (m := 1) ?_]
  rotate_left
  · have h := DebitList.accAddLengthLeFoldlSizeSubDebits vdls
    simp at h
    omega

  exact foldlPotentialGoLeFoldlDistanceFromBound eq vdls

theorem foldlPotentialGoLeFoldlDistanceFromBound (eq : ListShapeEquals' cls dls) (vdls : ListValidDebitList' acc dls) :
  cls.foldl CatenableList.potential.go acc ≤ dls.foldl DebitList'.distanceFromBound acc := by
  cases' eq with cl dl cls dls eq eqs
  · simp
  cases' vdls with _ _ _ _ vdl vdls
  simp
  have h :=  foldlPotentialGoLeFoldlDistanceFromBound eqs vdls
  apply Nat.le_trans ?_ h
  apply CatenableList.foldlPotentialGoIsMonotonic
  exact potentialGoLeDistanceFromBound eq vdl
end

theorem potentialLeSizeSubDebits (p : ShapeEquals cl dl) :
  CatenableList.potential cl <= DebitList.sizeSubDebits dl := by
  cases' p with cl dl vp p
  · simp [CatenableList.potential, DebitList.sizeSubDebits]
  simp [CatenableList.potential, DebitList.sizeSubDebits]
  exact potentialGoLeDistanceFromBound p vp

mutual
def List.minListDebitList' {A : Type _} (acc : Nat) (cls : List (CatenableList' A)) :
    Σ dls : List DebitList', ListValidDebitList' acc dls × ListShapeEquals' cls dls :=
  match cls with
  | .nil =>
    Sigma.mk [] (ListValidDebitList'.nil, ListShapeEquals'.nil)
  | .cons cl cls =>
    let (Sigma.mk dl (pf0, pf1)) := cl.minDebitList' acc
    let (Sigma.mk dls (pf2, pf3)) := cls.minListDebitList' (dl.distanceFromBound acc)
    let pf4 := by
      refine ListValidDebitList'.cons ?_ ?_
      · assumption
      · assumption
    let pf5 := by
      apply ListShapeEquals'.cons
      · assumption
      · assumption
    Sigma.mk (dl :: dls) (pf4, pf5)

def CatenableList'.minDebitList' {A : Type _} (acc : Nat) (cl : CatenableList' A) :
    Σ dl : DebitList', ValidDebitList' acc dl × ShapeEquals' cl dl :=
  let (.ccons _ cls) := cl
  let contrib := min acc cls.length
  match h : cls.minListDebitList' (acc - contrib + 2) with
  | (Sigma.mk dls (vdls, shapeEquality)) =>
  let dl := DebitList'.ccons contrib dls
  let vdl := by
    refine ValidDebitList'.proofs ?_ ?_ vdls
    · simp [dl, contrib]
    · simp [dl, contrib]
      have h' := listShapeEqualsImpLenEquals shapeEquality
      simp [h']
  let shapeEquality := by
    simp [dl]
    exact ShapeEquals'.ccons _ _ _ _ shapeEquality
  Sigma.mk dl (vdl, shapeEquality)
end

def CatenableList.minDebitList {A : Type _} (cl : CatenableList A) : Σ dl : DebitList, ShapeEquals cl dl :=
  match cl with
  | .nil => Sigma.mk (DebitList.nil) ShapeEquals.nil
  | .catList cl' =>
    let (Sigma.mk dl (validity, shapeEquality)) := cl'.minDebitList' 0
    Sigma.mk (.debitList dl validity) (ShapeEquals.succ shapeEquality)

mutual
theorem List.foldlMinDistanceFromBoundEqFoldlPotentialGo (cls : List (CatenableList' A)) (acc : Nat) :
  (List.minListDebitList' acc cls).1.foldl DebitList'.distanceFromBound acc = cls.foldl CatenableList.potential.go acc := by
  cases' cls with cl cls
  · simp [List.minListDebitList']
  · simp [List.minListDebitList']
    rw [CatenableList'.minDistanceFromBoundEqPotentialGo]
    apply List.foldlMinDistanceFromBoundEqFoldlPotentialGo cls _

theorem CatenableList'.minDistanceFromBoundEqPotentialGo (cl : CatenableList' A) (acc : Nat) :
  (cl.minDebitList' acc).1.distanceFromBound acc = CatenableList.potential.go acc cl := by
  cases' cl with _ cls
  simp [CatenableList'.minDebitList', DebitList'.distanceFromBound, CatenableList.potential.go]
  congr
  have h : acc - min acc cls.length + 2 = acc + 2 - min acc cls.length := by
    omega
  rewrite [h]
  apply List.foldlMinDistanceFromBoundEqFoldlPotentialGo cls _
end

theorem CatenableList.minEqPotential (cl : CatenableList A) :
  cl.minDebitList.1.sizeSubDebits = cl.potential := by
  cases cl
  · simp [minDebitList, DebitList.sizeSubDebits, potential]
  · simp [DebitList.sizeSubDebits, minDebitList, potential]
    apply CatenableList'.minDistanceFromBoundEqPotentialGo

-- ### Part 2.5 Lemmas about the CatenableList tail function in relation to the DebitList tail function

def DebitList'.append (dl dl' : DebitList') : DebitList' :=
  match dl with
  | .ccons debits dls => .ccons (debits + 1)  (dls ++ [dl'])

def ValidDebitList'.snoc {acc : Nat} {dls : List DebitList'} {dl : DebitList'}
                        (vdls : ListValidDebitList' acc dls)
                        (vdl : ValidDebitList' (dls.foldl DebitList'.distanceFromBound acc) dl) :
                        ListValidDebitList' acc (dls ++ [dl]) := by
  cases' vdls with _ _ dl' dls vdl' vdls
  · simp
    simp at vdl
    apply ListValidDebitList'.cons
    · assumption
    · exact ListValidDebitList'.nil
  · simp
    apply ListValidDebitList'.cons
    · assumption
    · apply ValidDebitList'.snoc
      · assumption
      · assumption

def ValidDebitList'.append {acc : Nat} {dl dl' : DebitList'} (vdl : ValidDebitList' acc dl)
  (vdl' : ValidDebitList' (dl.distanceFromBound acc + 1) dl') :
    ValidDebitList' (acc + 1) (dl.append dl') := by
  cases' dl with debits dls
  cases' vdl with _ _ debitsLeAcc debitsLeChildren validChildren
  simp [DebitList'.append]
  apply ValidDebitList'.proofs <;> simp
  · assumption
  · assumption
  · simp at validChildren
    apply ValidDebitList'.snoc
    · assumption
    · simp [DebitList'.distanceFromBound] at vdl'
      rewrite [Nat.sub_add_cancel (m := 1)] at vdl'
      rotate_left
      · calc
          1 ≤ _ := by
            simp at debitsLeAcc
            simp_all only [le_add_iff_nonneg_left, zero_le]
          (acc - debits + 2) ≤ _ := by
            simp
          (acc - debits + 2) + dls.length ≤ _ := by
            exact DebitList.accAddLengthLeFoldlSizeSubDebits validChildren
      assumption

-- A foldr that runs on non-empty lists, useful so that the DebitList version of append only needs to
-- concern itself with appending two non-empty DebitLists
@[simp]
def List.foldr' {A : Type _} (h : A) (ls : List A) (f : A -> A -> A) : A :=
  match ls with
  | .nil => h
  | .cons x' ls => f h (ls.foldr' x' f)

mutual
def ListValidDebitList'.incAcc {dls : List DebitList'} {acc acc' : Nat}
    (p : acc ≤ acc') (vdls : ListValidDebitList' acc dls) :
    ListValidDebitList' acc' dls := by
  match vdls with
  | .nil =>
    exact ListValidDebitList'.nil
  | .cons vdl vdls =>
    · apply ListValidDebitList'.cons
      · apply ValidDebitList'.incAcc (acc := acc) (acc' := acc')
        · exact p
        · assumption
      ·
        sorry

def ValidDebitList'.incAcc {dl : DebitList'} {acc acc' : Nat} (p : acc ≤ acc') (vdl : ValidDebitList' acc dl) :
    ValidDebitList' acc' dl := by
  match vdl with
  | .proofs leAcc leChildren validChilds =>

  cases' vdl with _ _ leAcc leChildren otherProofs
  apply ValidDebitList'.proofs
  · apply Nat.le_trans ?_ p
    assumption
  · exact leChildren
  · apply ListValidDebitList'.incAcc ?_ validChilds
    omega
end

-- TODO rename this to something more reasonable / following naming conventions
def foldlListValidDebitLists {dl0 : DebitList'} {dls : List DebitList'} {n : Nat}
                            (vdls : ListValidDebitList' n (dl0 :: dls)) :
    ValidDebitList' (n + 1) (dls.foldr' dl0 DebitList'.append) := by
  -- Proof based on recursively simplifying the foldr' away
  match dls with -- cases on dls so foldr' can decide what to do
  | .nil =>
    -- non recursive case where append is not applied so we manually construct a ValidDebitList'
    simp
    cases' vdls with _ _ _ _ vdl0 _
    have p : (n ≤ n + 1) := by
      simp_all only [le_add_iff_nonneg_right, zero_le]
    apply ValidDebitList'.incAcc p
    assumption
  | .cons dl1 dls => -- recursive case where append is applied
    match vdls with
    | .cons vdl0 vdls =>
    simp
    apply ValidDebitList'.append
    · assumption
    · apply foldlListValidDebitLists
      assumption

def DebitList'.dischargeDebits (dl : DebitList') (n : Nat) : DebitList' :=
  sorry

def ValidDebitListAccImpValidDebitListPredAcc {dl : DebitList'} {acc n : Nat}
    (vdl : ValidDebitList' (acc + n) dl) :
    ValidDebitList' acc (dl.dischargeDebits n) := by

  sorry

def DebitList.tail (dl : DebitList) : DebitList :=
  match dl with
  | nil => nil -- shortcircuit empty list case
  | .debitList dl' vdl =>

  let (.ccons debits dls) := dl'
  match dls with
  | .nil => DebitList.nil -- shortcircuit becomes empty list case
  | .cons hdl dls =>
  -- handle case where the resulting list is not empty
  -- create a almost correct DebitList' that has the same shape as CatenableList.tail
  let dl' := dls.foldr' (A := DebitList') hdl DebitList'.append
  -- prove that dl' is almost valid
  let pf0 : ValidDebitList' 3 dl' := by
    match vdl with
    | .proofs leAcc leChildren vChildren =>
    simp at leAcc leChildren vChildren
    exact foldlListValidDebitLists vChildren
  -- create the final debitlist
  let dl'' := dl'.dischargeDebits 3
  -- show that it is valid DebitList by having dischargeDebits lower ValidDebitList' 3 to ValidDebitList' 0
  let pf1 := by
    apply ValidDebitListAccImpValidDebitListPredAcc
    exact pf0
  DebitList.debitList dl'' pf1

def tailPreservesShape (cl : CatenableList A) (dl : DebitList) :
  ShapeEquals cl dl -> ShapeEquals cl.tail dl.tail := by
  sorry

theorem tailDebitsAddCostLeDebits (dl : DebitList) :
  dl.tail.sizeSubDebits  + DebitList.tailCost dl - 3 ≤ dl.sizeSubDebits :=
  sorry

-- ### Part 2.5 Proof of tail's amortized constant time

theorem CatenableList.tailIsConstantTime {A : Type _} : ∃ k : Nat, ∀ cl : CatenableList A,
  tailCost cl ≤ k - ((potential (tail cl) : Int) - (potential cl : Int)) := by
  exists 3
  intros cl
  match h : cl.minDebitList with
  | (Sigma.mk dl se') => ?_
  simp at se'
  let dl' := DebitList.tail dl
  have se : ShapeEquals (tail cl) dl' := by
    apply tailPreservesShape
    exact se'
  have ineq0 : potential (tail cl) ≤ DebitList.sizeSubDebits dl' := by
    exact potentialLeSizeSubDebits se
  have ineq1 : DebitList.sizeSubDebits dl' + DebitList.tailCost dl - 3 ≤ DebitList.sizeSubDebits dl := by
    unfold dl'
    exact tailDebitsAddCostLeDebits dl
  have eq0 : DebitList.sizeSubDebits dl = potential cl := by
    have h' : dl = cl.minDebitList.1 := by
      simp [h]
    simp [h']
    exact cl.minEqPotential
  have eq1 : cl.tailCost = dl.tailCost := by
    exact shapeEqualsImpTailCostEq se'
  omega
