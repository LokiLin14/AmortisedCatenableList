import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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

def tail (cl : CatenableList A) : CatenableList A :=
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
        | catList (ccons _ ncls) => ncls.length)
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

structure DebitList' where
  ccons :: (debits : Nat) (childs : List DebitList')

namespace DebitList'

def distanceFromBound (acc : Nat) (dl : DebitList') : Nat :=
  let (DebitList'.ccons debits children) := dl
  children.foldl distanceFromBound (acc - dl.debits + 2) - 1

end DebitList'

def List.inits' : (l : List α) -> List (List α × α)
  | List.nil => []
  | List.cons a as => ([], a) :: (inits' as).map (fun (as', a') => (a :: as', a'))
-- #eval List.inits' [1, 2, 3] -- [([], 1), ([1], 2), ([1, 2], 3)]

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

mutual
  inductive ListShapeEquals' : List (CatenableList' A) -> List DebitList' -> Prop where
    | nil : ListShapeEquals' [] []
    | cons : (c : CatenableList' A) -> (d : DebitList') ->
            (crest : List (CatenableList' A)) -> (drest : List DebitList') ->
            ShapeEquals' c d ->
            ListShapeEquals' crest drest ->
            ListShapeEquals' (c :: crest) (d :: drest)

  inductive ShapeEquals' : CatenableList' A -> DebitList' -> Prop where
    | ccons : (a : A) -> (cls : List (CatenableList' A)) -> (n : Nat) -> (dls : List DebitList') ->
        ListShapeEquals' cls dls ->
        ShapeEquals' (CatenableList'.ccons a cls) (DebitList'.ccons n dls)
end

inductive ShapeEquals : CatenableList A → DebitList → Prop where
  | nil : ShapeEquals CatenableList.nil DebitList.nil
  | succ : (cl : CatenableList' A) -> (dl : DebitList') -> (p : ValidDebitList' 0 dl) ->
      ShapeEquals' cl dl ->
      ShapeEquals (CatenableList.catList cl) (DebitList.debitList dl p)

namespace DebitList
open DebitList'

def sizeSubDebits : (dl : DebitList) -> Nat
  | nil => 0
  | debitList dl _ => distanceFromBound 0 dl

mutual
theorem accAddOneSubDebitsIsIncreasing {dl : DebitList'} {acc : Nat} (p : ValidDebitList' acc dl) :
    acc + 1 ≤ distanceFromBound acc dl := by
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
    acc + dls.length ≤ List.foldl distanceFromBound acc dls := by
  cases' p with _ _ dl dls vdl vdls
  · simp
  cases' dl with debits dlChilds
  simp
  apply Nat.le_trans ?_ (accAddLengthLeFoldlSizeSubDebits vdls)
  have h := accAddOneSubDebitsIsIncreasing vdl
  apply Nat.le_trans ?_ (Nat.add_le_add_iff_right.mpr h)
  omega
end

def tail (dl : DebitList) : DebitList :=
  sorry

theorem tailPreservesShape (cl : CatenableList A) (dl : DebitList) :
  ShapeEquals cl dl -> ShapeEquals (CatenableList.tail cl) (tail dl) := by
  sorry

def tailCost : DebitList -> Nat
  | nil => 0
  | debitList (ccons _ dls) _ => dls.length

theorem tailDebitsAddCostLeDebits (dl : DebitList) :
  sizeSubDebits (tail dl) + DebitList.tailCost dl - 3 ≤ sizeSubDebits dl :=
  sorry

def minDebitList (cl : CatenableList A) : DebitList :=
  sorry

theorem minPreservesShape (cl : CatenableList A) :
  ShapeEquals cl (minDebitList cl) := by
  sorry

theorem minEqPotential (cl : CatenableList A) :
  sizeSubDebits (minDebitList cl) = CatenableList.potential cl := by
  sorry

end DebitList

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

theorem shapeEqualsImpTailCostEq (p : ShapeEquals cl dl): cl.tailCost = dl.tailCost := by
  cases' p with cl dl _ p
  · simp [CatenableList.tailCost, DebitList.tailCost]
  · cases cl
    cases dl
    cases p
    rename_i p
    simp [CatenableList.tailCost, DebitList.tailCost]
    exact listShapeEqualsImpLenEquals p

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

namespace CatenableList

theorem tailIsConstantTime : ∃ k : Nat, ∀ cl : CatenableList A,
  tailCost cl ≤ k - ((potential (tail cl) : Int) - (potential cl : Int)) := by
  exists 3
  intros cl
  let dl := DebitList.minDebitList cl
  let dl' := DebitList.tail dl
  have se : ShapeEquals (tail cl) dl' := by
    apply DebitList.tailPreservesShape
    exact DebitList.minPreservesShape _
  have ineq0 : potential (tail cl) ≤ DebitList.sizeSubDebits dl' := by
    exact potentialLeSizeSubDebits se
  have ineq1 : DebitList.sizeSubDebits dl' + DebitList.tailCost dl - 3 ≤ DebitList.sizeSubDebits dl := by
    unfold dl'
    exact DebitList.tailDebitsAddCostLeDebits dl
  have eq0 : DebitList.sizeSubDebits dl = potential cl := by
    exact DebitList.minEqPotential _
  have eq1 : cl.tailCost = dl.tailCost := by
    exact shapeEqualsImpTailCostEq (DebitList.minPreservesShape _)
  omega
end CatenableList
