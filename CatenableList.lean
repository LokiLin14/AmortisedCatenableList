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

inductive ValidDebitList' : (acc : Nat) → (dl : DebitList') → Type where
  | proofs {acc : Nat} {dl : DebitList'}
    (debitsLeAcc : (dl.debits ≤ acc))
    (validChilds : ∀ p ∈ (List.inits' dl.childs),
      ValidDebitList' (p.fst.foldl distanceFromBound (acc - dl.debits + 2)) p.snd) :
    ValidDebitList' acc dl

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

def tail (dl : DebitList) : DebitList :=
  sorry

theorem tailPreservesShape (cl : CatenableList A) (dl : DebitList) :
  ShapeEquals cl dl -> ShapeEquals (CatenableList.tail cl) (tail dl) := by
  sorry

def tailCost : DebitList -> Nat
  | nil => 0
  | debitList (ccons _ dls) _ => dls.length

theorem tailDecreasesSizeSubDebitsByCost (dl : DebitList) :
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

theorem shapeEqualsImpTailCostEq (p : ShapeEquals cl dl): cl.tailCost = dl.tailCost := by
  sorry

theorem potentialLeSizeSubDebits (cl : CatenableList A) (dl : DebitList) (p : ShapeEquals cl dl) :
  CatenableList.potential cl <= DebitList.sizeSubDebits dl := by
  sorry

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
    exact potentialLeSizeSubDebits _ _ se
  have ineq1 : DebitList.sizeSubDebits dl' + DebitList.tailCost dl - 3 ≤ DebitList.sizeSubDebits dl := by
    unfold dl'
    exact DebitList.tailDecreasesSizeSubDebitsByCost dl
  have eq0 : DebitList.sizeSubDebits dl = potential cl := by
    exact DebitList.minEqPotential _
  have eq1 : cl.tailCost = dl.tailCost := by
    exact shapeEqualsImpTailCostEq (DebitList.minPreservesShape _)
  omega
end CatenableList
