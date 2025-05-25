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
def potential (cl :  CatenableList A) : Int :=
  match cl with
  | nil => 0
  | catList ncl => go 0 ncl
    where
      go (acc : Int) (ncl : CatenableList' A) : Int :=
        let (ccons _ ncls) := ncl;
        let contrib := if acc >= 0 then min acc ncls.length else 0;
          (ncls.foldl go (acc + 2 - contrib)) - 1

def tailCost : CatenableList A -> Nat
  | nil => 0
  | catList (ccons _ ncls) => ncls.length

theorem tailIsConstantTime : ∃ k : Nat, ∀ cl : CatenableList A,
  tailCost cl ≤ k - (potential (tail cl) - potential cl) := by
  exists 3
  sorry

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
    if !(opCost <= maxAmortisedCost - (potential clist' - potential clist)) then
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

def DebitList'.distanceFromIndex (acc : Nat) (dl : DebitList') : Nat :=
  let (DebitList'.ccons debits children) := dl
  children.foldl distanceFromIndex (acc - dl.debits + 2) - 1

def List.inits' : (l : List α) -> List (List α × α)
  | List.nil => []
  | List.cons a as => ([], a) :: (inits' as).map (fun (as', a') => (a :: as', a'))
-- #eval List.inits' [1, 2, 3] -- [([], 1), ([1], 2), ([1, 2], 3)]

inductive ValidDebitList' : (acc : Nat) → (dl : DebitList') → Type where
  | proofs {acc : Nat} {dl : DebitList'}
    (debitsLeAcc : (dl.debits ≤ acc))
    (validChilds : ∀ p ∈ (List.inits' dl.childs),
      ValidDebitList' (p.fst.foldl DebitList'.distanceFromIndex (acc - dl.debits + 2)) p.snd) :
    ValidDebitList' acc dl

inductive DebitList where
  | nil : DebitList
  | debitList : (dl : DebitList') -> ValidDebitList' 0 dl -> DebitList
