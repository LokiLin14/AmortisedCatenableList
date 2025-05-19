inductive CatenableList' where
  | ccons : List CatenableList' -> CatenableList'
deriving Repr, Hashable, BEq

inductive CatenableList where
  | nil : CatenableList
  | catList : CatenableList' -> CatenableList
deriving Repr, Hashable, BEq

namespace CatenableList
open CatenableList'

def snoc : CatenableList -> CatenableList
  | nil => catList (ccons [])
  | catList (ccons cls) => catList (ccons (cls ++ [ccons []]))

def cons : CatenableList -> CatenableList
  | nil => catList (ccons [])
  | catList cl' => catList (ccons [cl'])

def append (cl cl' : CatenableList) : CatenableList :=
  match (cl, cl') with
  | (nil, _) => cl'
  | (_, nil) => cl
  | (catList (ccons ncls), catList ncl') => catList (ccons (ncls ++ [ncl']))

def tail : CatenableList -> CatenableList
  | nil => nil
  | catList (ccons ncls) => ncls.map catList |> List.foldr append nil

def potential : CatenableList -> Int
  | nil => 0
  | catList ncl => go 0 ncl
    where
      go (acc : Int) (ncl : CatenableList') : Int :=
        let (ccons ncls) := ncl;
        let contrib := if acc >= 0 then min acc ncls.length else 0;
          (ncls.foldl go (acc + 2 - contrib)) - 1

inductive AmortisationOp where
  | consOp : AmortisationOp
  | snocOp : AmortisationOp
  | tailOp : AmortisationOp
deriving Repr
open AmortisationOp

theorem potentialStartsAtZero : potential nil = 0 := by
  rfl

def stressPotential (numOperations : Nat) (seed : Nat := 0) : IO Unit := do
  let maxAmortisedCost := 3
  let mut clist := nil
  let mut rng := mkStdGen seed
  for iteration in [1:numOperations] do
    let (opNum, rng') := stdNext rng
    rng := rng'
    let op := match opNum % 3 with
      | 0 => consOp
      | 1 => snocOp
      | _ => tailOp
    let (clist', opCost) := match op with
      | consOp => (cons clist, 1)
      | snocOp => (snoc clist, 1)
      | tailOp => (tail clist,
        match clist with
        | nil => 1
        | catList (ccons ncls) => ncls.length)
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
