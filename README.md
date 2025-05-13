# exam_proofs

This is a repository about deriving the potential function for amortised analysis of catenable lists (w.r.t. cons, snoc, tail) from purely functional datastructures page 154. The book uses the banker's method but the exam question wanted the physicist's method. 

See DebitList.lean for the implementation of cons snoc and tail. 
See Main.lean for stress testing the operations to ensure that DebitList shape implies Debits at each node. If so we can define the potential function by computing these debits. 