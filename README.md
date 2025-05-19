# exam_proofs

This is a repository about deriving the potential function for amortised analysis of catenable lists (w.r.t. cons, snoc, tail) from purely functional datastructures page 154. The book uses the banker's method but the exam question wanted the physicist's method. 

See CatenableList.lean for the implementation of cons snoc, tail, and potential function. 
The CatenableList.lean file also has a stress test to check that potential function inequality holds for tail, actual cost of tail <= amortised cost - (potential (tail tree) - potential tree).

To run the stress test, clone this repository and inside the root folder run `lake exe exam_proofs`. 