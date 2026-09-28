import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GraphWalkPaths
import Mathlib.Topology.Subpath










set_option autoImplicit false

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}



def concatSequence (p : Fin (n + 1) → V)
    (w : (i : Fin n) → G.Walk (p i.castSucc) (p i.succ)) :
    G.Walk (p 0) (p (Fin.last n)) :=
  Fin.dfoldl n (fun i => G.Walk (p 0) (p i)) (fun i ih => ih.append (w i)) .nil



theorem concatSequence_zero (p : Fin 1 → V)
    (w : (i : Fin 0) → G.Walk (p i.castSucc) (p i.succ)) :
    concatSequence p w = .nil := by
  rw [concatSequence, Fin.dfoldl_zero]



theorem concatSequence_succ (p : Fin (n + 2) → V)
    (w : (i : Fin (n + 1)) → G.Walk (p i.castSucc) (p i.succ)) :
    concatSequence p w =
      (concatSequence (p ∘ Fin.castSucc) (fun i => w i.castSucc)).append (w (Fin.last n)) := by
  rw [concatSequence, Fin.dfoldl_succ_last]
  rfl




theorem realizePath_concatSequence {X : Type*} [TopologicalSpace X]
    (a : V → X) (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))
    (p : Fin (n + 1) → V)
    (w : (i : Fin n) → G.Walk (p i.castSucc) (p i.succ)) :
    Path.Homotopic.Quotient.mk (realizePath a edge (concatSequence p w)) =
      Path.Homotopic.Quotient.mk
        (_root_.Path.concat (a ∘ p) (fun i => realizePath a edge (w i))) := by
  induction n with
  | zero => rw [concatSequence_zero, Path.concat_zero]; rfl
  | succ n ih =>
    erw [concatSequence_succ,
      realizePath_append a edge
        (concatSequence (p ∘ Fin.castSucc) (fun i => w i.castSucc)) (w (Fin.last n)),
      Path.concat_succ,
      Path.Homotopic.Quotient.mk_trans, ih]
    rfl

end SimpleGraph.Walk
