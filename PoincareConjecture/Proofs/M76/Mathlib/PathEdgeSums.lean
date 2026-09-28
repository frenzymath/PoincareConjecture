import PoincareConjecture.Proofs.M76.Mathlib.CyclicEdgeSums
import Mathlib.Data.Fin.Rev












set_option autoImplicit false

open scoped BigOperators

namespace Fin

variable {E G : Type*} [AddCommGroup G] {m n k : ℕ}




def pathEdgeSum (w : E → E → G) (u : Fin (n + 1) → E) : G :=
  ∑ i : Fin n, w (u i.castSucc) (u i.succ)




theorem pathEdgeSum_reverse (w : E → E → G)
    (hw : ∀ a b, w b a = -w a b) (u : Fin (n + 1) → E) :
    pathEdgeSum w (fun i => u i.rev) = -pathEdgeSum w u := by
  unfold pathEdgeSum
  calc
    (∑ i : Fin n, w (u i.castSucc.rev) (u i.succ.rev)) =
        ∑ i : Fin n, -w (u i.rev.castSucc) (u i.rev.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rev_castSucc, rev_succ]
      exact hw _ _
    _ = -(∑ i : Fin n, w (u i.rev.castSucc) (u i.rev.succ)) :=
      Finset.sum_neg_distrib _
    _ = -(∑ i : Fin n, w (u i.castSucc) (u i.succ)) :=
      congrArg Neg.neg (Equiv.sum_comp revPerm
        (fun i : Fin n => w (u i.castSucc) (u i.succ)))





theorem cyclicEdgeSum_init_append (w : E → E → G)
    (u : Fin (m + 2) → E) (v : Fin (n + 2) → E)
    (huv : u (last (m + 1)) = v 0)
    (hvu : v (last (n + 1)) = u 0) :
    cyclicEdgeSum w (append (init u) (init v)) =
      pathEdgeSum w u + pathEdgeSum w v := by
  rw [cyclicEdgeSum_append]
  have hu : snoc (init u) (init v 0) = u := by
    change snoc (init u) (v 0) = u
    rw [← huv, snoc_init_self]
  have hv : snoc (init v) (init u 0) = v := by
    change snoc (init v) (u 0) = v
    rw [← hvu, snoc_init_self]
  rw [hu, hv]
  rfl






theorem cyclicEdgeSum_three_paths (w : E → E → G)
    (hw : ∀ a b, w b a = -w a b)
    (u : Fin (m + 2) → E) (v : Fin (n + 2) → E) (p : Fin (k + 2) → E)
    (huv : u (last (m + 1)) = v 0)
    (hvu : v (last (n + 1)) = u 0)
    (hpu : p 0 = u 0) (hpv : p (last (k + 1)) = v 0) :
    cyclicEdgeSum w (append (init u) (init v)) =
      cyclicEdgeSum w (append (init u) (init (fun i => p i.rev))) +
        cyclicEdgeSum w (append (init p) (init v)) := by
  have huP : u (last (m + 1)) = (fun i : Fin (k + 2) => p i.rev) 0 := by
    simpa only [rev_zero] using huv.trans hpv.symm
  have hPu : (fun i => p i.rev) (last (k + 1)) = u 0 := by
    simpa only [rev_last] using hpu
  rw [cyclicEdgeSum_init_append w u v huv hvu,
    cyclicEdgeSum_init_append w u (fun i => p i.rev) huP hPu,
    cyclicEdgeSum_init_append w p v hpv (hvu.trans hpu.symm),
    pathEdgeSum_reverse w hw p]
  simp only [add_assoc, neg_add_cancel_left]

end Fin
