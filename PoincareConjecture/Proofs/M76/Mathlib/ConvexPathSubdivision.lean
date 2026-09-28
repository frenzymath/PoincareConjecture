import PoincareConjecture.Proofs.M76.Mathlib.ConvexSubtypePaths
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

open Set Metric
open scoped unitInterval

namespace Path

theorem exists_convex_subpath_partition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {a b : U} (p : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 2) → unitInterval) (s : Fin (n + 1) → Set E),
      t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧ Monotone t ∧
      ∀ i, Convex ℝ (s i) ∧ s i ⊆ U ∧
        ∀ u, (p.subpath (t i.castSucc) (t i.succ) u : E) ∈ s i := by
  classical
  choose r hr hrU using fun u : unitInterval =>
    Metric.isOpen_iff.mp hU (p u : E) (p u).property
  let C : unitInterval → Set unitInterval :=
    fun u => (fun v => (p v : E)) ⁻¹' ball (p u : E) (r u)
  have hCo (u : unitInterval) : IsOpen (C u) :=
    isOpen_ball.preimage (continuous_subtype_val.comp p.continuous)
  have hCc : univ ⊆ ⋃ u, C u := by
    intro u _
    exact mem_iUnion.mpr ⟨u, mem_ball_self (hr u)⟩
  obtain ⟨T, hT0, hTm, ⟨n, hTn⟩, hTC⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hCo hCc
  choose j hj using hTC
  let t : Fin (n + 2) → unitInterval := fun i => T i.val
  let s : Fin (n + 1) → Set E := fun i => ball (p (j i.val) : E) (r (j i.val))
  refine ⟨n, t, s, hT0, hTn (n + 1) (by omega), ?_, ?_⟩
  · intro i k hik
    exact hTm hik
  · intro i
    refine ⟨convex_ball _ _, hrU (j i.val), ?_⟩
    intro u
    change (p (Icc.convexComb (T i.val) (T (i.val + 1)) u) : E) ∈ s i
    apply hj i.val
    rw [← uIcc_of_le (hTm (Nat.le_succ i.val)), ← Path.range_subpathAux]
    exact mem_range_self u

end Path
