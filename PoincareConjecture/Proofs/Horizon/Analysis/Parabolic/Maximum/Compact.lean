import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.CompactMaximum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.ScalarTrace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlowAnalysis

theorem compact_min_velocity_nonnegative
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {T K : ℝ} (hT : 0 < T) (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set M)))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc 0 T) t)
    (hmin : ∀ t ∈ Ioc 0 T, ∀ x : M,
      (∀ y : M, f t x ≤ f t y) → f t x ≤ 0 → -K * f t x ≤ v t x)
    (hinit : ∀ x : M, 0 ≤ f 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ f t x := by
  have hcont : ContinuousOn (fun p : M × ℝ ↦ -f p.2 p.1)
      (univ ×ˢ Icc 0 T) :=
    hf.neg.comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hp.2, hp.1⟩)
  have h := Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max
    (F := fun x t ↦ -f t x) (F' := fun x t ↦ -v t x) (K := -K) hcont
    (fun x t ht ↦ (hderiv t ⟨ht.1.le, ht.2⟩ x).neg)
    (fun x t ht hneg hspace ↦ by
      have hv := hmin t ht x (fun y ↦ neg_le_neg_iff.mp (hspace y)) (by linarith)
      linarith)
    (fun x ↦ neg_nonpos.mpr (hinit x))
  exact fun t ht x ↦ neg_nonpos.mp (h x t ht)

theorem ricciFlow_supersolution_nonnegative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] {T K : ℝ} (hT : 0 < T) (F : RicciFlow n M (Icc 0 T))
    (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set M)))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc 0 T) t)
    (hinit : ∀ x : M, 0 ≤ f 0 x)
    (hsmooth : ∀ t ∈ Icc 0 T, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t))
    (hevol : ∀ t ∈ Ioc 0 T, ∀ x : M,
      (F.connection t).laplacian (f t) x - K * f t x ≤ v t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ f t x := by
  apply compact_min_velocity_nonnegative (K := K) hT f v hf hderiv _ hinit
  intro t ht x hmin _hneg
  have hlocal : IsLocalMin (f t) x := Filter.Eventually.of_forall hmin
  have hlap := (F.connection t).laplacian_nonneg_of_isLocalMinAt
    ((hsmooth t ⟨ht.1.le, ht.2⟩).contMDiffAt) hlocal
  have := hevol t ht x
  linarith

end PoincareConjecture.RicciFlowAnalysis
