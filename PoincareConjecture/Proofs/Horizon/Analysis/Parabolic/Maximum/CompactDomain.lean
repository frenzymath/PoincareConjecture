import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Maximum.Compact

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

theorem compact_subset_min_velocity_nonnegative
    {M : Type u} [TopologicalSpace M] {C : Set M} (hC : IsCompact C)
    {T K : ℝ} (hT : 0 < T) (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ C))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x ∈ C,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc 0 T) t)
    (hmin : ∀ t ∈ Ioc 0 T, ∀ x ∈ C,
      (∀ y ∈ C, f t x ≤ f t y) → f t x < 0 → -K * f t x ≤ v t x)
    (hinit : ∀ x ∈ C, 0 ≤ f 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ C, 0 ≤ f t x := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hmap : Continuous (fun p : C × ℝ ↦ (p.2, (p.1 : M))) := by fun_prop
  have hcont : ContinuousOn (fun p : C × ℝ ↦ -f p.2 p.1)
      (univ ×ˢ Icc 0 T) :=
    hf.neg.comp hmap.continuousOn (fun p hp ↦ ⟨hp.2, p.1.2⟩)
  have h := Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max
    (F := fun x : C ↦ fun t ↦ -f t x) (F' := fun x : C ↦ fun t ↦ -v t x)
    (K := -K) hcont
    (fun x t ht ↦ (hderiv t ⟨ht.1.le, ht.2⟩ x x.2).neg)
    (fun x t ht hneg hspace ↦ by
      have hv := hmin t ht x x.2
        (fun y hy ↦ neg_le_neg_iff.mp (hspace ⟨y, hy⟩)) (by linarith)
      linarith)
    (fun x ↦ neg_nonpos.mpr (hinit x x.2))
  exact fun t ht x hx ↦ neg_nonpos.mp (h ⟨x, hx⟩ t ht)

theorem ricciFlow_compactDomain_supersolution_nonnegative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {T K : ℝ} (hT : 0 < T) (F : RicciFlow n M (Icc 0 T))
    {U C : Set M} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ C))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x ∈ C,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc 0 T) t)
    (hinit : ∀ x ∈ C, 0 ≤ f 0 x)
    (hsmooth : ∀ t ∈ Icc 0 T, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t) U)
    (hboundary : ∀ t ∈ Icc 0 T, ∀ x ∈ C \ interior C, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioc 0 T, ∀ x ∈ interior C,
      (F.connection t).laplacian (f t) x - K * f t x ≤ v t x) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ C, 0 ≤ f t x := by
  apply compact_subset_min_velocity_nonnegative hC (K := K) hT f v hf hderiv _ hinit
  intro t ht x hx hmin hneg
  have hxint : x ∈ interior C := by
    by_contra hn
    exact (not_lt_of_ge (hboundary t ⟨ht.1.le, ht.2⟩ x ⟨hx, hn⟩)) hneg
  have hlocal : IsLocalMin (f t) x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hxint] with y hy
    exact hmin y hy
  have hlap := (F.connection t).laplacian_nonneg_of_isLocalMinAt
    ((hsmooth t ⟨ht.1.le, ht.2⟩).contMDiffAt (hU.mem_nhds (hCU hx))) hlocal
  have hv := hevol t ht x hxint
  linarith

end PoincareConjecture.RicciFlowAnalysis
