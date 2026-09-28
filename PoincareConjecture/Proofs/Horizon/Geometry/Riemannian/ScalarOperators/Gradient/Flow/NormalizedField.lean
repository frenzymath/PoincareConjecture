import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.ManifoldExpansion







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareConjecture.LeviCivitaData
theorem contMDiffOn_normalizedGradient_of_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l : ℝ} (hl : 0 < l) (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y)) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (D.normalizedGradient f)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro y hy
  have hgr := D.contMDiffAt_gradient (hf.contMDiffAt (hU.mem_nhds hy))
  have hpair : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun z => g.inner z (D.gradient f z) (D.gradient f z)) y := hgr.inner_bundle hgr
  have hnonzero : g.inner y (D.gradient f y) (D.gradient f y) ≠ 0 := by
    change ⟪D.gradient f y, D.gradient f y⟫_ℝ ≠ 0
    rw [real_inner_self_eq_norm_sq]
    have hpos : 0 < ‖D.gradient f y‖ := hl.trans_le (hgrad y hy)
    exact pow_ne_zero 2 hpos.ne'
  exact (((contDiffAt_inv ℝ hnonzero).contMDiffAt.comp y hpair).smul_section hgr).contMDiffWithinAt

theorem normalizedGradient_cross_le_of_pairing
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f h : M → ℝ) (y : M) {l c : ℝ} (hl : 0 < l) (hc : 0 < c)
    (hgrad : l ≤ g.tangentNorm y (D.gradient h y))
    (hunit : g.tangentNorm y (D.gradient h y) ≤ 1)
    (hpair : g.inner y (D.gradient f y) (D.gradient h y) ≤ -c) :
    mvfderiv (𝓡 n) f y (D.normalizedGradient h y) ≤ -c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm : 0 < ‖D.gradient h y‖ := hl.trans_le hgrad
  have hnorm' : ‖D.gradient h y‖ ≤ 1 := hunit
  have hq : g.inner y (D.gradient h y) (D.gradient h y) = ‖D.gradient h y‖ ^ 2 := by
    change ⟪D.gradient h y, D.gradient h y⟫_ℝ = _
    exact real_inner_self_eq_norm_sq _
  rw [normalizedGradient, map_smul, smul_eq_mul, ← D.inner_gradient, hq,
    mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ (sq_pos_of_pos hnorm)).mpr
  have hqle : ‖D.gradient h y‖ ^ 2 ≤ 1 := by nlinarith
  nlinarith
end PoincareConjecture.LeviCivitaData
