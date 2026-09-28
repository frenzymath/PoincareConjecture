import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison
import Mathlib.Topology.Order.Compact








set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

theorem pathELength_comp_le_of_tangentNorm_le_on_Icc
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {f : M → N} {γ : ℝ → M} {a b C : ℝ} (hC : 0 ≤ C)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ)
    (hf : ∀ u ∈ Icc a b, ContMDiffAt (𝓡 n) (𝓡 n) 1 f (γ u))
    (hbound : ∀ u ∈ Icc a b, ∀ v : TangentSpace (𝓡 n) (γ u),
      h.tangentNorm (f (γ u)) (mfderiv (𝓡 n) (𝓡 n) f (γ u) v) ≤
        C * g.tangentNorm (γ u) v) :
    h.pathELength (f ∘ γ) a b ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  rw [pathELength_eq_lintegral_tangentNorm, pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro u hu
  rw [mfderiv_comp_apply u ((hf u hu).mdifferentiableAt one_ne_zero)
    (hγ.mdifferentiable one_ne_zero u)]
  exact (ENNReal.ofReal_le_ofReal (hbound u hu _)).trans_eq (ENNReal.ofReal_mul hC)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture



theorem exists_first_exit_of_continuous
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X} (hγ : Continuous γ)
    {U : Set X} (hU : IsOpen U) (h0 : γ 0 ∈ U) (h1 : γ 1 ∉ U) :
    ∃ c ∈ Ioc (0 : ℝ) 1, γ c ∈ frontier U ∧ MapsTo γ (Icc 0 c) (closure U) := by
  let A := Icc (0 : ℝ) 1 ∩ γ ⁻¹' Uᶜ
  have hA : IsCompact A := isCompact_Icc.inter_right (hU.isClosed_compl.preimage hγ)
  obtain ⟨c, hc, hleast⟩ := hA.exists_isLeast ⟨1, ⟨by norm_num, h1⟩⟩
  have hcpos : 0 < c := lt_of_le_of_ne hc.1.1 (by
    intro heq
    exact hc.2 (heq ▸ h0))
  have hbefore : MapsTo γ (Ico 0 c) U := by
    intro t ht
    by_contra h
    exact (not_le_of_gt ht.2) (hleast ⟨⟨ht.1, ht.2.le.trans hc.1.2⟩, h⟩)
  have hclosed : MapsTo γ (Icc 0 c) (closure U) := by
    have hh := hbefore.closure_of_continuousOn hγ.continuousOn
    simpa only [closure_Ico hcpos.ne] using hh
  refine ⟨c, ⟨hcpos, hc.1.2⟩, ?_, hclosed⟩
  rw [frontier, hU.interior_eq]
  exact ⟨hclosed ⟨hcpos.le, le_rfl⟩, hc.2⟩

end PoincareConjecture
