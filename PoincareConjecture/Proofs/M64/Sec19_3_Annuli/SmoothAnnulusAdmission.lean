import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]






theorem m64Annulus_exists_eq_of_contMDiffOn
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    {f : LoopPlane → M} {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x, f (annulusPoint x 1) = c1 x) :
    ∃ A : M64Annulus g c0 c1, A.map = f := by
  have hcontinuous : ContinuousOn f m64AnnulusDomain := hf.continuousOn.mono hdom
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hloc : LocallyLipschitzOn m64AnnulusDomain f := by
    intro p hp
    obtain ⟨C, W, hW, hC⟩ := m64_lipschitzOn_nhds_of_contMDiffAt g
      (hf.contMDiffAt (hU.mem_nhds (hdom hp)))
    refine ⟨C, W ∩ m64AnnulusDomain,
      inter_mem (nhdsWithin_le_nhds hW) self_mem_nhdsWithin, ?_⟩
    intro x hx y hy
    change g.edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y
    simpa only [edist_dist, dist_eq_norm] using hC x hx.1 y hy.1
  obtain ⟨C, hC⟩ := M60.exists_lipschitzOnWith_of_compact_edist_ne_top
    m64AnnulusDomain_isCompact hloc (m64AnnulusDomain_edist_ne_top g hcontinuous)
  have hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    have h := hC x.property y.property
    change g.edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist (x : LoopPlane) y at h
    simpa only [ENNReal.ofReal_coe_nnreal, edist_dist, dist_eq_norm] using h
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← MeasureTheory.measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨A, hA, _⟩ := m64Annulus_of_lipschitz g f hcontinuous
    hperiodic hlower hupper C.coe_nonneg hLip hfinite
    (lt_add_one (∫ p in m64AnnulusDomain, m60AreaDensity g f p))
  exact ⟨A, hA⟩

end PoincareConjecture
