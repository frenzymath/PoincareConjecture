import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorVerticalColumn
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzDerivative
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





theorem m64_horizontal_column_of_metric_lipschitz
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    {z : LoopPlane} (hz : z ∈ m64AnnulusInterior) :
    g.tangentNorm (f z)
        (mfderiv (𝓡 2) (𝓡 n) f z
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ 2 * L := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  have hS : IsOpen m64AnnulusInterior := isOpen_m64AnnulusInterior
  have hSsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    intro x hx
    simp only [m64AnnulusInterior, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioo] at hx
    change 0 ≤ x 0 ∧ x 0 ≤ curvePeriod ∧ 0 ≤ x 1 ∧ x 1 ≤ 1
    have h0 := hx 0 trivial
    have h1 := hx 1 trivial
    simpa using ⟨h0.1.le, h0.2.le, h1.1.le, h1.2.le⟩
  let K : ℝ≥0 := ⟨L, hL⟩
  have hK : LipschitzOnWith K f m64AnnulusInterior := by
    intro x hx y hy
    have hh := hLip ⟨x, hSsub hx⟩ ⟨y, hSsub hy⟩
    change g.edist (f x) (f y) ≤
      (K : ℝ≥0∞) * edist x y
    rw [ENNReal.coe_nnreal_eq, edist_dist, dist_eq_norm]
    exact hh
  have hb := M60.norm_mfderiv_apply_le_of_lipschitzOn
    (F := EuclideanSpace ℝ (Fin n)) (f := f) hS hK hz
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  erw [OrthonormalBasis.norm_eq_one, mul_one] at hb
  change ‖mfderiv (𝓡 2) (𝓡 n) f z
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ ≤ 2 * L
  exact hb





theorem m64_horizontal_column_ae_of_metric_lipschitz
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :
    ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z
            (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ 2 * L := by
  apply (ae_restrict_iff' m64AnnulusDomain_measurableSet).2
  filter_upwards [m64AnnulusDomain_ae_eq_interior] with z hz
  intro hzdom
  exact m64_horizontal_column_of_metric_lipschitz g hL hLip (hz.mp hzdom)






theorem m64AnnulusIntegral_le_of_metric_lipschitz_and_ae_vertical
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    {L K1 : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    (hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal))
    (hcol1 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K1) :
    (∫ z in m64AnnulusDomain, m60AreaDensity g f z) ≤
      (2 * L) * K1 * volume.real m64AnnulusDomain := by
  have hcol0 := m64_horizontal_column_ae_of_metric_lipschitz g hL hLip
  have hK0 : 0 ≤ 2 * L := by positivity
  exact m64AnnulusIntegral_le_of_lipschitzOn_and_ae_column_bounds
    g hL hK0 hLip hfinite hcol0 hcol1

end PoincareConjecture
