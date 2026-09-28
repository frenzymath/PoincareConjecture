import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Radius.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Estimates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Lower.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Lower.TrichotomyTransfer












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

private theorem independent_of_metric_orthonormal
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (x : M) (a b : TangentSpace (𝓡 3) x)
    (ha : g.inner x a a = 1) (hb : g.inner x b b = 1) (hab : g.inner x a b = 0) :
    LinearIndependent ℝ ![a, b] := by
  apply linearIndependent_fin2.mpr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨fun hz => by simp [hz] at hb, ?_⟩
  intro r hr
  have hh := congrArg (fun w => g.inner x w b) hr
  simp only [map_smul, smul_apply, smul_eq_mul, hb, mul_one, hab] at hh
  subst r
  simp only [zero_smul] at hr
  simp [← hr] at ha



theorem noncompactKappaUniformCoreEstimates_of_trichotomy_of_services
    (P : NoncompactKappaServices.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy) :
    UniformSoulCenteredCoreConclusionOfServices.{u} := by
  let epsilonStar : ℝ := min neckSeparationThreshold (1 / 8)
  have hstar : 0 < epsilonStar := lt_min neckSeparationThreshold_pos (by norm_num)
  refine ⟨epsilonStar, hstar, ?_⟩
  intro epsilon hε hεstar
  have hεsmall : epsilon < 1 / 4 :=
    (hεstar.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hεsep : epsilon ≤ neckSeparationThreshold := hεstar.trans (min_le_left _ _)
  obtain ⟨D, hD, hneck⟩ := noncompact_uniform_strongNeck_radius_of_services P hε hεsmall hεsep
  obtain ⟨C, hC, hupper⟩ := noncompact_uniform_core_upper_and_volume_of_services P hD
  obtain ⟨B, hB, hlower⟩ := noncompact_uniform_soul_core_sectional_lower_of_services P htrichotomy hD
  let D₁ : ℝ := max B C
  have hBD : B ≤ D₁ := le_max_left _ _
  have hCD : C ≤ D₁ := le_max_right _ _
  have hD₁ : 1 < D₁ := hC.trans_le hCD
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hBpos : 0 < B := zero_lt_one.trans hB
  refine ⟨D, D₁, hD, hD₁, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact _hpositive
  let : NoncompactSpace M := not_compactSpace_iff.mp fun hcompact =>
    hnoncompact (isCompact_univ_iff.mpr hcompact)
  intro S
  obtain ⟨A⟩ := P.normalization M K S.center 0 le_rfl
  have hR : 0 < (K.flow.connection 0).scalarCurvature S.center := A.scale_eq ▸ A.scale_pos
  obtain ⟨hsectional, hvolLower, hvolUpper⟩ := hupper K S.center hnoncompact
  refine {
    epsilon_pos := hε
    soul_scalar_pos := hR
    radius_constant := hD
    curvature_constant := hD₁
    strong_outside := hneck K hnoncompact S
    sectional_bounds := ?_
    volume_bounds := ?_ }
  · intro x hx a b ha hb hab
    have hlin := independent_of_metric_orthonormal (K.flow.metric 0) x a b ha hb hab
    constructor
    · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hBpos hBD) hR.le).trans_lt
        (hlower K S hnoncompact x hx a b hlin)
    · exact (hsectional x hx a b).trans_le (mul_le_mul_of_nonneg_right hCD hR.le)
  · have hscale : 0 ≤ (K.flow.connection 0).scalarCurvature S.center ^ (-3 / 2 : ℝ) :=
      Real.rpow_nonneg hR.le _
    constructor
    · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hCpos hCD (by norm_num : (-3 / 2 : ℝ) ≤ 0))
        hscale)).trans_lt hvolLower
    · exact hvolUpper.trans_le (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hCpos.le hCD (by norm_num : (0 : ℝ) ≤ 3 / 2)) hscale))

theorem noncompactKappaUniformCoreEstimates_of_trichotomy
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy) :
    UniformSoulCenteredCoreConclusion P := by
  exact noncompactKappaUniformCoreEstimates_of_trichotomy_of_services P.noncompactServices htrichotomy

end PoincareConjecture
