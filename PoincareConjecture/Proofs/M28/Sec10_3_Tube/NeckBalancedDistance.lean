import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSpherePaths
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

private theorem neck_center_edist_upper (N : EpsilonNeck g) {x : M}
    (hx : x ∈ N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal
      ((Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ +
        4 * standardSpherePathCeiling) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcentral : N.coordinate_map (z.1, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  obtain ⟨γ, h0, h1, hγ, _, hlength, _, _⟩ :=
    exists_central_sphere_shortcut N N.center_on_central_sphere hcentral
  have hsphere := (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn
    h0 h1 zero_le_one).trans hlength.le
  have haxis := N.edist_coordinate_map_axis_le z.1 hzero hz
  have hcoord : N.coordinate_map (z.1, z.2) = x :=
    N.coordinate_map_coordinate_inverse hx
  rw [hcoord, sub_zero] at haxis
  have hheight : |z.2| ≤ N.epsilon⁻¹ := (abs_lt.mpr hz).le
  have haxis' : g.edist (N.coordinate_map (z.1, 0)) x ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹) :=
    haxis.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hheight
      (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))))
  have hsum := (Manifold.riemannianEDist_triangle
    (x := N.center) (y := N.coordinate_map (z.1, 0)) (z := x)).trans
      (add_le_add hsphere haxis')
  have heq : ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) +
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹) =
        ENNReal.ofReal ((Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ +
          4 * standardSpherePathCeiling) * N.scale) := by
    rw [← ENNReal.ofReal_add
      (mul_nonneg (mul_nonneg (by norm_num) standardSpherePathCeiling_pos.le)
        N.scale_pos.le)
      (mul_nonneg (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
        (inv_nonneg.mpr N.epsilon_pos.le))]
    congr 1
    ring
  exact hsum.trans_eq heq

private theorem neck_center_edist_upper_closure (N : EpsilonNeck g) {x : M}
    (hx : x ∈ closure N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal
      ((Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ +
        4 * standardSpherePathCeiling) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hclosed : IsClosed {y : M | g.edist N.center y ≤ ENNReal.ofReal
      ((Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ +
        4 * standardSpherePathCeiling) * N.scale)} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  exact (closure_minimal (fun _ hy => neck_center_edist_upper N hy) hclosed) hx

theorem exists_neck_frontier_distance_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → ∀ x ∈ frontier N.carrier,
          ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
            g.edist N.center x ∧
          g.edist N.center x ≤
            ENNReal.ofReal ((1.01 : ℝ) * N.scale * N.epsilon⁻¹) := by
  have hLs := standardSpherePathCeiling_pos
  refine ⟨min (1 / 1000) (1 / (4000 * standardSpherePathCeiling + 1)),
    lt_min (by norm_num) (by positivity), (min_le_left _ _).trans (by norm_num), ?_⟩
  intro M _ _ _ _ _ _ _ g N hsmall x hx
  have hepsilon : N.epsilon ≤ 1 / 1000 := hsmall.trans (min_le_left _ _)
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hrootLower : (999 / 1000 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hrootUpper : Real.sqrt (1 + N.epsilon) ≤ (1001 / 1000 : ℝ) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hout : x ∉ N.carrier := (N.carrier_open.frontier_eq ▸ hx).2
  have hlower := N.edist_central_lower_of_not_mem_region
    (r := (999 / 1000 : ℝ) * N.epsilon⁻¹) (by positivity) (by linarith)
    N.center_on_central_sphere (fun h => hout h.1)
  have hcoef : (0.99 : ℝ) ≤ Real.sqrt (1 - N.epsilon) * (999 / 1000) := by
    nlinarith only [hrootLower]
  have hlowBudget : (0.99 : ℝ) * N.scale * N.epsilon⁻¹ ≤
      (N.scale * Real.sqrt (1 - N.epsilon)) * ((999 / 1000) * N.epsilon⁻¹) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoef N.scale_pos.le) hA.le
    nlinarith only [h]
  have hrecip : 4000 * standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos
      (hsmall.trans (min_le_right _ _))
    simpa only [one_div, inv_inv] using h
  have hcoefUpper : Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ +
      4 * standardSpherePathCeiling ≤ (1.01 : ℝ) * N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hrootUpper hA.le
    linarith
  have hupperBudget := mul_le_mul_of_nonneg_right hcoefUpper N.scale_pos.le
  refine ⟨(ENNReal.ofReal_le_ofReal hlowBudget).trans hlower, ?_⟩
  apply (neck_center_edist_upper_closure N (frontier_subset_closure hx)).trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [hupperBudget]

end PoincareConjecture.M28
