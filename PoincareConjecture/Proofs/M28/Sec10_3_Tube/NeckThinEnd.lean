import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckOverlapCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls
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

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem neck_slice_edist_le (N : EpsilonNeck g)
    (p q : UnitTwoSphere) {a : ℝ}
    (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    g.edist (N.coordinate_map (p, a)) (N.coordinate_map (q, a)) ≤
      ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hlen, _, _⟩ := exists_standardSphere_short_path p q
  let η : ℝ → M := fun t => N.coordinate_map (γ t, a)
  have hη : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 η := by
    rw [← contMDiffOn_univ]
    apply (N.coordinate_map_smooth.of_le (by simp)).comp
    · exact (hγ.prodMk contMDiff_const).contMDiffOn
    · intro t _
      exact ⟨mem_univ _, ha⟩
  have hscale : 0 < 4 * N.scale := mul_pos (by norm_num) N.scale_pos
  have hbound := (coordinate_sphere_pathELength_le N hγ ha 0 1).trans_lt
    (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
      ENNReal.ofReal_ne_top hlen)
  have hdist := Manifold.riemannianEDist_le_pathELength hη.contMDiffOn
    (show η 0 = N.coordinate_map (p, a) by simp only [η, h0])
    (show η 1 = N.coordinate_map (q, a) by simp only [η, h1]) zero_le_one
  have hrhs : ENNReal.ofReal (4 * N.scale) * ENNReal.ofReal standardSpherePathCeiling =
      ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) := by
    rw [← ENNReal.ofReal_mul hscale.le]
    congr 1
    ring
  exact (hdist.trans hbound.le).trans_eq hrhs



theorem neck_edist_le_axial_gap_add_sphere (N : EpsilonNeck g) {x y : M}
    (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    g.edist x y ≤ ENNReal.ofReal
      ((2 * |(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
        4 * standardSpherePathCeiling) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let zx := N.coordinate_inverse x
  let zy := N.coordinate_inverse y
  have hzx : zx.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have hzy : zy.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem y hy).2
  have hax := N.edist_coordinate_map_axis_le zx.1 hzx hzy
  have hsqrt : Real.sqrt (1 + N.epsilon) ≤ 2 := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  have haxis : g.edist (N.coordinate_map (zx.1, zx.2))
      (N.coordinate_map (zx.1, zy.2)) ≤
      ENNReal.ofReal ((2 * |zy.2 - zx.2|) * N.scale) := by
    apply hax.trans (ENNReal.ofReal_le_ofReal ?_)
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt N.scale_pos.le) (abs_nonneg (zy.2 - zx.2))
    nlinarith
  have hsphere := neck_slice_edist_le N zx.1 zy.1 hzy
  have htriangle := (Manifold.riemannianEDist_triangle
    (x := N.coordinate_map (zx.1, zx.2))
    (y := N.coordinate_map (zx.1, zy.2))
    (z := N.coordinate_map (zy.1, zy.2))).trans (add_le_add haxis hsphere)
  have hxmap : N.coordinate_map (zx.1, zx.2) = x :=
    N.coordinate_map_coordinate_inverse hx
  have hymap : N.coordinate_map (zy.1, zy.2) = y :=
    N.coordinate_map_coordinate_inverse hy
  rw [hxmap, hymap] at htriangle
  have hrhs : ENNReal.ofReal ((2 * |zy.2 - zx.2|) * N.scale) +
      ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) =
      ENNReal.ofReal ((2 * |zy.2 - zx.2| +
        4 * standardSpherePathCeiling) * N.scale) := by
    rw [← ENNReal.ofReal_add
      (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) N.scale_pos.le)
      (mul_nonneg (mul_nonneg (by norm_num) standardSpherePathCeiling_pos.le)
        N.scale_pos.le)]
    congr 1
    ring
  exact htriangle.trans_eq hrhs

private theorem narrow_region_edist_le (N : EpsilonNeck g) {a b : ℝ}
    (hwidth : b - a ≤ N.epsilon⁻¹ / 128) {x y : M}
    (hx : x ∈ N.region a b) (hy : y ∈ N.region a b) :
    g.edist x y ≤ ENNReal.ofReal
      ((N.epsilon⁻¹ / 64 + 4 * standardSpherePathCeiling) * N.scale) := by
  have hgap : |(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| ≤
      N.epsilon⁻¹ / 128 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
  apply (neck_edist_le_axial_gap_add_sphere N hx.1 hy.1).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ N.scale_pos.le
  linarith



theorem neck_narrow_region_edist_center_le (N : EpsilonNeck g) {a b : ℝ}
    (hwidth : b - a ≤ N.epsilon⁻¹ / 128) {p : M}
    (hp : p ∈ closure (N.region a b)) {x : M} (hx : x ∈ N.region a b) :
    g.edist p x ≤ ENNReal.ofReal
      ((N.epsilon⁻¹ / 64 + 4 * standardSpherePathCeiling) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hclosed : IsClosed {y : M | g.edist x y ≤ ENNReal.ofReal
      ((N.epsilon⁻¹ / 64 + 4 * standardSpherePathCeiling) * N.scale)} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hsub : N.region a b ⊆ {y : M | g.edist x y ≤ ENNReal.ofReal
      ((N.epsilon⁻¹ / 64 + 4 * standardSpherePathCeiling) * N.scale)} :=
    fun _ hy => narrow_region_edist_le N hwidth hx hy
  have h := (closure_minimal hsub hclosed) hp
  change g.edist x p ≤ ENNReal.ofReal
    ((N.epsilon⁻¹ / 64 + 4 * standardSpherePathCeiling) * N.scale) at h
  simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using h





theorem exists_neck_narrow_region_capture_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon = N'.epsilon → N.epsilon ≤ epsilon₀ →
        ∀ a b : ℝ, b - a ≤ N.epsilon⁻¹ / 128 →
          N'.center ∈ closure (N.region a b) →
          N.region a b ⊆
            g.ball N'.center (N'.scale * N'.epsilon⁻¹ / 8) ∧
          N.region a b ⊆ N'.region (-(N'.epsilon⁻¹ / 2)) (N'.epsilon⁻¹ / 2) := by
  obtain ⟨epsilonS, hSpos, hSsmall, hscales⟩ :=
    exists_neck_overlap_scale_accuracy.{u}
  have hLs : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  refine ⟨min epsilonS (1 / (256 * standardSpherePathCeiling + 1)),
    lt_min hSpos (by positivity), (min_le_left _ _).trans hSsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N N' heq hN a b hwidth hclosure
  have hmeet : (N.carrier ∩ N'.carrier).Nonempty := by
    obtain ⟨x, hx', hx⟩ := mem_closure_iff.mp hclosure N'.carrier
      N'.carrier_open (N'.central_sphere_subset N'.center_on_central_sphere)
    exact ⟨x, hx.1, hx'⟩
  have hNsmall : N.epsilon ≤ epsilonS := hN.trans (min_le_left _ _)
  have hN'small : N'.epsilon ≤ epsilonS := heq ▸ hNsmall
  obtain ⟨hscale, _⟩ := hscales M g D N N' hNsmall hN'small hmeet
  have hsmall : N.epsilon ≤ 1 / (256 * standardSpherePathCeiling + 1) :=
    hN.trans (min_le_right _ _)
  have hinv : 256 * standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos hsmall
    simpa only [one_div, inv_inv] using h
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hcoefficient : 0 < N.epsilon⁻¹ / 64 + 4 * standardSpherePathCeiling :=
    by positivity
  have hbudget : (N.epsilon⁻¹ / 64 + 4 * standardSpherePathCeiling) * N.scale <
      N'.scale * N'.epsilon⁻¹ / 8 := by
    rw [← heq]
    have hscaled := mul_lt_mul_of_pos_left hscale hcoefficient
    have hsmall' : N.epsilon⁻¹ / 32 + 8 * standardSpherePathCeiling <
        N.epsilon⁻¹ / 8 := by linarith
    have hfinal := mul_lt_mul_of_pos_right hsmall' N'.scale_pos
    nlinarith
  have hball : N.region a b ⊆
      g.ball N'.center (N'.scale * N'.epsilon⁻¹ / 8) := by
    intro x hx
    apply (neck_narrow_region_edist_center_le N hwidth hclosure hx).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff
      (div_pos (mul_pos N'.scale_pos (inv_pos.mpr N'.epsilon_pos)) (by norm_num))).mpr
    exact hbudget
  exact ⟨hball, hball.trans (N'.small_ball_subset_middle N'.center_on_central_sphere)⟩

end PoincareConjecture.M28
