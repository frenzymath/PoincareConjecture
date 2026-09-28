import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Recenter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

private theorem exists_end_placement {epsilon : ℝ} (he : 0 < epsilon)
    {c : ℝ → ℝ}
    (hccont : ContinuousOn c (Icc ((4 / 5) * epsilon⁻¹) ((6 / 5) * epsilon⁻¹)))
    (hc : ∀ s ∈ Icc ((4 / 5) * epsilon⁻¹) ((6 / 5) * epsilon⁻¹),
      4 / 5 ≤ c s ∧ c s ≤ 6 / 5) :
    ∃ a : ℝ, a ∈ Icc (4 / 5) (6 / 5) ∧ c (a * epsilon⁻¹) * a ^ 2 = 1 := by
  let lo := (4 / 5 : ℝ) * epsilon⁻¹
  let hi := (6 / 5 : ℝ) * epsilon⁻¹
  have hL : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  let f : ℝ → ℝ := fun s => c s * (epsilon * s) ^ 2 - 1
  have hf : ContinuousOn f (Icc lo hi) :=
    (hccont.mul ((continuousOn_const.mul continuousOn_id).pow 2)).sub continuousOn_const
  have hlo : epsilon * lo = (4 / 5 : ℝ) := by dsimp [lo]; field_simp
  have hhi : epsilon * hi = (6 / 5 : ℝ) := by dsimp [hi]; field_simp
  have hfl : f lo ≤ 0 := by
    dsimp only [f]
    rw [hlo]
    nlinarith [(hc lo (left_mem_Icc.mpr hlohi)).2]
  have hfh : 0 ≤ f hi := by
    dsimp only [f]
    rw [hhi]
    nlinarith [(hc hi (right_mem_Icc.mpr hlohi)).1]
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc hlohi hf ⟨hfl, hfh⟩
  have hsc : (epsilon * s) * epsilon⁻¹ = s := by field_simp
  refine ⟨epsilon * s, ?_, ?_⟩
  · constructor
    · exact hlo ▸ mul_le_mul_of_nonneg_left hs.1 he.le
    · exact hhi ▸ mul_le_mul_of_nonneg_left hs.2 he.le
  · rw [hsc]
    change c s * (epsilon * s) ^ 2 - 1 = 0 at hz
    linarith



theorem exists_attaching_necks_threshold {epsilon : ℝ}
    (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 200) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ epsilon / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), N.epsilon ≤ delta → ∀ q : UnitTwoSphere,
        ∃ (a b : ℝ) (B E : EpsilonNeck g),
          a ∈ Icc (4 / 5) (6 / 5) ∧ b ∈ Icc (4 / 5) (6 / 5) ∧
          B.epsilon = epsilon ∧ E.epsilon = epsilon ∧
          B.connection = N.connection ∧ E.connection = N.connection ∧
          B.center = N.coordinate_map (q, 0) ∧
          E.center = N.coordinate_map (q, a * epsilon⁻¹) ∧
          B.carrier = N.region (-b * epsilon⁻¹) (b * epsilon⁻¹) ∧
          E.carrier = N.region 0 (2 * a * epsilon⁻¹) ∧
          B.central_sphere = N.central_sphere ∧
          E.coordinate_map = N.coordinate_map ∘
            RoundCylinderAffine.space a (a * epsilon⁻¹) ∧
          E.coordinate_inverse = RoundCylinderAffine.inverseSpace a (a * epsilon⁻¹) ∘
            N.coordinate_inverse := by
  obtain ⟨delta₁, hd₁, hd₁e, hneck⟩ := exists_recentered_neck_threshold.{u} he hesmall
  obtain ⟨delta₂, hd₂, _, hcurv⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (by norm_num : (0 : ℝ) < 1 / 5)
  refine ⟨min delta₁ delta₂, lt_min hd₁ hd₂, (min_le_left _ _).trans hd₁e, ?_⟩
  intro M _ _ _ _ _ _ _ g N hN q
  have hNe := (hN.trans (min_le_left _ _)).trans hd₁e
  have hL : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hNinv : 4 * epsilon⁻¹ ≤ N.epsilon⁻¹ := by
    have hi : (epsilon / 4)⁻¹ = 4 * epsilon⁻¹ := by field_simp
    rw [← hi]
    exact (inv_le_inv₀ (by positivity) N.epsilon_pos).mpr hNe
  let c : ℝ → ℝ := fun s =>
    N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, s))
  have hsub : Icc ((4 / 5 : ℝ) * epsilon⁻¹) ((6 / 5 : ℝ) * epsilon⁻¹) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hc (s : ℝ) (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
      4 / 5 < c s ∧ c s < 6 / 5 := by
    have hh := (hcurv N N.connection (hN.trans (min_le_right _ _)) q hs).1
    obtain ⟨hl, hu⟩ := abs_lt.mp hh
    constructor <;> dsimp only [c] <;> linarith
  have hccont : ContinuousOn c
      (Icc ((4 / 5) * epsilon⁻¹) ((6 / 5) * epsilon⁻¹)) := by
    apply continuousOn_const.mul
    apply N.connection.continuous_scalarCurvature.comp_continuousOn
    exact N.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨mem_univ _, hsub hs⟩)
  obtain ⟨a, ha, hacal⟩ := exists_end_placement he hccont
    (fun s hs => ⟨(hc s (hsub hs)).1.le, (hc s (hsub hs)).2.le⟩)
  have hap : 0 < a := by linarith [ha.1]
  have haabs : |a * epsilon⁻¹| ≤ (3 / 2) * epsilon⁻¹ := by
    rw [abs_of_pos (mul_pos hap hL)]
    exact mul_le_mul_of_nonneg_right (by linarith [ha.2]) hL.le
  obtain ⟨E, hEe, hEc, hEcenter, hEcarrier, hEsphere, hEmap, hEinv⟩ :=
    hneck N (hN.trans (min_le_left _ _)) q (a * epsilon⁻¹) a haabs hap hacal
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hc0 : 0 < c 0 := by linarith [(hc 0 hzero).1]
  let b := (Real.sqrt (c 0))⁻¹
  have hbp : 0 < b := inv_pos.mpr (Real.sqrt_pos.mpr hc0)
  have hbcal : c 0 * b ^ 2 = 1 := RoundCylinderAffine.calibrated_dilation hc0
  have hb : b ∈ Icc (4 / 5) (6 / 5) := by
    have hh := hc 0 hzero
    constructor <;> nlinarith [sq_nonneg (b - 4 / 5), sq_nonneg (b - 6 / 5)]
  obtain ⟨B, hBe, hBc, hBcenter, hBcarrier, hBsphere, _, _⟩ :=
    hneck N (hN.trans (min_le_left _ _)) q 0 b (by simp; positivity) hbp hbcal
  refine ⟨a, b, B, E, ha, hb, hBe, hEe, hBc, hEc, hBcenter, hEcenter,
    ?_, ?_, ?_, hEmap, hEinv⟩
  · simpa only [zero_sub, zero_add, neg_mul] using hBcarrier
  · convert hEcarrier using 1
    congr 1 <;> ring
  · exact hBsphere.trans N.centralSphere_range

end PoincareConjecture.NoncompactKappa.Positive
