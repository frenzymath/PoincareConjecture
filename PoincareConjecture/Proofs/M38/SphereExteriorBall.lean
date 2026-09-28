import PoincareConjecture.Proofs.M38.SpherePoleNormalization
import PoincareConjecture.Proofs.M38.AnnulusReparametrization










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩


noncomputable def sphereScaledPoleBall (p : sphereCarrier.{u}.carrier)
    (r : ℝ) (hr : 0 < r) : SurgeryBallEmbedding sphereCarrier.{u} := by
  let q : sphereCarrier.{u}.carrier := ULift.up (-p.down)
  let f : StandardCapSpace → sphereCarrier.{u}.carrier :=
    fun x => spherePunctureInverse q (ULift.up (r • x))
  let g : sphereCarrier.{u}.carrier → StandardCapSpace :=
    fun y => r⁻¹ • (spherePunctureMap q y).down
  have hscale : ContDiff ℝ ∞ (fun x : StandardCapSpace => r • x) :=
    contDiff_const_smul r
  have hinvscale : ContDiff ℝ ∞ (fun x : StandardCapSpace => r⁻¹ • x) :=
    contDiff_const_smul r⁻¹
  have hup : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : StandardCapSpace => (ULift.up (r • x) : euclideanCarrier.{u}.carrier)) :=
    (threeManifold_up_contMDiff StandardCapSpace).comp
      hscale.contMDiff
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := (spherePunctureInverse_smooth q).comp hup
  have hsub : f '' Metric.ball 0 2 ⊆ ({q} : Set sphereCarrier.{u}.carrier)ᶜ := by
    rintro _ ⟨x, _, rfl⟩
    exact spherePunctureInverse_ne q (ULift.up (r • x))
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    hinvscale.contMDiff.comp_contMDiffOn
      ((threeManifold_down_contMDiff StandardCapSpace).comp_contMDiffOn
        ((spherePunctureMap_smooth q).mono hsub))
  have hleft : Set.LeftInvOn g f (Metric.ball (0 : StandardCapSpace) 2) := by
    intro x _
    change r⁻¹ • (spherePunctureMap q (spherePunctureInverse q (ULift.up (r • x)))).down = x
    rw [spherePuncture_right_inverse q (Set.mem_univ _)]
    change r⁻¹ • (r • x) = x
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  exact {
    map := f
    inverse := g
    map_smooth := hf.contMDiffOn
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg f (hleft hx)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball
      hf.contMDiffOn hg hleft }


theorem sphereScaledPoleBall_map (p : sphereCarrier.{u}.carrier) {r : ℝ} (hr : 0 < r)
    (x : StandardCapSpace) :
    (sphereScaledPoleBall p r hr).map x =
      spherePunctureInverse (ULift.up (-p.down)) (ULift.up (r • x)) := rfl


theorem sphereScaledPoleBall_inverse (p y : sphereCarrier.{u}.carrier)
    {r : ℝ} (hr : 0 < r) :
    (sphereScaledPoleBall p r hr).inverse y =
      r⁻¹ • (spherePunctureMap (ULift.up (-p.down)) y).down := rfl


theorem spherePunctureInverse_zero (p : sphereCarrier.{u}.carrier) :
    spherePunctureInverse p (ULift.up 0) = ULift.up (-p.down) := by
  apply ULift.ext
  change threeSphereStereoInverse p.down 0 = -p.down
  simpa only [neg_neg] using threeSphereStereoInverse_opposite_zero (-p.down)


theorem sphereScaledPoleBall_center (p : sphereCarrier.{u}.carrier)
    {r : ℝ} (hr : 0 < r) : (sphereScaledPoleBall p r hr).map 0 = p := by
  rw [sphereScaledPoleBall_map, smul_zero, spherePunctureInverse_zero]
  apply ULift.ext
  exact neg_neg p.down


theorem sphereScaledPoleBall_right_inverse (p y : sphereCarrier.{u}.carrier)
    {r : ℝ} (hr : 0 < r) (hy : y ≠ ULift.up (-p.down)) :
    (sphereScaledPoleBall p r hr).map ((sphereScaledPoleBall p r hr).inverse y) = y := by
  rw [sphereScaledPoleBall_map, sphereScaledPoleBall_inverse, smul_smul,
    mul_inv_cancel₀ hr.ne', one_smul]
  exact spherePuncture_left_inverse (ULift.up (-p.down)) hy


theorem sphereScaledPoleBall_mem_closed_iff (p y : sphereCarrier.{u}.carrier)
    {r : ℝ} (hr : 0 < r) :
    y ∈ (sphereScaledPoleBall p r hr).closedBall ↔
      y ≠ ULift.up (-p.down) ∧ ‖(spherePunctureMap (ULift.up (-p.down)) y).down‖ ≤ r := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [sphereScaledPoleBall_map]
    refine ⟨spherePunctureInverse_ne _ _, ?_⟩
    rw [spherePuncture_right_inverse _ (Set.mem_univ _)]
    have hxnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change ‖r • x‖ ≤ r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  · rintro ⟨hy, hnorm⟩
    refine ⟨(sphereScaledPoleBall p r hr).inverse y, ?_,
      sphereScaledPoleBall_right_inverse p y hr hy⟩
    rw [Metric.mem_closedBall, dist_zero_right, sphereScaledPoleBall_inverse,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    calc
      r⁻¹ * ‖(spherePunctureMap (ULift.up (-p.down)) y).down‖ ≤ r⁻¹ * r :=
        mul_le_mul_of_nonneg_left hnorm (inv_pos.mpr hr).le
      _ = 1 := inv_mul_cancel₀ hr.ne'


theorem spherePuncture_opposite_norm (p : sphereCarrier.{u}.carrier)
    (x : StandardCapSpace) (hx : x ≠ 0) :
    ‖(spherePunctureMap (ULift.up (-p.down)) (spherePunctureInverse p (ULift.up x))).down‖ =
      4 / ‖x‖ := by
  have h := threeSphereStereo_opposite (-p.down) x hx
  simp only [neg_neg] at h
  change ‖stereographic' 3 (-p.down) (threeSphereStereoInverse p.down x)‖ = _
  rw [threeSphereStereoInverse, h, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num)
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))),
    (threeSphereStereoOppositeIsometry (-p.down)).norm_map]
  field_simp [norm_ne_zero_iff.mpr hx]


theorem sphereScaledPoleBall_opposite_mem (p : sphereCarrier.{u}.carrier)
    {r : ℝ} (hr : 0 < r) (x : StandardCapSpace) :
    spherePunctureInverse p (ULift.up x) ∈ (sphereScaledPoleBall p r hr).closedBall ↔
      4 / r ≤ ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [spherePunctureInverse_zero, sphereScaledPoleBall_mem_closed_iff]
    simp only [ne_eq, not_true_eq_false, false_and, norm_zero, false_iff]
    exact not_le.mpr (div_pos (by norm_num) hr)
  · have hne : spherePunctureInverse p (ULift.up x) ≠ ULift.up (-p.down) := by
      intro heq
      have hzero := spherePunctureInverse_zero p
      have hinj := (spherePuncture_right_inverse p).injOn
        (Set.mem_univ (ULift.up x)) (Set.mem_univ (ULift.up 0)) (heq.trans hzero.symm)
      exact hx (congrArg ULift.down hinj)
    rw [sphereScaledPoleBall_mem_closed_iff, and_iff_right hne,
      spherePuncture_opposite_norm p x hx]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [div_le_iff₀ hn, div_le_iff₀ hr]
    exact by rw [mul_comm]


theorem sphereScaledPoleBall_complement (p : sphereCarrier.{u}.carrier)
    {r : ℝ} (hr : 0 < r) :
    (sphereScaledPoleBall p r hr).closedBallᶜ =
      (fun x : StandardCapSpace => spherePunctureInverse p (ULift.up x)) ''
        Metric.ball 0 (4 / r) := by
  ext y
  constructor
  · intro hy
    have hyp : y ≠ p := by
      intro heq
      apply hy
      refine ⟨0, by simp, ?_⟩
      rw [sphereScaledPoleBall_center, heq]
    let x := (spherePunctureMap p y).down
    have hxy : spherePunctureInverse p (ULift.up x) = y := spherePuncture_left_inverse p hyp
    refine ⟨x, ?_, hxy⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_not_ge (fun h => hy (hxy ▸ (sphereScaledPoleBall_opposite_mem p hr x).mpr h))
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_compl_iff, sphereScaledPoleBall_opposite_mem]
    exact not_le.mpr (by simpa only [Metric.mem_ball, dist_zero_right] using hx)



noncomputable def sphereOuterBall (p : sphereCarrier.{u}.carrier) :
    SurgeryBallEmbedding sphereCarrier.{u} :=
  annulusReparametrizedBall (a := 1 / 8) (by norm_num) (by norm_num)
    (sphereScaledPoleBall (ULift.up (-p.down)) (8 / 3) (by norm_num))


theorem sphereOuterBall_complement (p : sphereCarrier.{u}.carrier) :
    (sphereOuterBall p).closedBallᶜ =
      (spherePoleReferenceBall p).map '' Metric.ball 0 (3 / 2) := by
  rw [sphereOuterBall, annulusReparametrizedBall_closedBall,
    sphereScaledPoleBall_complement]
  norm_num <;> rfl


theorem sphereOuterBall_full_disjoint (p : sphereCarrier.{u}.carrier) :
    Disjoint ((sphereOuterBall p).map '' Metric.ball 0 2)
      ((spherePoleReferenceBall p).map '' Metric.ball 0 1) := by
  let H := sphereScaledPoleBall (ULift.up (-p.down)) 3 (by norm_num)
  have houter : (sphereOuterBall p).map '' Metric.ball 0 2 ⊆ H.closedBall := by
    rw [sphereOuterBall, annulusReparametrizedBall_image]
    rintro y ⟨x, hx, rfl⟩
    have hnorm : ‖x‖ < 9 / 8 := by
      simpa only [Metric.mem_ball, dist_zero_right, show (1 : ℝ) + 1 / 8 = 9 / 8 by norm_num]
        using hx
    refine ⟨(8 / 9 : ℝ) • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 8 / 9)]
      nlinarith
    · change (sphereScaledPoleBall (ULift.up (-p.down)) 3 (by norm_num)).map
        ((8 / 9 : ℝ) • x) = _
      rw [sphereScaledPoleBall_map, sphereScaledPoleBall_map, smul_smul]
      norm_num
  have hinner : (spherePoleReferenceBall p).map '' Metric.ball 0 1 ⊆ H.closedBallᶜ := by
    change (spherePoleReferenceBall p).map '' Metric.ball 0 1 ⊆
      (sphereScaledPoleBall (ULift.up (-p.down)) 3 (by norm_num)).closedBallᶜ
    rw [sphereScaledPoleBall_complement]
    rintro y ⟨x, hx, rfl⟩
    refine ⟨x, Metric.ball_subset_ball (by norm_num) hx, rfl⟩
  exact Set.disjoint_left.mpr (fun _ hy hz => hinner hz (houter hy))

end PoincareConjecture.M38
