import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalProfiles
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SouthernSphereChart








set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


theorem stackCanonicalMeridian_formula
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    (∀ v : ℝ, (stackCanonicalMeridian rFlat rOne v0 v1 v).1 =
      1 - Real.smoothTransition ((v ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2)) *
        (1 - Real.sqrt (1 - v ^ 2))) ∧
    ∀ v ∈ Icc (-1 : ℝ) 0,
      (stackCanonicalMeridian rFlat rOne v0 v1 v).2 =
        -1 + (v + 1) * Real.smoothTransition
          ((1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)) := by
  have hv1pos : 0 < v1 := hv0.trans hv01
  have hrOnepos : 0 < rOne := hrFlat.trans hradii
  have hv01sq : v0 ^ 2 < v1 ^ 2 := (sq_lt_sq₀ hv0.le hv1pos.le).mpr hv01
  have hv1sq : v1 ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hv1pos.le zero_le_one).mpr hv1
  have hr01sq : rFlat ^ 2 < rOne ^ 2 := (sq_lt_sq₀ hrFlat.le hrOnepos.le).mpr hradii
  have hr1sq : rOne ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hrOnepos.le zero_le_one).mpr hrOne
  obtain ⟨_, _, _, hafar, halow, _⟩ :=
    stackCanonicalFactor_spec (v0 ^ 2) (v1 ^ 2) hv01sq hv1sq
  obtain ⟨_, _, _, hbfar, _, _⟩ :=
    stackCanonicalFactor_spec (rFlat ^ 2) (rOne ^ 2) hr01sq hr1sq
  have hdv : 0 < v1 ^ 2 - v0 ^ 2 := sub_pos.mpr hv01sq
  have hdr : 0 < rOne ^ 2 - rFlat ^ 2 := sub_pos.mpr hr01sq
  constructor
  · intro v
    change stackCanonicalFactor (v0 ^ 2) (v1 ^ 2) (v ^ 2) * Real.sqrt (1 - v ^ 2) = _
    by_cases hv : v1 ^ 2 ≤ v ^ 2
    · have harg : 1 ≤ (v ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2) :=
        (le_div_iff₀ hdv).mpr (by linarith)
      rw [hafar _ hv, Real.smoothTransition.one_of_one_le harg]
      ring
    · have hr : Real.sqrt (1 - v ^ 2) ≠ 0 :=
        (Real.sqrt_pos.mpr (by linarith [lt_of_not_ge hv])).ne'
      rw [stackCanonicalFactor]
      field_simp [hr]
      ring
  · intro v hv
    have hvsq : v ^ 2 ≤ 1 := by
      have habs : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2.trans zero_le_one⟩
      simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg v) zero_le_one).mpr habs
    have hrsq : (Real.sqrt (1 - v ^ 2)) ^ 2 = 1 - v ^ 2 :=
      Real.sq_sqrt (sub_nonneg.mpr hvsq)
    by_cases hfar : v1 ^ 2 ≤ v ^ 2
    · have ha : stackCanonicalHorizontal v0 v1 v = 1 := hafar _ hfar
      have hvneg : v < 0 := by nlinarith only [hv.2, hfar, sq_pos_of_pos hv1pos]
      have hroot : Real.sqrt (1 - (Real.sqrt (1 - v ^ 2)) ^ 2) = -v := by
        rw [hrsq, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_neg hvneg]
      have hcancel : (-v)⁻¹ * v = -1 := by
        rw [inv_neg, neg_mul, inv_mul_cancel₀ hvneg.ne]
      change stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2)
        ((stackCanonicalHorizontal v0 v1 v * Real.sqrt (1 - v ^ 2)) ^ 2) * v = _
      rw [ha, one_mul]
      rw [stackCanonicalFactor, hroot, hrsq]
      calc
        (1 + (1 - Real.smoothTransition
            ((1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2))) * ((-v)⁻¹ - 1)) * v =
          (Real.smoothTransition ((1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)) +
            (1 - Real.smoothTransition ((1 - v ^ 2 - rFlat ^ 2) /
              (rOne ^ 2 - rFlat ^ 2))) * (-v)⁻¹) * v := by ring
        _ = _ := by rw [add_mul, mul_assoc, hcancel]; ring
    · have hvsmall : v ^ 2 < v1 ^ 2 := lt_of_not_ge hfar
      have hrgt : rOne < Real.sqrt (1 - v ^ 2) := by
        nlinarith only [hrsq, hgap, hvsmall, hrOnepos, Real.sqrt_nonneg (1 - v ^ 2)]
      have hRge : Real.sqrt (1 - v ^ 2) ≤
          stackCanonicalHorizontal v0 v1 v * Real.sqrt (1 - v ^ 2) := by
        simpa only [one_mul, stackCanonicalHorizontal] using mul_le_mul_of_nonneg_right
          (halow (v ^ 2) (sq_nonneg v)) (Real.sqrt_nonneg (1 - v ^ 2))
      have hRsq : rOne ^ 2 ≤
          (stackCanonicalHorizontal v0 v1 v * Real.sqrt (1 - v ^ 2)) ^ 2 :=
        (sq_le_sq₀ hrOnepos.le (hrOnepos.le.trans (hrgt.le.trans hRge))).mpr
          (hrgt.le.trans hRge)
      have harg : 1 ≤ (1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2) :=
        (le_div_iff₀ hdr).mpr (by linarith only [hgap, hvsmall])
      change stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2)
        ((stackCanonicalHorizontal v0 v1 v * Real.sqrt (1 - v ^ 2)) ^ 2) * v = _
      rw [hbfar _ hRsq, Real.smoothTransition.one_of_one_le harg]
      ring


theorem stackCanonicalMeridian_regular
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let R := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).1
    let Z := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).2
    ∀ v ∈ Ioc (-1 : ℝ) 0,
      DifferentiableAt ℝ R v ∧ DifferentiableAt ℝ Z v ∧
      0 ≤ deriv R v ∧ 0 ≤ deriv Z v ∧
      (0 < deriv R v ∨ 0 < deriv Z v) := by
  let R := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).1
  let Z := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).2
  let r := fun v : ℝ => Real.sqrt (1 - v ^ 2)
  let k := fun v : ℝ => Real.smoothTransition ((v ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2))
  let theta := fun v : ℝ => Real.smoothTransition
    ((1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2))
  have hv1pos : 0 < v1 := hv0.trans hv01
  have hrOnepos : 0 < rOne := hrFlat.trans hradii
  have hv01sq : v0 ^ 2 < v1 ^ 2 := (sq_lt_sq₀ hv0.le hv1pos.le).mpr hv01
  have hv1sq : v1 ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hv1pos.le zero_le_one).mpr hv1
  have hr01sq : rFlat ^ 2 < rOne ^ 2 := (sq_lt_sq₀ hrFlat.le hrOnepos.le).mpr hradii
  have hr1sq : rOne ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hrOnepos.le zero_le_one).mpr hrOne
  have hdv : 0 < v1 ^ 2 - v0 ^ 2 := sub_pos.mpr hv01sq
  have hdr : 0 < rOne ^ 2 - rFlat ^ 2 := sub_pos.mpr hr01sq
  obtain ⟨hRformula, hZformula⟩ := stackCanonicalMeridian_formula
    rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  obtain ⟨_, _, halow, _, _, _, _⟩ := stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨_, _, _, hbfar, _, _⟩ :=
    stackCanonicalFactor_spec (rFlat ^ 2) (rOne ^ 2) hr01sq hr1sq
  have hZnear (w : ℝ) (hw : w ^ 2 < v1 ^ 2) : Z w = w := by
    have hrad : 0 < 1 - w ^ 2 := by linarith only [hw, hv1sq]
    have hrsq : (r w) ^ 2 = 1 - w ^ 2 := Real.sq_sqrt hrad.le
    have hrgt : rOne < r w := by
      nlinarith only [hrsq, hgap, hw, hrOnepos, Real.sqrt_nonneg (1 - w ^ 2)]
    have hRge : r w ≤ R w := by
      exact (one_mul (r w)) ▸ mul_le_mul_of_nonneg_right (halow w) (Real.sqrt_nonneg _)
    have hRsq : rOne ^ 2 ≤ (R w) ^ 2 :=
      (sq_le_sq₀ hrOnepos.le (hrOnepos.le.trans (hrgt.le.trans hRge))).mpr
        (hrgt.le.trans hRge)
    change stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2) ((R w) ^ 2) * w = w
    rw [hbfar _ hRsq, one_mul]
  have hSc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hS : Differentiable ℝ Real.smoothTransition := hSc.differentiable (by simp)
  have hSnonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
    Real.smoothTransition.monotone.deriv_nonneg
  change ∀ v ∈ Ioc (-1 : ℝ) 0,
    DifferentiableAt ℝ R v ∧ DifferentiableAt ℝ Z v ∧
    0 ≤ deriv R v ∧ 0 ≤ deriv Z v ∧ (0 < deriv R v ∨ 0 < deriv Z v)
  intro v hv
  have hvabs : |v| < 1 := abs_lt.mpr ⟨hv.1, hv.2.trans_lt zero_lt_one⟩
  have hvsq : v ^ 2 < 1 := by
    simpa only [sq_abs, one_pow] using (sq_lt_sq₀ (abs_nonneg v) zero_le_one).mpr hvabs
  have hrpos : 0 < r v := Real.sqrt_pos.mpr (sub_pos.mpr hvsq)
  have hrle : r v ≤ 1 := Real.sqrt_le_one.mpr (by linarith only [sq_nonneg v])
  have hdradius : HasDerivAt r (-v / r v) v := by
    have h := ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_pow 2 v)).sqrt
      (sub_pos.mpr hvsq).ne'
    convert h using 1 <;> dsimp only [r] <;> norm_num
    ring
  let kp := deriv Real.smoothTransition ((v ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2)) *
    (2 * v / (v1 ^ 2 - v0 ^ 2))
  have hdk : HasDerivAt k kp v := by
    have hi : HasDerivAt (fun w : ℝ => (w ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2))
        (2 * v / (v1 ^ 2 - v0 ^ 2)) v := by
      exact (((hasDerivAt_pow 2 v).sub_const (v0 ^ 2)).div_const
        (v1 ^ 2 - v0 ^ 2)).congr_deriv (by norm_num)
    exact (hS _).hasDerivAt.comp v hi
  have hkp : kp ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hSnonneg _)
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hv.2) hdv.le)
  have hRderiv : HasDerivAt R (-kp * (1 - r v) + k v * (-v / r v)) v := by
    have heq : R = fun w => 1 - k w * (1 - r w) := funext hRformula
    rw [heq]
    exact ((hasDerivAt_const v (1 : ℝ)).sub
      (hdk.mul ((hasDerivAt_const v (1 : ℝ)).sub hdradius))).congr_deriv
        (by simp only [Pi.sub_apply]; ring)
  have hRnonneg : 0 ≤ deriv R v := by
    rw [hRderiv.deriv]
    exact add_nonneg (mul_nonneg (neg_nonneg.mpr hkp) (sub_nonneg.mpr hrle))
      (mul_nonneg (Real.smoothTransition.nonneg _)
        (div_nonneg (neg_nonneg.mpr hv.2) hrpos.le))
  by_cases hkzero : k v = 0
  · have harg : (v ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2) ≤ 0 :=
      Real.smoothTransition.zero_iff_nonpos.mp hkzero
    have hsmall : v ^ 2 < v1 ^ 2 := by
      have h := (div_le_iff₀ hdv).mp harg
      linarith only [h, hv01sq]
    have hopen : IsOpen {w : ℝ | w ^ 2 < v1 ^ 2} :=
      isOpen_lt (continuous_id.pow 2) continuous_const
    have heq : Z =ᶠ[𝓝 v] (fun w : ℝ => w) := by
      filter_upwards [hopen.mem_nhds hsmall] with w hw
      exact hZnear w hw
    have hZd : HasDerivAt Z 1 v := (hasDerivAt_id v).congr_of_eventuallyEq heq
    refine ⟨hRderiv.differentiableAt, hZd.differentiableAt, hRnonneg, ?_, Or.inr ?_⟩ <;>
      rw [hZd.deriv] <;> norm_num
  · have hkpos : 0 < k v := lt_of_le_of_ne (Real.smoothTransition.nonneg _) (Ne.symm hkzero)
    have hvneg : v < 0 := by
      apply lt_of_le_of_ne hv.2
      intro hz
      have harg : (v ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2) ≤ 0 := by
        rw [hz, zero_pow (by norm_num : 2 ≠ 0), zero_sub]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v0)) hdv.le
      exact hkzero (Real.smoothTransition.zero_of_nonpos harg)
    let tp := deriv Real.smoothTransition
      ((1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)) *
        (-2 * v / (rOne ^ 2 - rFlat ^ 2))
    have hdt : HasDerivAt theta tp v := by
      have hi : HasDerivAt (fun w : ℝ => (1 - w ^ 2 - rFlat ^ 2) /
          (rOne ^ 2 - rFlat ^ 2)) (-2 * v / (rOne ^ 2 - rFlat ^ 2)) v := by
        exact ((((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_pow 2 v)).sub_const
          (rFlat ^ 2)).div_const (rOne ^ 2 - rFlat ^ 2)).congr_deriv (by norm_num)
      exact (hS _).hasDerivAt.comp v hi
    have htp : 0 ≤ tp := mul_nonneg (hSnonneg _)
      (div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) hv.2) hdr.le)
    have heq : Z =ᶠ[𝓝 v] (fun w => -1 + (w + 1) * theta w) := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hv.1, hvneg⟩] with w hw
      exact hZformula w ⟨hw.1.le, hw.2.le⟩
    have hZd : HasDerivAt Z (theta v + (v + 1) * tp) v := by
      have h : HasDerivAt (fun w => -1 + (w + 1) * theta w)
          (theta v + (v + 1) * tp) v := by
        exact ((hasDerivAt_const v (-1 : ℝ)).add
          (((hasDerivAt_id v).add_const 1).mul hdt)).congr_deriv (by simp only [id_eq]; ring)
      exact h.congr_of_eventuallyEq heq
    refine ⟨hRderiv.differentiableAt, hZd.differentiableAt, hRnonneg, ?_, Or.inl ?_⟩
    · rw [hZd.deriv]
      exact add_nonneg (Real.smoothTransition.nonneg _)
        (mul_nonneg (by linarith only [hv.1]) htp)
    · rw [hRderiv.deriv]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (neg_nonneg.mpr hkp) (sub_nonneg.mpr hrle))
        (mul_pos hkpos (div_pos (neg_pos.mpr hvneg) hrpos))


theorem stackCanonicalModel_southern_geometry
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    ∀ p : E2 × ℝ, ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 → p.2 ≤ 0 →
      (‖(M p).1‖, (M p).2) = stackCanonicalMeridian rFlat rOne v0 v1 p.2 ∧
      ‖(M p).1‖ ≤ 1 ∧ -1 ≤ (M p).2 ∧ (M p).2 ≤ 0 ∧
      (‖(M p).1‖ ≤ rFlat → M p = (p.1, -1)) ∧
      (|p.2| ≤ v0 → M p = ((Real.sqrt (1 - p.2 ^ 2))⁻¹ • p.1, p.2)) := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  change ∀ p : E2 × ℝ, ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 → p.2 ≤ 0 →
    (‖(M p).1‖, (M p).2) = stackCanonicalMeridian rFlat rOne v0 v1 p.2 ∧
    ‖(M p).1‖ ≤ 1 ∧ -1 ≤ (M p).2 ∧ (M p).2 ≤ 0 ∧
    (‖(M p).1‖ ≤ rFlat → M p = (p.1, -1)) ∧
    (|p.2| ≤ v0 → M p = ((Real.sqrt (1 - p.2 ^ 2))⁻¹ • p.1, p.2))
  obtain ⟨_, hapos, halow, _, hanear, hafar, _⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨_, _, _, hbnear, hbfar, _⟩ :=
    stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  change ∀ x, ‖x‖ ≤ rFlat → b x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹ at hbnear
  change ∀ x, rOne ≤ ‖x‖ → b x = 1 at hbfar
  obtain ⟨hRf, hZf⟩ := stackCanonicalMeridian_formula
    rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  have hM (p : E2 × ℝ) : M p = (a p.2 • p.1, b (a p.2 • p.1) * p.2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  intro p hp hpneg
  have hvabs : |p.2| ≤ 1 := by
    have hsq : p.2 ^ 2 ≤ 1 := by nlinarith only [hp, sq_nonneg ‖p.1‖]
    exact (sq_le_sq₀ (abs_nonneg p.2) zero_le_one).mp (by simpa only [sq_abs, one_pow])
  have hv : p.2 ∈ Icc (-1 : ℝ) 0 := ⟨(abs_le.mp hvabs).1, hpneg⟩
  have hroot : Real.sqrt (1 - p.2 ^ 2) = ‖p.1‖ := by
    rw [show 1 - p.2 ^ 2 = ‖p.1‖ ^ 2 by linarith only [hp],
      Real.sqrt_sq (norm_nonneg p.1)]
  have hn : ‖a p.2 • p.1‖ = a p.2 * ‖p.1‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hapos p.2)]
  have hpair : (‖(M p).1‖, (M p).2) = stackCanonicalMeridian rFlat rOne v0 v1 p.2 := by
    rw [hM, stackCanonicalMeridian, hroot]
    change (‖a p.2 • p.1‖, stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2)
      (‖a p.2 • p.1‖ ^ 2) * p.2) = _
    rw [hn]
  have hR : ‖(M p).1‖ = 1 - Real.smoothTransition
      ((p.2 ^ 2 - v0 ^ 2) / (v1 ^ 2 - v0 ^ 2)) * (1 - Real.sqrt (1 - p.2 ^ 2)) :=
    (congrArg Prod.fst hpair).trans (hRf p.2)
  have hZ : (M p).2 = -1 + (p.2 + 1) * Real.smoothTransition
      ((1 - p.2 ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)) :=
    (congrArg Prod.snd hpair).trans (hZf p.2 hv)
  have hrle : Real.sqrt (1 - p.2 ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by linarith only [sq_nonneg p.2])
  have hheight_nonneg : 0 ≤ (p.2 + 1) * Real.smoothTransition
      ((1 - p.2 ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)) :=
    mul_nonneg (by linarith only [hv.1]) (Real.smoothTransition.nonneg _)
  have hheight_le : (p.2 + 1) * Real.smoothTransition
      ((1 - p.2 ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)) ≤ 1 := by
    calc
      _ ≤ (p.2 + 1) * 1 := mul_le_mul_of_nonneg_left
        (Real.smoothTransition.le_one _) (by linarith only [hv.1])
      _ ≤ 1 := by linarith only [hpneg]
  refine ⟨hpair, ?_, by linarith only [hZ, hheight_nonneg],
    by linarith only [hZ, hheight_le], ?_, ?_⟩
  · rw [hR]
    exact sub_le_self _ (mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr hrle))
  · intro hflat
    have hnormge : ‖p.1‖ ≤ ‖(M p).1‖ := by
      rw [hM, hn]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (halow p.2) (norm_nonneg p.1)
    have hnormflat : ‖p.1‖ ≤ rFlat := hnormge.trans hflat
    have hnormsq : ‖p.1‖ ^ 2 < rOne ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg p.1) (hrFlat.le.trans hradii.le)).mpr (hnormflat.trans_lt hradii)
    have hv1pos : 0 < v1 := hv0.trans hv01
    have hvlarge : v1 ≤ |p.2| := by
      apply (sq_le_sq₀ hv1pos.le (abs_nonneg p.2)).mp
      rw [sq_abs]
      linarith only [hp, hnormsq, hgap]
    have ha : a p.2 = 1 := hafar p.2 hvlarge
    have hvneg : p.2 < 0 := by
      have hxlt : ‖p.1‖ < 1 := hnormflat.trans_lt (hradii.trans hrOne)
      have hxsq : ‖p.1‖ ^ 2 < 1 := by
        simpa only [one_pow] using (sq_lt_sq₀ (norm_nonneg p.1) zero_le_one).mpr hxlt
      nlinarith only [hp, hpneg, hxsq]
    have hrootv : Real.sqrt (1 - ‖p.1‖ ^ 2) = -p.2 := by
      rw [show 1 - ‖p.1‖ ^ 2 = p.2 ^ 2 by linarith only [hp],
        Real.sqrt_sq_eq_abs, abs_of_neg hvneg]
    rw [hM, ha, one_smul, hbnear _ hnormflat, hrootv,
      inv_neg, neg_mul, inv_mul_cancel₀ hvneg.ne]
  · intro hnear
    have ha : a p.2 = (Real.sqrt (1 - p.2 ^ 2))⁻¹ := hanear p.2 hnear
    have hvlt : |p.2| < 1 := hnear.trans_lt (hv01.trans hv1)
    have hvsq : p.2 ^ 2 < 1 := by
      simpa only [sq_abs, one_pow] using (sq_lt_sq₀ (abs_nonneg p.2) zero_le_one).mpr hvlt
    have hrootpos : 0 < Real.sqrt (1 - p.2 ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hvsq)
    have hunit : ‖a p.2 • p.1‖ = 1 := by
      rw [hn, ha, ← hroot, inv_mul_cancel₀ hrootpos.ne']
    rw [hM, hbfar _ (by rw [hunit]; exact hrOne.le), one_mul, ha]


theorem stackCanonicalModel_flat_disc
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    (∀ x : E2, ‖x‖ ≤ rFlat →
      M (heightCoordinates (southSpherePoint x : E3)) = (x, -1)) ∧
    (((fun q : UnitTwoSphere => M (heightCoordinates (q : E3))) '' Qminus) ∩
      (closedBall (0 : E2) rFlat ×ˢ (univ : Set ℝ))) =
        closedBall (0 : E2) rFlat ×ˢ ({-1} : Set ℝ) := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  change (∀ x : E2, ‖x‖ ≤ rFlat →
    M (heightCoordinates (southSpherePoint x : E3)) = (x, -1)) ∧
    (((fun q : UnitTwoSphere => M (heightCoordinates (q : E3))) '' Qminus) ∩
      (closedBall (0 : E2) rFlat ×ˢ (univ : Set ℝ))) =
        closedBall (0 : E2) rFlat ×ˢ ({-1} : Set ℝ)
  obtain ⟨_, _, _, _, _, hafar, _⟩ := stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  have hgeom := stackCanonicalModel_southern_geometry
    rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  have hdisc (x : E2) (hx : ‖x‖ ≤ rFlat) :
      M (heightCoordinates (southSpherePoint x : E3)) = (x, -1) := by
    have hxlt : ‖x‖ < 1 := hx.trans_lt (hradii.trans hrOne)
    have hcoord := southSpherePoint_coordinates x hxlt
    have hxsq : ‖x‖ ^ 2 < rOne ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg x) (hrFlat.le.trans hradii.le)).mpr (hx.trans_lt hradii)
    have hsqrt : (Real.sqrt (1 - ‖x‖ ^ 2)) ^ 2 = 1 - ‖x‖ ^ 2 :=
      Real.sq_sqrt (by nlinarith [norm_nonneg x])
    have ha : a (-Real.sqrt (1 - ‖x‖ ^ 2)) = 1 := by
      apply hafar
      rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply (sq_le_sq₀ (hv0.le.trans hv01.le) (Real.sqrt_nonneg _)).mp
      linarith only [hsqrt, hxsq, hgap]
    have hnorm : ‖(M (heightCoordinates (southSpherePoint x : E3))).1‖ ≤ rFlat := by
      simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos a a 0 le_rfl,
        hcoord, ha, one_smul]
      exact hx
    have hh : (heightCoordinates (southSpherePoint x : E3)).2 ≤ 0 := by
      rw [hcoord]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    have h := (hgeom _ (sphere_height_coordinates_sq (southSpherePoint x)) hh).2.2.2.2.1 hnorm
    simpa only [hcoord] using h
  refine ⟨hdisc, ?_⟩
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hp⟩
    have hflat := (hgeom _ (sphere_height_coordinates_sq q) hq).2.2.2.2.1
      (mem_closedBall_zero_iff.mp hp.1)
    refine ⟨hp.1, ?_⟩
    change (M (heightCoordinates (q : E3))).2 = -1
    exact congrArg Prod.snd hflat
  · intro hp
    have hx : ‖p.1‖ ≤ rFlat := mem_closedBall_zero_iff.mp hp.1
    have hz : p.2 = -1 := hp.2
    refine ⟨⟨southSpherePoint p.1, ?_, ?_⟩, hp.1, mem_univ _⟩
    · change (heightCoordinates (southSpherePoint p.1 : E3)).2 ≤ 0
      rw [southSpherePoint_coordinates _ (hx.trans_lt (hradii.trans hrOne))]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    · change M (heightCoordinates (southSpherePoint p.1 : E3)) = p
      rw [hdisc _ hx]
      exact Prod.ext rfl hz.symm


theorem stackCanonicalModel_reflection_height
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    (∀ p : E2 × ℝ, M (p.1, -p.2) = ((M p).1, -(M p).2)) ∧
    ∀ p : E2 × ℝ, ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 → |(M p).2| ≤ 1 := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  change (∀ p : E2 × ℝ, M (p.1, -p.2) = ((M p).1, -(M p).2)) ∧
    ∀ p : E2 × ℝ, ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 → |(M p).2| ≤ 1
  obtain ⟨_, _, _, _, _, _, haeven⟩ := stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  have hreflection (p : E2 × ℝ) : M (p.1, -p.2) = ((M p).1, -(M p).2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
    have ha : a (-p.2) = a p.2 := haeven p.2
    rw [ha, mul_neg]
  refine ⟨hreflection, ?_⟩
  intro p hp
  have hgeom := stackCanonicalModel_southern_geometry
    rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  by_cases hv : p.2 ≤ 0
  · obtain ⟨_, _, hlo, hhi, _, _⟩ := hgeom p hp hv
    exact abs_le.mpr ⟨hlo, hhi.trans zero_le_one⟩
  · have hsp : ‖p.1‖ ^ 2 + (-p.2) ^ 2 = 1 := by simpa only [neg_sq] using hp
    obtain ⟨_, _, hlo, hhi, _, _⟩ := hgeom (p.1, -p.2) hsp (by linarith only [lt_of_not_ge hv])
    change -1 ≤ (M (p.1, -p.2)).2 at hlo
    change (M (p.1, -p.2)).2 ≤ 0 at hhi
    rw [hreflection] at hlo hhi
    exact abs_le.mpr ⟨by linarith only [hhi], by linarith only [hlo]⟩


theorem exists_stackCanonicalRadii (d : ℝ) (hd : 0 < d) :
    ∃ rFlat rOne v0 v1 : ℝ,
      0 < rFlat ∧ 1 - d < rFlat ∧ rFlat < rOne ∧ rOne < 1 ∧
      0 < v0 ∧ v0 < v1 ∧ v1 < 1 ∧ v1 ^ 2 + rOne ^ 2 < 1 := by
  let e := min d (1 / 2)
  let rFlat := 1 - e / 2
  let rOne := (rFlat + 1) / 2
  let v1 := (1 - rOne) / 2
  let v0 := v1 / 2
  have hepos : 0 < e := lt_min hd (by norm_num)
  have hed : e ≤ d := min_le_left _ _
  have hehalf : e ≤ 1 / 2 := min_le_right _ _
  have hrf : 0 < rFlat := by dsimp only [rFlat]; linarith
  have hrfr : rFlat < rOne := by dsimp only [rOne, rFlat]; linarith
  have hrone : rOne < 1 := by dsimp only [rOne, rFlat]; linarith
  have hronepos : 0 < rOne := hrf.trans hrfr
  have hv1 : 0 < v1 := by dsimp only [v1]; linarith
  have hv1lt : v1 < 1 := by dsimp only [v1]; linarith
  refine ⟨rFlat, rOne, v0, v1, hrf, ?_, hrfr, hrone, ?_, ?_, hv1lt, ?_⟩
  · dsimp only [rFlat]
    linarith
  · dsimp only [v0]
    linarith
  · dsimp only [v0]
    linarith
  · have hq : 0 < (1 - rOne) * rOne := mul_pos (sub_pos.mpr hrone) hronepos
    dsimp only [v1]
    nlinarith

end PoincareConjecture.M25.Topology3D
