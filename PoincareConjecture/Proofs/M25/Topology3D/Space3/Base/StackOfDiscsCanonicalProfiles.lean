import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfilePath
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope








set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


noncomputable def stackCanonicalFactor (lo hi s : ℝ) : ℝ :=
  1 + (1 - Real.smoothTransition ((s - lo) / (hi - lo))) *
    ((Real.sqrt (1 - s))⁻¹ - 1)


theorem stackCanonicalFactor_spec (lo hi : ℝ)
    (hlohi : lo < hi) (hhi : hi < 1) :
    ContDiff ℝ ∞ (stackCanonicalFactor lo hi) ∧
    (∀ s, 0 < stackCanonicalFactor lo hi s) ∧
    (∀ s, s ≤ lo → stackCanonicalFactor lo hi s =
      (Real.sqrt (1 - s))⁻¹) ∧
    (∀ s, hi ≤ s → stackCanonicalFactor lo hi s = 1) ∧
    (∀ s, 0 ≤ s → 1 ≤ stackCanonicalFactor lo hi s) ∧
    ∀ s, 0 ≤ s → s < 1 → stackCanonicalFactor lo hi s ≤
      (Real.sqrt (1 - s))⁻¹ := by
  have hd : 0 < hi - lo := sub_pos.mpr hlohi
  let chi : ℝ → ℝ := fun s => 1 - Real.smoothTransition ((s - lo) / (hi - lo))
  have hchi : ContDiff ℝ ∞ chi := by
    dsimp only [chi]
    fun_prop
  have hfar (s : ℝ) (hs : hi ≤ s) : chi s = 0 := by
    have harg : 1 ≤ (s - lo) / (hi - lo) := (le_div_iff₀ hd).mpr (by linarith)
    dsimp only [chi]
    rw [Real.smoothTransition.one_of_one_le harg, sub_self]
  have hsupport : tsupport chi ⊆ Iio (1 : ℝ) := by
    have hs : Function.support chi ⊆ Iic hi := by
      intro s hs
      by_contra h
      exact hs (hfar s (le_of_lt (lt_of_not_ge h)))
    exact (closure_minimal hs isClosed_Iic).trans (fun _ hs => hs.trans_lt hhi)
  have hroot : ContDiffOn ℝ ∞ (fun s : ℝ => Real.sqrt (1 - s)) (Iio 1) :=
    (contDiff_const.sub contDiff_id).contDiffOn.sqrt
      (fun _ hs => (sub_pos.mpr hs).ne')
  have hinv : ContDiffOn ℝ ∞ (fun s : ℝ => (Real.sqrt (1 - s))⁻¹ - 1)
      (Iio 1) :=
    (hroot.inv (fun _ hs => (Real.sqrt_pos.mpr (sub_pos.mpr hs)).ne')).sub
      contDiffOn_const
  have hsmooth : ContDiff ℝ ∞ (stackCanonicalFactor lo hi) := by
    have h := contDiff_cutoff_smul isOpen_Iio chi hchi hsupport
      (fun s : ℝ => (Real.sqrt (1 - s))⁻¹ - 1) hinv
    exact contDiff_const.add h
  have hfarF (s : ℝ) (hs : hi ≤ s) : stackCanonicalFactor lo hi s = 1 := by
    change 1 + chi s * ((Real.sqrt (1 - s))⁻¹ - 1) = 1
    rw [hfar s hs, zero_mul, add_zero]
  have hbounds (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
      1 ≤ stackCanonicalFactor lo hi s ∧
        stackCanonicalFactor lo hi s ≤ (Real.sqrt (1 - s))⁻¹ := by
    have hr : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr (sub_pos.mpr hs1)
    have hrle : Real.sqrt (1 - s) ≤ 1 := by
      apply Real.sqrt_le_one.mpr
      linarith
    have hri : 1 ≤ (Real.sqrt (1 - s))⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hrle (inv_nonneg.mpr hr.le)
      simpa only [mul_inv_cancel₀ hr.ne', one_mul] using h
    have hS0 := Real.smoothTransition.nonneg ((s - lo) / (hi - lo))
    have hS1 := Real.smoothTransition.le_one ((s - lo) / (hi - lo))
    have hlow := mul_nonneg (sub_nonneg.mpr hS1) (sub_nonneg.mpr hri)
    have hupp := mul_nonneg hS0 (sub_nonneg.mpr hri)
    dsimp only [stackCanonicalFactor]
    constructor <;> nlinarith only [hlow, hupp]
  refine ⟨hsmooth, ?_, ?_, hfarF, ?_, fun s hs0 hs1 => (hbounds s hs0 hs1).2⟩
  · intro s
    by_cases hs : hi ≤ s
    · rw [hfarF s hs]
      exact zero_lt_one
    · have hs1 : s < 1 := (lt_of_not_ge hs).trans hhi
      have hr : 0 < (Real.sqrt (1 - s))⁻¹ :=
        inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hs1))
      have harg : (s - lo) / (hi - lo) < 1 :=
        (div_lt_one hd).mpr (by linarith [lt_of_not_ge hs])
      have hS := Real.smoothTransition.lt_one_of_lt_one harg
      have hS0 := Real.smoothTransition.nonneg ((s - lo) / (hi - lo))
      have hpos := mul_pos (sub_pos.mpr hS) hr
      dsimp only [stackCanonicalFactor]
      nlinarith only [hpos, hS0]
  · intro s hs
    have harg : (s - lo) / (hi - lo) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hd.le
    simp only [stackCanonicalFactor, Real.smoothTransition.zero_of_nonpos harg,
      sub_zero, one_mul]
    ring
  · intro s hs
    by_cases h : s < 1
    · exact (hbounds s hs h).1
    · rw [hfarF s (hhi.le.trans (le_of_not_gt h))]


noncomputable def stackCanonicalHorizontal (v0 v1 v : ℝ) : ℝ :=
  stackCanonicalFactor (v0 ^ 2) (v1 ^ 2) (v ^ 2)


noncomputable def stackCanonicalVertical (rFlat rOne : ℝ) (x : E2) : ℝ :=
  stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2) (‖x‖ ^ 2)


noncomputable def stackCanonicalMeridian
    (rFlat rOne v0 v1 v : ℝ) : ℝ × ℝ :=
  let R := stackCanonicalHorizontal v0 v1 v * Real.sqrt (1 - v ^ 2)
  (R, stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2) (R ^ 2) * v)


theorem stackCanonicalHorizontal_spec (v0 v1 : ℝ)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    ContDiff ℝ ∞ a ∧
    (∀ v, 0 < a v) ∧
    (∀ v, 1 ≤ a v) ∧
    (∀ v, |v| < 1 → a v ≤ (Real.sqrt (1 - v ^ 2))⁻¹) ∧
    (∀ v, |v| ≤ v0 → a v = (Real.sqrt (1 - v ^ 2))⁻¹) ∧
    (∀ v, v1 ≤ |v| → a v = 1) ∧
    ∀ v, a (-v) = a v := by
  have hv1pos : 0 < v1 := hv0.trans hv01
  have hsq : v0 ^ 2 < v1 ^ 2 := (sq_lt_sq₀ hv0.le hv1pos.le).mpr hv01
  have hsq1 : v1 ^ 2 < 1 := by
    have h := (sq_lt_sq₀ hv1pos.le zero_le_one).mpr hv1
    simpa only [one_pow] using h
  obtain ⟨hs, hp, hn, hf, hlow, hupp⟩ := stackCanonicalFactor_spec (v0 ^ 2) (v1 ^ 2) hsq hsq1
  refine ⟨hs.comp (contDiff_id.pow 2), fun v => hp _,
    fun v => hlow _ (sq_nonneg v), ?_, ?_, ?_, ?_⟩
  · intro v hv
    apply hupp _ (sq_nonneg v)
    have h := (sq_lt_sq₀ (abs_nonneg v) zero_le_one).mpr hv
    simpa only [sq_abs, one_pow] using h
  · intro v hv
    apply hn
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg v) hv0.le).mpr hv
  · intro v hv
    apply hf
    simpa only [sq_abs] using (sq_le_sq₀ hv1pos.le (abs_nonneg v)).mpr hv
  · intro v
    simp only [stackCanonicalHorizontal, neg_sq]


theorem stackCanonicalVertical_spec (rFlat rOne : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1) :
    let b := stackCanonicalVertical rFlat rOne
    ContDiff ℝ ∞ b ∧
    (∀ x, 0 < b x) ∧
    (∀ x, 1 ≤ b x) ∧
    (∀ x, ‖x‖ ≤ rFlat → b x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹) ∧
    (∀ x, rOne ≤ ‖x‖ → b x = 1) ∧
    ∀ x y, ‖x‖ = ‖y‖ → b x = b y := by
  have hrOnepos : 0 < rOne := hrFlat.trans hradii
  have hsq : rFlat ^ 2 < rOne ^ 2 := (sq_lt_sq₀ hrFlat.le hrOnepos.le).mpr hradii
  have hsq1 : rOne ^ 2 < 1 := by
    have h := (sq_lt_sq₀ hrOnepos.le zero_le_one).mpr hrOne
    simpa only [one_pow] using h
  obtain ⟨hs, hp, hn, hf, hlow, _⟩ :=
    stackCanonicalFactor_spec (rFlat ^ 2) (rOne ^ 2) hsq hsq1
  refine ⟨hs.comp (contDiff_id.norm_sq ℝ), fun x => hp _,
    fun x => hlow _ (sq_nonneg ‖x‖), ?_, ?_, ?_⟩
  · intro x hx
    exact hn _ ((sq_le_sq₀ (norm_nonneg x) hrFlat.le).mpr hx)
  · intro x hx
    exact hf _ ((sq_le_sq₀ hrOnepos.le (norm_nonneg x)).mpr hx)
  · intro x y hxy
    simp only [stackCanonicalVertical, hxy]

end PoincareConjecture.M25.Topology3D
