import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CollarAbsorption
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue







set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.M25.Topology3D

theorem collarProfileCutoff_nonneg (b₁ b h : ℝ) : 0 ≤ collarCutoff b₁ b h :=
  (collarCutoff_mem_Icc b₁ b h).1

theorem collarProfileCutoff_monotone {b₁ b : ℝ} (hb : b₁ < b) :
    Monotone (collarCutoff b₁ b) := by
  intro h₁ h₂ hle
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

structure CollarProfileParams where
  a : ℝ
  ε : ℝ
  b₁ : ℝ
  b : ℝ
  a_pos : 0 < a
  a_lt_one : a < 1
  ε_pos : 0 < ε
  ε_lt_one : ε < 1
  b₁_bound : a / (1 - ε) ≤ b₁
  b₁_lt_b : b₁ < b
  b_lt_one : b < 1

noncomputable def standardCollarProfileParams {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    CollarProfileParams where
  a := a
  ε := (1 - a) / 2
  b₁ := (1 + a) / 2
  b := (3 + a) / 4
  a_pos := ha.1
  a_lt_one := ha.2
  ε_pos := by linarith [ha.2]
  ε_lt_one := by linarith [ha.1]
  b₁_bound := by
    rw [div_le_iff₀ (by linarith [ha.1])]
    nlinarith [sq_nonneg (1 - a)]
  b₁_lt_b := by linarith [ha.2]
  b_lt_one := by linarith [ha.2]

noncomputable def collarWeight (a ε b₁ b h : ℝ) : ℝ :=
  ε + collarCutoff b₁ b h * (1 - a / h - ε)

theorem collarWeight_eq_of_le {a ε b₁ b h : ℝ} (hb : b₁ < b) (hh : h ≤ b₁) :
    collarWeight a ε b₁ b h = ε := by
  rw [collarWeight, collarCutoff_eq_zero hb hh]
  ring

theorem collarWeight_eq_of_ge {a ε b₁ b h : ℝ} (hb : b₁ < b) (hh : b ≤ h) :
    collarWeight a ε b₁ b h = 1 - a / h := by
  rw [collarWeight, collarCutoff_eq_one hb hh]
  ring

noncomputable def collarProfile (P : CollarProfileParams) (h : ℝ) : ℝ :=
  P.a + h * collarWeight P.a P.ε P.b₁ P.b h
namespace CollarProfileParams
variable (P : CollarProfileParams)

theorem one_sub_ε_pos : 0 < 1 - P.ε := by linarith [P.ε_lt_one]

theorem b₁_pos : 0 < P.b₁ :=
  lt_of_lt_of_le (div_pos P.a_pos P.one_sub_ε_pos) P.b₁_bound

theorem b_pos : 0 < P.b := lt_trans P.b₁_pos P.b₁_lt_b

theorem div_le_of_b₁_le {h : ℝ} (hh : P.b₁ ≤ h) : P.a / h ≤ 1 - P.ε := by
  have hpos : 0 < h := lt_of_lt_of_le P.b₁_pos hh
  rw [div_le_iff₀ hpos]
  have := (div_le_iff₀ P.one_sub_ε_pos).1 (P.b₁_bound.trans hh)
  linarith

theorem weight_factor_nonneg {h : ℝ} (hh : P.b₁ ≤ h) : 0 ≤ 1 - P.a / h - P.ε := by
  linarith [P.div_le_of_b₁_le hh]

theorem collarWeight_ge (h : ℝ) : P.ε ≤ collarWeight P.a P.ε P.b₁ P.b h := by
  rcases le_or_gt h P.b₁ with hh | hh
  · rw [collarWeight_eq_of_le P.b₁_lt_b hh]
  · unfold collarWeight
    have := mul_nonneg (collarProfileCutoff_nonneg P.b₁ P.b h)
      (P.weight_factor_nonneg hh.le)
    linarith

theorem collarWeight_pos (h : ℝ) : 0 < collarWeight P.a P.ε P.b₁ P.b h :=
  lt_of_lt_of_le P.ε_pos (P.collarWeight_ge h)

theorem collarWeight_monotone : Monotone (collarWeight P.a P.ε P.b₁ P.b) := by
  intro h₁ h₂ hle
  rcases le_or_gt h₁ P.b₁ with h1 | h1
  · rw [collarWeight_eq_of_le P.b₁_lt_b h1]
    exact P.collarWeight_ge h₂
  · unfold collarWeight
    have hc := collarProfileCutoff_monotone P.b₁_lt_b hle
    have hf : 1 - P.a / h₁ - P.ε ≤ 1 - P.a / h₂ - P.ε := by
      have hpos : 0 < h₁ := lt_trans P.b₁_pos h1
      have : P.a / h₂ ≤ P.a / h₁ := div_le_div_of_nonneg_left P.a_pos.le hpos hle
      linarith
    have := mul_le_mul hc hf (P.weight_factor_nonneg h1.le)
      (collarProfileCutoff_nonneg _ _ _)
    linarith

theorem contDiff_collarWeight : ContDiff ℝ ∞ (collarWeight P.a P.ε P.b₁ P.b) := by
  rw [contDiff_iff_contDiffAt]
  intro h
  rcases lt_or_ge h P.b₁ with hh | hh
  · have hev : collarWeight P.a P.ε P.b₁ P.b =ᶠ[𝓝 h] fun _ => P.ε := by
      filter_upwards [Iio_mem_nhds hh] with y hy
      exact collarWeight_eq_of_le P.b₁_lt_b hy.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hne : h ≠ 0 := (lt_of_lt_of_le P.b₁_pos hh).ne'
    unfold collarWeight
    apply contDiffAt_const.add
    apply ((contDiff_collarCutoff P.b₁ P.b).contDiffAt).mul
    apply ContDiffAt.sub _ contDiffAt_const
    apply contDiffAt_const.sub
    exact contDiffAt_const.div contDiffAt_id hne

theorem collarProfile_eq_of_le {h : ℝ} (hh : h ≤ P.b₁) :
    collarProfile P h = P.a + h * P.ε := by
  rw [collarProfile, collarWeight_eq_of_le P.b₁_lt_b hh]

theorem collarProfile_eq_self {h : ℝ} (hh : P.b ≤ h) : collarProfile P h = h := by
  have hne : h ≠ 0 := (lt_of_lt_of_le P.b_pos hh).ne'
  rw [collarProfile, collarWeight_eq_of_ge P.b₁_lt_b hh]
  field_simp
  ring

theorem collarProfile_zero : collarProfile P 0 = P.a := by
  rw [P.collarProfile_eq_of_le P.b₁_pos.le]
  ring

theorem collarProfile_one : collarProfile P 1 = 1 :=
  P.collarProfile_eq_self P.b_lt_one.le

theorem collarProfile_strictMono : StrictMono (collarProfile P) := by
  intro h₁ h₂ hlt
  unfold collarProfile
  have hw₁ := P.collarWeight_pos h₁
  have hmono := P.collarWeight_monotone hlt.le
  rcases le_or_gt h₂ P.b₁ with h2 | h2
  · rw [collarWeight_eq_of_le P.b₁_lt_b h2,
      collarWeight_eq_of_le P.b₁_lt_b (hlt.le.trans h2)]
    have := mul_lt_mul_of_pos_right hlt P.ε_pos
    linarith
  · rcases le_or_gt h₁ P.b₁ with h1 | h1
    · rw [collarWeight_eq_of_le P.b₁_lt_b h1]
      have hpos : 0 < h₂ := lt_trans P.b₁_pos h2
      have h₁ε := mul_lt_mul_of_pos_right hlt P.ε_pos
      have h₂w := mul_le_mul_of_nonneg_left (P.collarWeight_ge h₂) hpos.le
      linarith
    · have hpos : 0 < h₁ := lt_trans P.b₁_pos h1
      have h₁w := mul_lt_mul_of_pos_right hlt hw₁
      have h₂w := mul_le_mul_of_nonneg_left hmono (lt_trans hpos hlt).le
      linarith

theorem contDiff_collarProfile : ContDiff ℝ ∞ (collarProfile P) := by
  unfold collarProfile
  exact contDiff_const.add (contDiff_id.mul P.contDiff_collarWeight)

theorem collarProfile_surjective : Function.Surjective (collarProfile P) := by
  intro y
  have hcont := P.contDiff_collarProfile.continuous
  set x₁ : ℝ := min P.b₁ ((y - P.a) / P.ε) with hx₁
  set x₂ : ℝ := max P.b y with hx₂
  have hx₁b : x₁ ≤ P.b₁ := min_le_left _ _
  have hx₂b : P.b ≤ x₂ := le_max_left _ _
  have hle : x₁ ≤ x₂ := hx₁b.trans (P.b₁_lt_b.le.trans hx₂b)
  have hlo : collarProfile P x₁ ≤ y := by
    rw [P.collarProfile_eq_of_le hx₁b]
    have : x₁ ≤ (y - P.a) / P.ε := min_le_right _ _
    have := mul_le_mul_of_nonneg_right this P.ε_pos.le
    rw [div_mul_cancel₀ _ P.ε_pos.ne'] at this
    linarith
  have hhi : y ≤ collarProfile P x₂ := by
    rw [P.collarProfile_eq_self hx₂b]
    exact le_max_right _ _
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hle hcont.continuousOn ⟨hlo, hhi⟩
  exact ⟨x, hx⟩

noncomputable def collarProfileOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (collarProfile P)
    P.collarProfile_strictMono P.collarProfile_surjective

theorem collarProfile_image_Ioo :
    collarProfile P '' Ioo 0 1 = Ioo P.a 1 := by
  have h := P.collarProfileOrderIso.image_Ioo 0 1
  simp only [collarProfileOrderIso, StrictMono.coe_orderIsoOfSurjective] at h
  rw [h, P.collarProfile_zero, P.collarProfile_one]

theorem hasDerivAt_collarProfile (h : ℝ) :
    HasDerivAt (collarProfile P)
      (collarWeight P.a P.ε P.b₁ P.b h + h * deriv (collarWeight P.a P.ε P.b₁ P.b) h) h := by
  have hw : HasDerivAt (collarWeight P.a P.ε P.b₁ P.b)
      (deriv (collarWeight P.a P.ε P.b₁ P.b) h) h :=
    ((P.contDiff_collarWeight.differentiable (by simp)) h).hasDerivAt
  have h1 : HasDerivAt (fun x : ℝ => x * collarWeight P.a P.ε P.b₁ P.b x)
      (1 * collarWeight P.a P.ε P.b₁ P.b h + h * deriv (collarWeight P.a P.ε P.b₁ P.b) h) h :=
    (hasDerivAt_id h).mul hw
  have h2 : HasDerivAt (fun x : ℝ => P.a + x * collarWeight P.a P.ε P.b₁ P.b x)
      (1 * collarWeight P.a P.ε P.b₁ P.b h + h * deriv (collarWeight P.a P.ε P.b₁ P.b) h) h :=
    h1.const_add P.a
  rw [one_mul] at h2
  exact h2

theorem deriv_collarWeight_nonneg (h : ℝ) :
    0 ≤ deriv (collarWeight P.a P.ε P.b₁ P.b) h := by
  exact P.collarWeight_monotone.deriv_nonneg

theorem collarProfile_deriv_pos (h : ℝ) :
    0 < collarWeight P.a P.ε P.b₁ P.b h + h * deriv (collarWeight P.a P.ε P.b₁ P.b) h := by
  rcases lt_or_ge h P.b₁ with hh | hh
  · have hev : collarWeight P.a P.ε P.b₁ P.b =ᶠ[𝓝 h] fun _ => P.ε := by
      filter_upwards [Iio_mem_nhds hh] with y hy
      exact collarWeight_eq_of_le P.b₁_lt_b hy.le
    rw [hev.deriv_eq, deriv_const, mul_zero, add_zero]
    exact P.collarWeight_pos h
  · have hpos : 0 ≤ h := (lt_of_lt_of_le P.b₁_pos hh).le
    have := mul_nonneg hpos (P.deriv_collarWeight_nonneg h)
    linarith [P.collarWeight_pos h]

noncomputable def collarProfileDiffeomorph : ℝ ≃ₘ[ℝ] ℝ := by
  let e : ℝ ≃ₜ ℝ := P.collarProfileOrderIso.toHomeomorph
  have he : ContDiff ℝ ∞ (e : ℝ → ℝ) := P.contDiff_collarProfile
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := he.contMDiff
      contMDiff_invFun := ?_ }
  apply ContDiff.contMDiff
  exact e.contDiff_symm_deriv (fun x => (P.collarProfile_deriv_pos x).ne')
    (fun x => P.hasDerivAt_collarProfile x) he


@[simp] theorem collarProfileDiffeomorph_apply (h : ℝ) :
    P.collarProfileDiffeomorph h = collarProfile P h := rfl
end CollarProfileParams

theorem exists_tail_profile (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ φ : ℝ ≃ₘ[ℝ] ℝ, ∃ b ∈ Ioo (0 : ℝ) 1,
      φ '' Ioo 0 1 = (if side then Ioo a 1 else Ioo 0 a) ∧
      ∀ h : ℝ, (if side then b ≤ h else h ≤ b) → φ h = h := by
  cases side
  · let ha' : (1 - a) ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨by linarith [ha.2], by linarith [ha.1]⟩
    let P := standardCollarProfileParams ha'
    let R : ℝ ≃ₘ[ℝ] ℝ :=
      { toEquiv :=
          { toFun := fun h => 1 - h
            invFun := fun h => 1 - h
            left_inv := by intro h; ring
            right_inv := by intro h; ring }
        contMDiff_toFun := (contDiff_const.sub contDiff_id).contMDiff
        contMDiff_invFun := (contDiff_const.sub contDiff_id).contMDiff }
    let φ : ℝ ≃ₘ[ℝ] ℝ := (R.trans P.collarProfileDiffeomorph).trans R
    have hφ (h : ℝ) : φ h = 1 - P.collarProfileDiffeomorph (1 - h) := rfl
    refine ⟨φ, 1 - P.b, ⟨by linarith [P.b_lt_one], by linarith [P.b_pos]⟩, ?_, ?_⟩
    · rw [show (if false then Ioo a 1 else Ioo 0 a) = Ioo 0 a by rfl]
      ext y
      constructor
      · rintro ⟨h, hh, rfl⟩
        have hp0 : P.collarProfileDiffeomorph (1 - h) ∈ Ioo P.a 1 := by
          rw [← P.collarProfile_image_Ioo]
          exact ⟨1 - h, ⟨by linarith [hh.2], by linarith [hh.1]⟩, rfl⟩
        have hp : P.collarProfileDiffeomorph (1 - h) ∈ Ioo (1 - a) 1 := by
          change (1 - a < P.collarProfileDiffeomorph (1 - h) ∧
            P.collarProfileDiffeomorph (1 - h) < 1) at hp0
          exact hp0
        rw [hφ]
        exact ⟨by linarith [hp.2], by linarith [hp.1]⟩
      · intro hy
        have hp0 : 1 - y ∈ Ioo P.a 1 := by
          change 1 - y ∈ Ioo (1 - a) 1
          exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
        rw [← P.collarProfile_image_Ioo] at hp0
        obtain ⟨h, hh, he⟩ := hp0
        refine ⟨1 - h, ⟨by linarith [hh.2], by linarith [hh.1]⟩, ?_⟩
        rw [hφ]
        have harg : (1 : ℝ) - (1 - h) = h := by ring
        rw [harg]
        change 1 - P.collarProfileDiffeomorph h = y
        have he' : P.collarProfileDiffeomorph h = 1 - y := by
          simpa only [P.collarProfileDiffeomorph_apply] using he
        rw [he']
        ring
    · intro h hh
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      have hP : P.b ≤ 1 - h := by linarith [hh]
      change 1 - P.collarProfileDiffeomorph (1 - h) = h
      rw [P.collarProfileDiffeomorph_apply, P.collarProfile_eq_self hP]
      ring
  · let P := standardCollarProfileParams ha
    refine ⟨P.collarProfileDiffeomorph, P.b, ⟨P.b_pos, P.b_lt_one⟩, ?_, ?_⟩
    · simp only [↓reduceIte]
      exact P.collarProfile_image_Ioo
    · intro h hh
      simp only [↓reduceIte] at hh
      exact P.collarProfile_eq_self hh
end PoincareConjecture.M25.Topology3D
