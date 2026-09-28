import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CollarAbsorption
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Topology.Algebra.Order.Field













set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
open PoincareConjecture.M25.Topology3D

namespace Real




noncomputable def positiveRadialDerivative (f : ℝ → ℝ) (m u b s : ℝ) : ℝ :=
  (1 - collarCutoff m u s) * deriv f s + collarCutoff m u s * ((b - s)⁻¹) ^ 2




noncomputable def positiveRadialPrimitive (f : ℝ → ℝ) (l m u b s : ℝ) : ℝ :=
  f l + ∫ t in l..s, positiveRadialDerivative f m u b t

variable {f : ℝ → ℝ} {L l m u U b s : ℝ}



theorem positiveRadialDerivative_eq_deriv (hmu : m < u) (hs : s ≤ m) :
    positiveRadialDerivative f m u b s = deriv f s := by
  simp [positiveRadialDerivative, collarCutoff_eq_zero hmu hs]




theorem positiveRadialDerivative_eq_inv_sq (hmu : m < u) (hs : u ≤ s) :
    positiveRadialDerivative f m u b s = ((b - s)⁻¹) ^ 2 := by
  simp [positiveRadialDerivative, collarCutoff_eq_one hmu hs]





theorem contDiffOn_positiveRadialDerivative (hmu : m < u) (huU : u < U)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U)) :
    ContDiffOn ℝ ∞ (positiveRadialDerivative f m u b) (Ioo L b) := by
  apply isOpen_Ioo.contDiffOn_iff.mpr
  intro s hs
  have hB : ContDiffAt ℝ ∞ (fun t : ℝ => ((b - t)⁻¹) ^ 2) s :=
    ((contDiffAt_const.sub contDiffAt_id).inv (sub_ne_zero.mpr hs.2.ne')).pow 2
  by_cases hsu : s ≤ u
  · have hfs : ContDiffAt ℝ ∞ (deriv f) s :=
      (hf.deriv_of_isOpen isOpen_Ioo (by simp)).contDiffAt
        (isOpen_Ioo.mem_nhds ⟨hs.1, hsu.trans_lt huU⟩)
    exact ((contDiffAt_const.sub (contDiff_collarCutoff m u).contDiffAt).mul hfs).add
      ((contDiff_collarCutoff m u).contDiffAt.mul hB)
  · apply hB.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (lt_of_not_ge hsu)] with t ht
    exact positiveRadialDerivative_eq_inv_sq hmu ht.le




theorem positiveRadialDerivative_pos (hmu : m < u)
    (hfderiv : ∀ s ∈ Icc l u, 0 < deriv f s) (hs : s ∈ Ico l b) :
    0 < positiveRadialDerivative f m u b s := by
  have hB : 0 < ((b - s)⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr hs.2))
  by_cases hsu : s ≤ u
  · have hfd := hfderiv s ⟨hs.1, hsu⟩
    have hη := collarCutoff_mem_Icc m u s
    rcases hη.1.eq_or_lt with hzero | hpos
    · simp [positiveRadialDerivative, hzero.symm, hfd]
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr hη.2) hfd.le) (mul_pos hpos hB)
  · rw [positiveRadialDerivative_eq_inv_sq hmu (lt_of_not_ge hsu).le]
    exact hB




theorem intervalIntegrable_positiveRadialDerivative (hmu : m < u) (huU : u < U)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U)) (hl : l ∈ Ioo L b) (hs : s ∈ Ioo L b) :
    IntervalIntegrable (positiveRadialDerivative f m u b) volume l s :=
  ((contDiffOn_positiveRadialDerivative hmu huU hf).continuousOn.mono
    (ordConnected_Ioo.uIcc_subset hl hs)).intervalIntegrable




theorem hasDerivAt_positiveRadialPrimitive (hmu : m < u) (huU : u < U)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U)) (hl : l ∈ Ioo L b) (hs : s ∈ Ioo L b) :
    HasDerivAt (positiveRadialPrimitive f l m u b)
      (positiveRadialDerivative f m u b s) s := by
  have hH := (contDiffOn_positiveRadialDerivative (b := b) hmu huU hf).continuousOn
  exact (intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_positiveRadialDerivative hmu huU hf hl hs)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hH s hs)
    (hH.continuousAt (isOpen_Ioo.mem_nhds hs))).const_add (f l)




theorem contDiffOn_positiveRadialPrimitive (hmu : m < u) (huU : u < U)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U)) (hl : l ∈ Ioo L b) :
    ContDiffOn ℝ ∞ (positiveRadialPrimitive f l m u b) (Ioo L b) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mpr
  refine ⟨fun s hs =>
    (hasDerivAt_positiveRadialPrimitive hmu huU hf hl hs).differentiableAt.differentiableWithinAt,
    ?_⟩
  apply (contDiffOn_positiveRadialDerivative hmu huU hf).congr
  intro s hs
  exact (hasDerivAt_positiveRadialPrimitive hmu huU hf hl hs).deriv




@[simp] theorem positiveRadialPrimitive_apply_anchor (f : ℝ → ℝ) (l m u b : ℝ) :
    positiveRadialPrimitive f l m u b l = f l := by
  simp [positiveRadialPrimitive]




theorem positiveRadialPrimitive_eqOn (hLl : L < l) (hmu : m < u) (huU : u < U)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U)) :
    EqOn (positiveRadialPrimitive f l m u b) f (Icc l m) := by
  intro s hs
  have hsub : Icc l s ⊆ Ioo L U := fun t ht =>
    ⟨hLl.trans_le ht.1, (ht.2.trans hs.2).trans_lt (hmu.trans huU)⟩
  have hcongr : (∫ t in l..s, positiveRadialDerivative f m u b t) =
      ∫ t in l..s, deriv f t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs.1]
    exact fun t ht => positiveRadialDerivative_eq_deriv hmu (ht.2.trans hs.2)
  rw [positiveRadialPrimitive, hcongr,
    intervalIntegral.integral_deriv_of_contDiffOn_Icc ((hf.mono hsub).of_le (by simp)) hs.1]
  ring




theorem strictMonoOn_positiveRadialPrimitive (hLl : L < l) (hmu : m < u)
    (huU : u < U) (hlb : l < b) (hf : ContDiffOn ℝ ∞ f (Ioo L U))
    (hfderiv : ∀ s ∈ Icc l u, 0 < deriv f s) :
    StrictMonoOn (positiveRadialPrimitive f l m u b) (Ico l b) := by
  have hsub : Ico l b ⊆ Ioo L b := fun _ hx => ⟨hLl.trans_le hx.1, hx.2⟩
  apply strictMonoOn_of_deriv_pos (convex_Ico l b)
    ((contDiffOn_positiveRadialPrimitive hmu huU hf ⟨hLl, hlb⟩).continuousOn.mono hsub)
  intro s hs
  have hs' := interior_subset hs
  rw [(hasDerivAt_positiveRadialPrimitive hmu huU hf ⟨hLl, hlb⟩ (hsub hs')).deriv]
  exact positiveRadialDerivative_pos hmu hfderiv hs'




theorem deriv_positiveRadialPrimitive_pos (hLl : L < l) (hmu : m < u)
    (huU : u < U) (hlb : l < b) (hf : ContDiffOn ℝ ∞ f (Ioo L U))
    (hfderiv : ∀ s ∈ Icc l u, 0 < deriv f s) (hs : s ∈ Ico l b) :
    0 < deriv (positiveRadialPrimitive f l m u b) s := by
  rw [(hasDerivAt_positiveRadialPrimitive hmu huU hf ⟨hLl, hlb⟩
    ⟨hLl.trans_le hs.1, hs.2⟩).deriv]
  exact positiveRadialDerivative_pos hmu hfderiv hs



theorem positiveRadialPrimitive_pos (hLl : L < l) (hmu : m < u)
    (huU : u < U) (hlb : l < b) (hf : ContDiffOn ℝ ∞ f (Ioo L U))
    (hfderiv : ∀ s ∈ Icc l u, 0 < deriv f s) (hfpos : 0 < f l)
    (hs : s ∈ Ico l b) : 0 < positiveRadialPrimitive f l m u b s := by
  have hmono := (strictMonoOn_positiveRadialPrimitive hLl hmu huU hlb hf hfderiv).monotoneOn
  have hle := hmono (show l ∈ Ico l b from ⟨le_rfl, hlb⟩) hs hs.1
  rw [positiveRadialPrimitive_apply_anchor] at hle
  exact hfpos.trans_le hle




theorem positiveRadialPrimitive_upper_formula (hLl : L < l) (hlm : l < m)
    (hmu : m < u) (huU : u < U) (hub : u < b)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U)) (hs : s ∈ Ico u b) :
    positiveRadialPrimitive f l m u b s =
      positiveRadialPrimitive f l m u b u + (b - s)⁻¹ - (b - u)⁻¹ := by
  have hLu : L < u := (hLl.trans hlm).trans hmu
  have hl : l ∈ Ioo L b := ⟨hLl, ((hlm.trans hmu).trans hub)⟩
  have hu : u ∈ Ioo L b := ⟨hLu, hub⟩
  have hs' : s ∈ Ioo L b := ⟨hLu.trans_le hs.1, hs.2⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_positiveRadialDerivative hmu huU hf hl hu)
    (intervalIntegrable_positiveRadialDerivative hmu huU hf hu hs')
  have hcongr : (∫ t in u..s, positiveRadialDerivative f m u b t) =
      ∫ t in u..s, ((b - t)⁻¹) ^ 2 := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs.1]
    exact fun t ht => positiveRadialDerivative_eq_inv_sq hmu ht.1
  have hBint : IntervalIntegrable (fun t : ℝ => ((b - t)⁻¹) ^ 2) volume u s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs.1
    intro t ht
    exact (((continuousAt_const.sub continuousAt_id).inv₀
      (sub_ne_zero.mpr (ht.2.trans_lt hs.2).ne')).pow 2).continuousWithinAt
  have hA : ∀ t ∈ uIcc u s, HasDerivAt (fun z : ℝ => (b - z)⁻¹)
      (((b - t)⁻¹) ^ 2) t := by
    rw [uIcc_of_le hs.1]
    intro t ht
    simpa only [id_eq, Pi.inv_apply, neg_neg, one_div, inv_pow] using!
      ((hasDerivAt_id t).const_sub b).inv (sub_ne_zero.mpr (ht.2.trans_lt hs.2).ne')
  have hBprimitive := intervalIntegral.integral_eq_sub_of_hasDerivAt hA hBint
  simp only [positiveRadialPrimitive]
  rw [← hsplit, hcongr, hBprimitive]
  ring

end Real
