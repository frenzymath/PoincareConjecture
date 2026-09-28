import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointCutoff
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMinimum













set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint




noncomputable def transverseTimeAmplitude (R epsilon z : ℝ) : ℝ :=
  max 0 ((epsilon / R) * (R - |z|))




noncomputable def signedTimeCutoff (R epsilon t z : ℝ) : ℝ :=
  max (-transverseTimeAmplitude R epsilon z)
    (min t (transverseTimeAmplitude R epsilon z))



theorem transverseTimeAmplitude_mem {R epsilon : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (z : ℝ) :
    transverseTimeAmplitude R epsilon z ∈ Icc 0 epsilon := by
  refine ⟨le_max_left _ _, max_le hepsilon ?_⟩
  calc
    (epsilon / R) * (R - |z|) ≤ (epsilon / R) * R :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (abs_nonneg _))
        (div_nonneg hepsilon hR.le)
    _ = epsilon := div_mul_cancel₀ _ hR.ne'



theorem signedTimeCutoff_mem {R epsilon : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (t z : ℝ) :
    signedTimeCutoff R epsilon t z ∈ Icc (-epsilon) epsilon := by
  have ha := transverseTimeAmplitude_mem hR hepsilon z
  refine ⟨(neg_le_neg ha.2).trans (le_max_left _ _), ?_⟩
  exact max_le ((neg_nonpos.mpr ha.1).trans hepsilon)
    ((min_le_right _ _).trans ha.2)



theorem signedTimeCutoff_core {R epsilon t : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (ht : t ∈ Icc (-epsilon) epsilon) :
    signedTimeCutoff R epsilon t 0 = t := by
  have ha : transverseTimeAmplitude R epsilon 0 = epsilon := by
    simp only [transverseTimeAmplitude, abs_zero, sub_zero,
      div_mul_cancel₀ _ hR.ne', max_eq_right hepsilon]
  rw [signedTimeCutoff, ha, min_eq_left ht.2, max_eq_right ht.1]




theorem signedTimeCutoff_eq_zero_of_radius_le {R epsilon : ℝ}
    (hR : 0 < R) (hepsilon : 0 ≤ epsilon) (t z : ℝ) (hz : R ≤ |z|) :
    signedTimeCutoff R epsilon t z = 0 := by
  have ha : transverseTimeAmplitude R epsilon z = 0 := by
    exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg hepsilon hR.le) (sub_nonpos.mpr hz))
  simp only [signedTimeCutoff, ha, neg_zero, max_eq_left (min_le_right t 0)]



theorem signedTimeCutoff_at_zero {R epsilon : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (z : ℝ) :
    signedTimeCutoff R epsilon 0 z = 0 := by
  have ha := (transverseTimeAmplitude_mem hR hepsilon z).1
  simp only [signedTimeCutoff, min_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]



theorem transverseTimeAmplitude_abs_sub_le {R epsilon : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (z w : ℝ) :
    |transverseTimeAmplitude R epsilon z - transverseTimeAmplitude R epsilon w| ≤
      (epsilon / R) * |z - w| := by
  have hratio : 0 ≤ epsilon / R := div_nonneg hepsilon hR.le
  apply (abs_max_sub_max_le_max 0 ((epsilon / R) * (R - |z|))
    0 ((epsilon / R) * (R - |w|))).trans
  apply max_le
  · simpa only [sub_self, abs_zero] using mul_nonneg hratio (abs_nonneg (z - w))
  · have heq : (epsilon / R) * (R - |z|) - (epsilon / R) * (R - |w|) =
        (epsilon / R) * (|w| - |z|) := by ring
    rw [heq, abs_mul, abs_of_nonneg hratio]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [abs_sub_comm w z] using abs_abs_sub_abs_le_abs_sub w z) hratio




theorem signedTimeCutoff_abs_sub_le {R epsilon : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (t z w : ℝ) :
    |signedTimeCutoff R epsilon t z - signedTimeCutoff R epsilon t w| ≤
      (epsilon / R) * |z - w| := by
  have ha := transverseTimeAmplitude_abs_sub_le hR hepsilon z w
  have hnonneg := mul_nonneg (div_nonneg hepsilon hR.le) (abs_nonneg (z - w))
  have hmin : |min t (transverseTimeAmplitude R epsilon z) -
      min t (transverseTimeAmplitude R epsilon w)| ≤ (epsilon / R) * |z - w| := by
    apply (abs_min_sub_min_le_max t _ t _).trans
    exact max_le (by simpa only [sub_self, abs_zero] using hnonneg) ha
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le ?_ hmin
  simpa only [neg_sub_neg, abs_sub_comm] using ha

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem signedTimeCutoff_finitePiecewiseAffineOn
    {S : Set E} {t z : E → ℝ} (ht : FinitePiecewiseAffineOn t S)
    (hz : FinitePiecewiseAffineOn z S) (R epsilon : ℝ) :
    FinitePiecewiseAffineOn (fun x => signedTimeCutoff R epsilon (t x) (z x)) S := by
  have hnegz : FinitePiecewiseAffineOn (fun x => -z x) S :=
    hz.postcomp (-ContinuousAffineMap.id ℝ ℝ)
  have habs : FinitePiecewiseAffineOn (fun x => |z x|) S := by
    apply (hz.positivePart.add hnegz.positivePart).congr
    intro x _
    change max 0 (z x) + max 0 (-z x) = |z x|
    by_cases hx : 0 ≤ z x
    · rw [max_eq_right hx, max_eq_left (neg_nonpos.mpr hx), add_zero, abs_of_nonneg hx]
    · have hx' : z x ≤ 0 := (lt_of_not_ge hx).le
      rw [max_eq_left hx', max_eq_right (neg_nonneg.mpr hx'), zero_add, abs_of_nonpos hx']
  have hamp : FinitePiecewiseAffineOn
      (fun x => transverseTimeAmplitude R epsilon (z x)) S :=
    (habs.postcomp ((epsilon / R) •
      (ContinuousAffineMap.const ℝ ℝ R - ContinuousAffineMap.id ℝ ℝ))).positivePart
  have hnegamp : FinitePiecewiseAffineOn
      (fun x => -transverseTimeAmplitude R epsilon (z x)) S :=
    hamp.postcomp (-ContinuousAffineMap.id ℝ ℝ)
  have hmin := ht.min hamp
  apply ((hmin.sub hnegamp).positivePart.add hnegamp).congr
  intro x _
  let a := transverseTimeAmplitude R epsilon (z x)
  change max 0 (min (t x) a - -a) + -a = max (-a) (min (t x) a)
  by_cases hx : -a ≤ min (t x) a
  · rw [max_eq_right (sub_nonneg.mpr hx), max_eq_right hx]
    ring
  · have hx' : min (t x) a ≤ -a := (lt_of_not_ge hx).le
    rw [max_eq_left (sub_nonpos.mpr hx'), max_eq_left hx', zero_add]

end PoincareConjecture.M76.ZeroChargeJoint
