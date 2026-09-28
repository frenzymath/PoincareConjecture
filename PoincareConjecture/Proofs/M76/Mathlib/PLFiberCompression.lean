import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd
import Mathlib.Topology.Order.IntermediateValue












set_option autoImplicit false

open Set Geometry

namespace PLFiberCompression




noncomputable def value (delta w t : ℝ) : ℝ :=
  delta * t + (1 - delta) * max (-w) (min t w)



theorem value_of_le_neg {delta w t : ℝ} (hw : 0 ≤ w) (ht : t ≤ -w) :
    value delta w t = delta * t - (1 - delta) * w := by
  rw [value, min_eq_left (by linarith), max_eq_left ht]
  ring



theorem value_of_mem {delta w t : ℝ} (ht : t ∈ Icc (-w) w) :
    value delta w t = t := by
  rw [value, min_eq_left ht.2, max_eq_right ht.1]
  ring



theorem value_of_width_le {delta w t : ℝ} (hw : 0 ≤ w) (ht : w ≤ t) :
    value delta w t = delta * t + (1 - delta) * w := by
  rw [value, min_eq_right ht, max_eq_right (by linarith)]



theorem value_zero_width (delta t : ℝ) : value delta 0 t = delta * t := by
  simp only [value, neg_zero, max_eq_left (min_le_right t 0), mul_zero, add_zero]



theorem continuous_value (delta : ℝ) :
    Continuous (fun z : ℝ × ℝ => value delta z.1 z.2) := by
  unfold value
  fun_prop




theorem strictMono_value {delta w : ℝ} (hd : 0 < delta) (hw : 0 ≤ w) :
    StrictMono (value delta w) := by
  intro a b hab
  by_cases ha : a ≤ -w
  · rw [value_of_le_neg hw ha]
    by_cases hb : b ≤ -w
    · rw [value_of_le_neg hw hb]
      nlinarith [mul_pos hd (sub_pos.mpr hab)]
    · by_cases hb' : b ≤ w
      · rw [value_of_mem ⟨le_of_not_ge hb, hb'⟩]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hd.le (show a + w ≤ 0 by linarith)]
      · rw [value_of_width_le hw (le_of_not_ge hb')]
        nlinarith [mul_pos hd (sub_pos.mpr hab),
          mul_nonpos_of_nonneg_of_nonpos hd.le (show a + w ≤ 0 by linarith),
          mul_nonneg hd.le (show 0 ≤ b - w by linarith)]
  · by_cases ha' : a ≤ w
    · rw [value_of_mem ⟨le_of_not_ge ha, ha'⟩]
      by_cases hb : b ≤ w
      · rw [value_of_mem ⟨by linarith, hb⟩]
        exact hab
      · rw [value_of_width_le hw (le_of_not_ge hb)]
        nlinarith [mul_pos hd (show 0 < b - w by linarith)]
    · rw [value_of_width_le hw (le_of_not_ge ha'),
        value_of_width_le hw (by linarith)]
      nlinarith [mul_pos hd (sub_pos.mpr hab)]




theorem inverse_value {delta w : ℝ} (hd : 0 < delta) (hw : 0 ≤ w) (t : ℝ) :
    value delta⁻¹ w (value delta w t) = t := by
  by_cases ht : t ≤ -w
  · have hv : value delta w t ≤ -w := by
      rw [value_of_le_neg hw ht]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hd.le (show t + w ≤ 0 by linarith)]
    rw [value_of_le_neg hw hv, value_of_le_neg hw ht]
    field_simp
    ring
  · by_cases ht' : t ≤ w
    · rw [value_of_mem ⟨le_of_not_ge ht, ht'⟩,
        value_of_mem ⟨le_of_not_ge ht, ht'⟩]
    · have hv : w ≤ value delta w t := by
        rw [value_of_width_le hw (le_of_not_ge ht')]
        nlinarith [mul_nonneg hd.le (show 0 ≤ t - w by linarith)]
      rw [value_of_width_le hw hv, value_of_width_le hw (le_of_not_ge ht')]
      field_simp
      ring




theorem image_unit_interval {delta w : ℝ} (hd : 0 < delta)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    value delta w '' Ioo (-1) 1 =
      Ioo (-(delta + (1 - delta) * w)) (delta + (1 - delta) * w) := by
  have hc : Continuous (value delta w) :=
    (continuous_value delta).comp (continuous_const.prodMk continuous_id)
  rw [hc.image_Ioo_of_strictMono (strictMono_value hd hw),
    value_of_le_neg hw (by linarith), value_of_width_le hw hw1]
  congr 1 <;> ring



theorem value_mem_unit_interval {delta w t : ℝ} (hd : 0 < delta)
    (hd1 : delta ≤ 1) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (ht : t ∈ Ioo (-1) 1) : value delta w t ∈ Ioo (-1) 1 := by
  have h := image_unit_interval hd hw hw1 ▸ mem_image_of_mem (value delta w) ht
  have htop : delta + (1 - delta) * w ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hw1)]
  exact ⟨lt_of_le_of_lt (by linarith) h.1, lt_of_lt_of_le h.2 htop⟩




theorem abs_value_le {delta w t : ℝ} (hd : 1 ≤ delta) (hw : 0 ≤ w) :
    |value delta w t| ≤ delta * |t| := by
  by_cases ht : t ≤ -w
  · rw [value_of_le_neg hw ht, abs_of_nonpos (show t ≤ 0 by linarith)]
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hd) hw,
      mul_nonneg (show 0 ≤ delta by linarith) (show 0 ≤ -t - w by linarith)]
  · by_cases ht' : t ≤ w
    · rw [value_of_mem ⟨le_of_not_ge ht, ht'⟩]
      nlinarith [mul_nonneg (sub_nonneg.mpr hd) (abs_nonneg t)]
    · rw [value_of_width_le hw (le_of_not_ge ht'),
        abs_of_nonneg (show 0 ≤ t by linarith)]
      apply abs_le.mpr
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hd) hw,
        mul_nonneg (show 0 ≤ delta by linarith) (show 0 ≤ t - w by linarith)]





noncomputable def homeomorph {X : Type*} [TopologicalSpace X]
    (delta : ℝ) (hd : 0 < delta) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : Continuous w) : (X × ℝ) ≃ₜ (X × ℝ) where
  toFun z := (z.1, value delta (w z.1) z.2)
  invFun z := (z.1, value delta⁻¹ (w z.1) z.2)
  left_inv z := Prod.ext rfl (inverse_value hd (hw z.1) z.2)
  right_inv z := Prod.ext rfl (by
    simpa only [inv_inv] using inverse_value (inv_pos.mpr hd) (hw z.1) z.2)
  continuous_toFun := continuous_fst.prodMk ((continuous_value delta).comp
    ((hc.comp continuous_fst).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk ((continuous_value delta⁻¹).comp
    ((hc.comp continuous_fst).prodMk continuous_snd))





theorem finitePiecewiseAffineOn_value {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {w t : E → ℝ} {S : Set E} (delta : ℝ)
    (hw : FinitePiecewiseAffineOn w S) (ht : FinitePiecewiseAffineOn t S) :
    FinitePiecewiseAffineOn (fun x => value delta (w x) (t x)) S := by
  have hn : FinitePiecewiseAffineOn (fun x => -w x) S :=
    (hw.postcomp (-ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  have hm := hn.max (ht.min hw)
  have hdt : FinitePiecewiseAffineOn (fun x => delta * t x) S :=
    (ht.postcomp (delta • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  have hdm : FinitePiecewiseAffineOn
      (fun x => (1 - delta) * max (-w x) (min (t x) (w x))) S :=
    (hm.postcomp ((1 - delta) • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  exact hdt.add hdm



theorem locallyPiecewiseAffineOn_value_pair (delta : ℝ) :
    LocallyPiecewiseAffineOn (fun z : ℝ × ℝ => value delta z.1 z.2) univ := by
  intro z _
  obtain ⟨K, hK, hzK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ z))
  have hw := (K.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have ht := (K.affineOnFaces_affine
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  obtain ⟨J, hJ, hJK, hf⟩ := finitePiecewiseAffineOn_value delta hw ht
  refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, hf⟩
  rw [hJK]
  exact hzK (mem_singleton z)




theorem locallyPiecewiseAffineOn_value {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {w t : E → ℝ} {U : Set E} (delta : ℝ)
    (hw : LocallyPiecewiseAffineOn w U) (ht : LocallyPiecewiseAffineOn t U) :
    LocallyPiecewiseAffineOn (fun x => value delta (w x) (t x)) U := by
  exact ((locallyPiecewiseAffineOn_value_pair delta).comp
    (hw.prod_mk ht)).mono hw.isOpen (fun _ hx => ⟨hx, mem_univ _⟩)




theorem homeomorph_mem_piecewiseAffineGroupoid {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (delta : ℝ) (hd : 0 < delta) (w : E → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : Continuous w) (hPL : LocallyPiecewiseAffineOn w univ) :
    (homeomorph delta hd w hw hc).toOpenPartialHomeomorph ∈
      piecewiseAffineGroupoid (E × ℝ) := by
  have hfst := locallyPiecewiseAffineOn_affine
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap isOpen_univ
  have hsnd := locallyPiecewiseAffineOn_affine
    (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap isOpen_univ
  have hw' := (hPL.comp hfst).mono isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  apply (mem_piecewiseAffineGroupoid_iff_forward
    (homeomorph delta hd w hw hc).toOpenPartialHomeomorph).mpr
  exact hfst.prod_mk (locallyPiecewiseAffineOn_value delta hw' hsnd)

end PLFiberCompression
