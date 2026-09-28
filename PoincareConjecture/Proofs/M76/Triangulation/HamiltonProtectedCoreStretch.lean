import PoincareConjecture.Proofs.M76.Mathlib.SmallLipschitzHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.PLBandCutoff
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffinePi
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinder

set_option autoImplicit false

open Set Metric Geometry
open scoped NNReal

namespace PoincareConjecture.M76

private noncomputable def scalarCoreMargin (x : ℝ) : ℝ := max 0 (2 - ‖x‖)

private noncomputable def scalarCoreClip (x : ℝ) : ℝ :=
  max (-scalarCoreMargin x) (min x (scalarCoreMargin x))

private theorem scalarCoreClip_lipschitz : LipschitzWith 1 scalarCoreClip := by
  have hm : LipschitzWith 1 scalarCoreMargin := by
    have h : LipschitzWith 1 (fun x : ℝ => 2 - ‖x‖) := by
      simpa using (LipschitzWith.const (2 : ℝ)).sub
        (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
    exact h.const_max 0
  change LipschitzWith 1 (fun x : ℝ =>
    max (-scalarCoreMargin x) (min x (scalarCoreMargin x)))
  simpa only [Pi.neg_apply, id_eq, max_self] using
    hm.neg.max ((LipschitzWith.id).min hm)

private theorem scalarCoreClip_core (x : ℝ) (hx : |x| ≤ 1) : scalarCoreClip x = x := by
  have hm : |x| ≤ scalarCoreMargin x := by
    apply le_trans _ (le_max_right _ _)
    simp only [Real.norm_eq_abs]
    linarith
  rw [scalarCoreClip, min_eq_left ((le_abs_self x).trans hm),
    max_eq_right ((neg_le_neg hm).trans (neg_abs_le x))]

private theorem scalarCoreClip_outside (x : ℝ) (hx : 2 ≤ |x|) : scalarCoreClip x = 0 := by
  have hm : scalarCoreMargin x = 0 := by
    apply max_eq_left
    simpa only [Real.norm_eq_abs] using sub_nonpos.mpr hx
  simp only [scalarCoreClip, hm, neg_zero]
  exact max_eq_left (min_le_right _ _)

private theorem localPL_neg {f : ℝ → ℝ}
    (hf : LocallyPiecewiseAffineOn f univ) :
    LocallyPiecewiseAffineOn (fun x => -f x) univ := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  refine ⟨K, hK, hxK, hKU, fun s hs => ?_⟩
  obtain ⟨a, ha⟩ := hfK s hs
  exact ⟨-a, fun y hy => congrArg Neg.neg (ha hy)⟩

private theorem scalarCoreClip_localPL : LocallyPiecewiseAffineOn scalarCoreClip univ := by
  have hid := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
  have hnid := localPL_neg hid
  have hn : LocallyPiecewiseAffineOn (norm : ℝ → ℝ) univ := by
    apply (hid.max hnid).congr
    intro x _
    change max x (-x) = ‖x‖
    rw [Real.norm_eq_abs]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left (by linarith)]
    · rw [abs_of_nonpos hx, max_eq_right (by linarith)]
  have hdiff : LocallyPiecewiseAffineOn (fun x : ℝ => 2 - ‖x‖) univ := by
    intro x hx
    obtain ⟨K, hK, hxK, hKU, hnK⟩ := hn x hx
    refine ⟨K, hK, hxK, hKU, fun s hs => ?_⟩
    obtain ⟨a, ha⟩ := hnK s hs
    exact ⟨ContinuousAffineMap.const ℝ ℝ 2 - a,
      fun y hy => congrArg (fun t : ℝ => 2 - t) (ha hy)⟩
  have hm : LocallyPiecewiseAffineOn scalarCoreMargin univ :=
    (locallyPiecewiseAffineOn_affine (0 : ℝ →ᴬ[ℝ] ℝ) isOpen_univ).max hdiff
  have hmin : LocallyPiecewiseAffineOn (fun x : ℝ => min x (scalarCoreMargin x)) univ := by
    apply (localPL_neg (hnid.max (localPL_neg hm))).congr
    intro x _
    change -max (-x) (-scalarCoreMargin x) = min x (scalarCoreMargin x)
    rcases le_total x (scalarCoreMargin x) with hx | hx
    · rw [max_eq_left (neg_le_neg hx), min_eq_left hx, neg_neg]
    · rw [max_eq_right (neg_le_neg hx), min_eq_right hx, neg_neg]
  exact (localPL_neg hm).max hmin

private theorem exists_scalar_core_stretch {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ q : ℝ ≃ₜ ℝ, q.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid ℝ ∧
      (∀ x, |x| ≤ 1 → q x = r * x) ∧
      (∀ x, 2 ≤ |x| → q x = x) ∧
      (∀ x, |q x| < 2 ↔ |x| < 2) ∧
      (∀ x, |q x - x| ≤ 4) ∧
      ∀ x, |x| ≤ r → |q.symm x| ≤ 1 := by
  let ell : ℝ≥0 := ⟨r - 1, by linarith⟩
  have hu : LipschitzWith ell (fun x => (r - 1) * scalarCoreClip x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, ← mul_sub, norm_mul, Real.norm_eq_abs,
      abs_of_pos (show 0 < r - 1 by linarith)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one, one_mul, Real.norm_eq_abs] using
        scalarCoreClip_lipschitz.norm_sub_le x y) (by linarith)
  obtain ⟨q, hq⟩ := hu.exists_homeomorph_add (by change r - 1 < 1; linarith)
  have hqcore (x : ℝ) (hx : |x| ≤ 1) : q x = r * x := by
    rw [hq x, scalarCoreClip_core x hx]
    ring
  have hqout (x : ℝ) (hx : 2 ≤ |x|) : q x = x := by
    rw [hq x, scalarCoreClip_outside x hx, mul_zero, add_zero]
  have hqPL : LocallyPiecewiseAffineOn q univ := by
    intro x hx
    obtain ⟨K, hK, hxK, hKU, hv⟩ := scalarCoreClip_localPL x hx
    refine ⟨K, hK, hxK, hKU, fun s hs => ?_⟩
    obtain ⟨a, ha⟩ := hv s hs
    refine ⟨ContinuousAffineMap.id ℝ ℝ + (r - 1) • a, fun y hy => ?_⟩
    change q y = y + (r - 1) * a y
    rw [hq y, ha hy]
  have hqball (x : ℝ) : |q x| < 2 ↔ |x| < 2 := by
    constructor
    · intro hx
      by_contra hn
      rw [hqout x (le_of_not_gt hn)] at hx
      exact hn hx
    · intro hx
      by_contra hn
      have heq : q x = x := q.injective (hqout (q x) (le_of_not_gt hn))
      rw [heq] at hn
      exact hn hx
  refine ⟨q, ⟨hqPL, q.toOpenPartialHomeomorph.locallyPiecewiseAffineOn_symm hqPL⟩,
    hqcore, hqout, hqball, ?_, ?_⟩
  · intro x
    by_cases hx : 2 ≤ |x|
    · simp only [hqout x hx, sub_self, abs_zero]
      norm_num
    · have hx2 : |x| < 2 := lt_of_not_ge hx
      have hqx := (hqball x).mpr hx2
      exact (abs_sub (q x) x).trans (by linarith)
  · intro x hx
    have hr0 : 0 < r := by linarith
    have hdiv : |x / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hr0]
      exact (div_le_one₀ hr0).mpr hx
    have heq : q (x / r) = x := by
      rw [hqcore _ hdiv]
      field_simp
    rw [← heq, q.symm_apply_apply]
    exact hdiv

theorem exists_protected_core_stretch (ι : Type*) [Fintype ι]
    (J : Finset ι) {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ F : (ι → ℝ) ≃ₜ (ι → ℝ),
      F.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ι → ℝ) ∧
      (∀ x i, i ∈ J → F x i = x i) ∧
      (∀ x, ‖F x‖ < 2 ↔ ‖x‖ < 2) ∧
      (∀ x, ‖F x - x‖ ≤ 4) ∧
      ∀ x ∈ coordinateCylinder J, ‖x‖ ≤ r → ‖F.symm x‖ ≤ 1 := by
  classical
  obtain ⟨q, hqPL, _, _, hqball, hqbound, hqcore⟩ := exists_scalar_core_stretch hr hr2
  let e : ι → ℝ ≃ₜ ℝ := fun i => if i ∈ J then Homeomorph.refl ℝ else q
  let F := Homeomorph.piCongrRight e
  have hePL (i : ι) : (e i).toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid ℝ := by
    by_cases hi : i ∈ J
    · simp only [e, if_pos hi]
      exact ⟨locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ,
        locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ⟩
    · simpa only [e, if_neg hi] using hqPL
  have hFPL : LocallyPiecewiseAffineOn F univ := by
    change LocallyPiecewiseAffineOn (fun (x : ι → ℝ) (i : ι) => e i (x i)) univ
    have he (i : ι) : LocallyPiecewiseAffineOn (e i : ℝ → ℝ) univ := (hePL i).1
    simpa only [Set.pi_univ] using LocallyPiecewiseAffineOn.piMap he
  refine ⟨F, ⟨hFPL, F.toOpenPartialHomeomorph.locallyPiecewiseAffineOn_symm hFPL⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x i hi
    change e i (x i) = x i
    simp only [e, if_pos hi, Homeomorph.refl_apply, id_eq]
  · intro x
    rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 2),
      pi_norm_lt_iff (by norm_num : (0 : ℝ) < 2)]
    apply forall_congr'
    intro i
    change ‖e i (x i)‖ < 2 ↔ ‖x i‖ < 2
    by_cases hi : i ∈ J
    · simp only [e, if_pos hi, Homeomorph.refl_apply, id_eq]
    · simpa only [e, if_neg hi, Real.norm_eq_abs] using hqball (x i)
  · intro x
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)).mpr
    intro i
    change ‖e i (x i) - x i‖ ≤ 4
    by_cases hi : i ∈ J
    · simp only [e, if_pos hi, Homeomorph.refl_apply, id_eq, sub_self, norm_zero]
      norm_num
    · simpa only [e, if_neg hi, Real.norm_eq_abs] using hqbound (x i)
  · intro x hx hxr
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    change ‖(e i).symm (x i)‖ ≤ 1
    by_cases hi : i ∈ J
    · simpa only [e, if_pos hi, Homeomorph.refl_symm, Homeomorph.refl_apply, id_eq,
        Real.norm_eq_abs] using hx i hi
    · simp only [e, if_neg hi, Real.norm_eq_abs]
      exact hqcore _ ((show |x i| ≤ ‖x‖ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i).trans hxr)

end PoincareConjecture.M76
