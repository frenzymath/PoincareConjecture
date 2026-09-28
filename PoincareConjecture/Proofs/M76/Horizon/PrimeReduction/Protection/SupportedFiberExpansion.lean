import PoincareConjecture.Proofs.M76.Mathlib.PLFiberCompression
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic







set_option autoImplicit false
noncomputable section
open Set Geometry

namespace PoincareConjecture.M76.ProtectedFiberExpansion

def outerWidth (L w : ℝ) : ℝ := (2 - L⁻¹) * w

def value (L w t : ℝ) : ℝ :=
  PLFiberCompression.value 2 (outerWidth L w)
    (PLFiberCompression.value (2 * L)⁻¹ w (L * t))

private theorem compression_neg (d w t : ℝ) (hw : 0 ≤ w) :
    PLFiberCompression.value d w (-t) = -PLFiberCompression.value d w t := by
  by_cases ht : t ≤ -w
  · rw [PLFiberCompression.value_of_le_neg hw ht,
      PLFiberCompression.value_of_width_le hw (by linarith)]
    ring
  · by_cases ht' : t ≤ w
    · rw [PLFiberCompression.value_of_mem ⟨by linarith, ht'⟩,
        PLFiberCompression.value_of_mem ⟨by linarith, by linarith⟩]
    · rw [PLFiberCompression.value_of_le_neg hw (show -t ≤ -w by linarith),
        PLFiberCompression.value_of_width_le hw (show w ≤ t by linarith)]
      ring

theorem width_le_outerWidth {L w : ℝ} (hL : 1 < L) (hw : 0 ≤ w) :
    w ≤ outerWidth L w := by
  have hi : L⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hL.le
  unfold outerWidth
  nlinarith

theorem value_neg {L w : ℝ} (hL : 1 < L) (hw : 0 ≤ w) (t : ℝ) :
    value L w (-t) = -value L w t := by
  simp only [value, mul_neg]
  rw [compression_neg _ _ _ hw,
    compression_neg _ _ _ (hw.trans (width_le_outerWidth hL hw))]

theorem strictMono_value {L w : ℝ} (hL : 1 < L) (hw : 0 ≤ w) :
    StrictMono (value L w) := by
  exact (PLFiberCompression.strictMono_value (by norm_num : (0 : ℝ) < 2)
    (hw.trans (width_le_outerWidth hL hw))).comp
      ((PLFiberCompression.strictMono_value (by positivity : 0 < (2 * L)⁻¹) hw).comp
        (strictMono_id.const_mul (by linarith : 0 < L)))

theorem value_of_outerWidth_le {L w t : ℝ} (hL : 1 < L) (hw : 0 ≤ w)
    (ht : outerWidth L w ≤ t) : value L w t = t := by
  have hLp : 0 < L := by linarith
  have hL0 : L ≠ 0 := ne_of_gt hLp
  have hwt : w ≤ t := (width_le_outerWidth hL hw).trans ht
  have hLt : w ≤ L * t := by nlinarith
  have hm : PLFiberCompression.value (2 * L)⁻¹ w (L * t) =
      t / 2 + (1 - (2 * L)⁻¹) * w := by
    rw [PLFiberCompression.value_of_width_le hw hLt]
    field_simp
  have hmge : outerWidth L w ≤ t / 2 + (1 - (2 * L)⁻¹) * w := by
    have hid : (2 * L)⁻¹ = L⁻¹ / 2 := by field_simp
    rw [hid]
    unfold outerWidth at ht ⊢
    nlinarith
  rw [value, hm, PLFiberCompression.value_of_width_le
    (hw.trans (width_le_outerWidth hL hw)) hmge]
  unfold outerWidth
  field_simp
  ring

theorem value_of_outerWidth_le_abs {L w t : ℝ} (hL : 1 < L) (hw : 0 ≤ w)
    (ht : outerWidth L w ≤ |t|) : value L w t = t := by
  by_cases ht0 : 0 ≤ t
  · exact value_of_outerWidth_le hL hw (by simpa only [abs_of_nonneg ht0] using ht)
  · have hn := value_of_outerWidth_le hL hw
      (show outerWidth L w ≤ -t by simpa only [abs_of_neg (lt_of_not_ge ht0)] using ht)
    rw [value_neg hL hw] at hn
    linarith

theorem value_zero_width {L : ℝ} (hL : 1 < L) (t : ℝ) : value L 0 t = t :=
  value_of_outerWidth_le_abs hL le_rfl (by simp [outerWidth])

theorem value_zero {L w : ℝ} (hL : 1 < L) (hw : 0 ≤ w) : value L w 0 = 0 := by
  have h := value_neg hL hw 0
  simp only [neg_zero] at h
  linarith

theorem value_at_innerWidth {L w : ℝ} (hL : 1 < L) (hw : 0 ≤ w) :
    value L w (w / L) = w := by
  have hL0 : L ≠ 0 := ne_of_gt (show 0 < L by linarith)
  have he : L * (w / L) = w := by field_simp
  rw [value, he, PLFiberCompression.value_of_mem ⟨by linarith, le_rfl⟩,
    PLFiberCompression.value_of_mem ⟨by
      have := width_le_outerWidth hL hw
      linarith, width_le_outerWidth hL hw⟩]

theorem abs_value_gt_width {L w t : ℝ} (hL : 1 < L) (hw : 0 ≤ w)
    (ht : w / L < |t|) : w < |value L w t| := by
  have hpos : w < value L w |t| := by
    calc
      w = value L w (w / L) := (value_at_innerWidth hL hw).symm
      _ < value L w |t| := strictMono_value hL hw ht
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0] at hpos
    exact hpos.trans_le (le_abs_self _)
  · rw [abs_of_neg (lt_of_not_ge ht0), value_neg hL hw] at hpos
    exact hpos.trans_le (neg_le_abs _)

def homeomorph {E : Type*} [TopologicalSpace E]
    (L : ℝ) (hL : 1 < L) (w : E → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : Continuous w) : (E × ℝ) ≃ₜ (E × ℝ) :=
  ((PLFiberCompression.homeomorph L (by linarith) (fun _ => 0)
    (fun _ => le_rfl) continuous_const).trans
      (PLFiberCompression.homeomorph (2 * L)⁻¹ (by positivity) w hw hc)).trans
    (PLFiberCompression.homeomorph 2 (by norm_num)
      (fun x => outerWidth L (w x))
      (fun x => (hw x).trans (width_le_outerWidth hL (hw x)))
      (continuous_const.mul hc))

theorem homeomorph_apply {E : Type*} [TopologicalSpace E]
    (L : ℝ) (hL : 1 < L) (w : E → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : Continuous w) (z : E × ℝ) :
    homeomorph L hL w hw hc z = (z.1, value L (w z.1) z.2) := by
  change (_, PLFiberCompression.value 2 _
    (PLFiberCompression.value (2 * L)⁻¹ _ (PLFiberCompression.value L 0 _))) = _
  rw [PLFiberCompression.value_zero_width]
  rfl

theorem homeomorph_mem_piecewiseAffineGroupoid {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : ℝ) (hL : 1 < L) (w : E → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : Continuous w) (hPL : LocallyPiecewiseAffineOn w univ) :
    (homeomorph L hL w hw hc).toOpenPartialHomeomorph ∈
      piecewiseAffineGroupoid (E × ℝ) := by
  have hz : LocallyPiecewiseAffineOn (fun _ : E => (0 : ℝ)) univ :=
    locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ E 0) isOpen_univ
  have hb : LocallyPiecewiseAffineOn (fun x => outerWidth L (w x)) univ := by
    exact ((locallyPiecewiseAffineOn_affine
      ((2 - L⁻¹) • ContinuousAffineMap.id ℝ ℝ) isOpen_univ).comp hPL).mono
        isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  unfold homeomorph
  rw [Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.trans_toOpenPartialHomeomorph]
  exact (piecewiseAffineGroupoid (E × ℝ)).trans
    ((piecewiseAffineGroupoid (E × ℝ)).trans
      (PLFiberCompression.homeomorph_mem_piecewiseAffineGroupoid _ _ _ _ _ hz)
      (PLFiberCompression.homeomorph_mem_piecewiseAffineGroupoid _ _ _ _ _ hPL))
    (PLFiberCompression.homeomorph_mem_piecewiseAffineGroupoid _ _ _ _ _ hb)

def squareCutoff (r s : ℝ) (x : ℝ × ℝ) : ℝ :=
  min 1 (max 0 ((s - r)⁻¹ * (s - ‖x‖)))

theorem squareCutoff_properties {r s : ℝ} (hrs : r < s) :
    Continuous (squareCutoff r s) ∧
    (∀ x, squareCutoff r s x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x, ‖x‖ ≤ r → squareCutoff r s x = 1) ∧
    (∀ x, s ≤ ‖x‖ → squareCutoff r s x = 0) := by
  refine ⟨by unfold squareCutoff; fun_prop, ?_, ?_, ?_⟩
  · intro x
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  · intro x hx
    have h : 1 ≤ (s - r)⁻¹ * (s - ‖x‖) := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ (sub_pos.mpr hrs)).mpr (by linarith)
    exact min_eq_left (h.trans (le_max_right _ _))
  · intro x hx
    have h : (s - r)⁻¹ * (s - ‖x‖) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (sub_nonneg.mpr hrs.le))
        (sub_nonpos.mpr hx)
    simp only [squareCutoff, max_eq_left h, min_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]

theorem squareCutoff_locallyPL (r s : ℝ) :
    LocallyPiecewiseAffineOn (squareCutoff r s) univ := by
  have hfst := locallyPiecewiseAffineOn_affine
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap isOpen_univ
  have hsnd := locallyPiecewiseAffineOn_affine
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap isOpen_univ
  have hn : LocallyPiecewiseAffineOn (norm : (ℝ × ℝ) → ℝ) univ := by
    exact ((hfst.max hfst.neg).max (hsnd.max hsnd.neg)).congr
      (fun x _ => by simp only [Prod.norm_def, Real.norm_eq_abs, abs_eq_max_neg]; rfl)
  have ha := locallyPiecewiseAffineOn_affine
    (((s - r)⁻¹ : ℝ) •
      (ContinuousAffineMap.const ℝ ℝ s - ContinuousAffineMap.id ℝ ℝ)) isOpen_univ
  have hh : LocallyPiecewiseAffineOn (fun x : ℝ × ℝ =>
      (s - r)⁻¹ * (s - ‖x‖)) univ := by
    exact (ha.comp hn).mono isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  exact (locallyPiecewiseAffineOn_affine
    (ContinuousAffineMap.const ℝ (ℝ × ℝ) 1) isOpen_univ).min
    ((locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ (ℝ × ℝ) 0) isOpen_univ).max hh)

theorem exists_supported_expansion_of_bounds_with_support {r s η : ℝ}
    (hrs : r < s) (hη : 0 < η) :
    ∃ v : ℝ, 0 < v ∧ v < 2 ∧
      ∃ H : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ),
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid ((ℝ × ℝ) × ℝ) ∧
      (∀ z, (H z).1 = z.1) ∧
      (∀ x, H (x, 0) = (x, 0)) ∧
      (∀ z, s ≤ ‖z.1‖ ∨ v ≤ |z.2| → H z = z) ∧
      ∀ z, ‖z.1‖ ≤ r → η ≤ |z.2| → 1 < |(H z).2| := by
  let L : ℝ := 2 + η⁻¹
  have hL : 1 < L := by
    have := inv_pos.mpr hη
    dsimp [L]
    linarith
  have hLη : L⁻¹ < η := by
    have hp : 0 < L := by linarith
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hp).mpr
    dsimp [L]
    rw [mul_add, mul_inv_cancel₀ (ne_of_gt hη)]
    linarith
  obtain ⟨hc, hw, hcore, hout⟩ := squareCutoff_properties hrs
  let H := homeomorph L hL (squareCutoff r s) (fun x => (hw x).1) hc
  have hval := homeomorph_apply L hL (squareCutoff r s) (fun x => (hw x).1) hc
  have hi : 0 < L⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : L⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hL.le
  refine ⟨2 - L⁻¹, by linarith, by linarith, H,
    homeomorph_mem_piecewiseAffineGroupoid L hL _ _ hc
    (squareCutoff_locallyPL r s), ?_, ?_, ?_, ?_⟩
  · intro z
    change (homeomorph L hL (squareCutoff r s) (fun x => (hw x).1) hc z).1 = z.1
    rw [hval]
  · intro x
    rw [show H (x, 0) = _ from hval _, value_zero hL (hw x).1]
  · intro z hz
    rw [show H z = _ from hval _]
    apply Prod.ext
    · rfl
    change value L (squareCutoff r s z.1) z.2 = z.2
    rcases hz with hz | hz
    · rw [hout _ hz, value_zero_width hL]
    · apply value_of_outerWidth_le_abs hL (hw z.1).1
      have hw0 := (hw z.1).1
      have hw1 := (hw z.1).2
      unfold outerWidth
      nlinarith
  · intro z hz ht
    rw [show H z = _ from hval _, hcore _ hz]
    exact abs_value_gt_width hL (by norm_num) (by simpa only [one_div] using hLη.trans_le ht)

theorem exists_supported_expansion_of_bounds {r s η : ℝ}
    (hrs : r < s) (hη : 0 < η) :
    ∃ H : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ),
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid ((ℝ × ℝ) × ℝ) ∧
      (∀ z, (H z).1 = z.1) ∧
      (∀ x, H (x, 0) = (x, 0)) ∧
      (∀ z, s ≤ ‖z.1‖ ∨ 2 ≤ |z.2| → H z = z) ∧
      ∀ z, ‖z.1‖ ≤ r → η ≤ |z.2| → 1 < |(H z).2| := by
  obtain ⟨v, _, hv, H, hH, hfst, hzero, hfix, hmove⟩ :=
    exists_supported_expansion_of_bounds_with_support hrs hη
  exact ⟨H, hH, hfst, hzero,
    fun z hz => hfix z (hz.imp_right (fun h => hv.le.trans h)), hmove⟩

theorem exists_supported_expansion_of_compact_with_support
    {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C)
    (hCr : ∀ z ∈ C, ‖z.1‖ < 1) (hC0 : ∀ z ∈ C, z.2 ≠ 0) :
    ∃ s v : ℝ, 0 < s ∧ s < 1 ∧ 0 < v ∧ v < 2 ∧
      ∃ H : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ),
        H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid ((ℝ × ℝ) × ℝ) ∧
        (∀ z, (H z).1 = z.1) ∧
        (∀ x, H (x, 0) = (x, 0)) ∧
        (∀ z, s ≤ ‖z.1‖ ∨ v ≤ |z.2| → H z = z) ∧
        ∀ z ∈ C, 1 < |(H z).2| := by
  obtain ⟨ε, hε, hr⟩ := hC.exists_forall_le'
    (show ContinuousOn (fun z : (ℝ × ℝ) × ℝ => 1 - ‖z.1‖) C by fun_prop)
    (fun z hz => sub_pos.mpr (hCr z hz))
  obtain ⟨η, hη, ht⟩ := hC.exists_forall_le'
    (show ContinuousOn (fun z : (ℝ × ℝ) × ℝ => |z.2|) C by fun_prop)
    (fun z hz => abs_pos.mpr (hC0 z hz))
  let r := max 0 (1 - ε)
  let s := (r + 1) / 2
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r < 1 := max_lt (by norm_num) (by linarith)
  have hrs : r < s := by dsimp [s]; linarith
  obtain ⟨v, hv0, hv2, H, hH, hfst, hzero, hfix, hmove⟩ :=
    exists_supported_expansion_of_bounds_with_support hrs hη
  refine ⟨s, v, by dsimp [s]; linarith, by dsimp [s]; linarith, hv0, hv2,
    H, hH, hfst, hzero, hfix, ?_⟩
  intro z hz
  apply hmove z ?_ (ht z hz)
  exact (show ‖z.1‖ ≤ 1 - ε by linarith [hr z hz]).trans (le_max_right _ _)

theorem exists_supported_expansion_of_compact
    {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C)
    (hCr : ∀ z ∈ C, ‖z.1‖ < 1) (hC0 : ∀ z ∈ C, z.2 ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∃ H : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ),
        H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid ((ℝ × ℝ) × ℝ) ∧
        (∀ z, (H z).1 = z.1) ∧
        (∀ x, H (x, 0) = (x, 0)) ∧
        (∀ z, s ≤ ‖z.1‖ ∨ 2 ≤ |z.2| → H z = z) ∧
        ∀ z ∈ C, 1 < |(H z).2| := by
  obtain ⟨s, v, hs0, hs1, _, hv, H, hH, hfst, hzero, hfix, hmove⟩ :=
    exists_supported_expansion_of_compact_with_support hC hCr hC0
  exact ⟨s, hs0, hs1, H, hH, hfst, hzero,
    fun z hz => hfix z (hz.imp_right (fun h => hv.le.trans h)), hmove⟩

end PoincareConjecture.M76.ProtectedFiberExpansion
