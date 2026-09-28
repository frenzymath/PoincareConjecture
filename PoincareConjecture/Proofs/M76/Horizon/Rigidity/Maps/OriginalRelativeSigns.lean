import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalPLDomination
import PoincareConjecture.Proofs.M76.Mathlib.PLBandCutoff

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}

private theorem localPL_scale {h : V3 → ℝ} {U : Set V3}
    (hh : LocallyPiecewiseAffineOn h U) (c : ℝ) :
    LocallyPiecewiseAffineOn (fun x => c * h x) U := by
  simpa only [preimage_univ, inter_univ, ContinuousAffineMap.coe_smul,
    ContinuousAffineMap.coe_id, Function.comp_def, Pi.smul_apply, id_eq, smul_eq_mul] using
    (locallyPiecewiseAffineOn_affine (c • ContinuousAffineMap.id ℝ ℝ)
      isOpen_univ).comp hh

private theorem localPL_neg {h : V3 → ℝ} {U : Set V3}
    (hh : LocallyPiecewiseAffineOn h U) :
    LocallyPiecewiseAffineOn (fun x => -h x) U := by
  simpa only [neg_one_mul] using localPL_scale hh (-1)

private theorem localPL_min {f g : V3 → ℝ} {U : Set V3}
    (hf : LocallyPiecewiseAffineOn f U) (hg : LocallyPiecewiseAffineOn g U) :
    LocallyPiecewiseAffineOn (fun x => Min.min (f x) (g x)) U := by
  exact (localPL_neg ((localPL_neg hf).max (localPL_neg hg))).congr
    (fun x _ => by
      change -Max.max (-f x) (-g x) = Min.min (f x) (g x)
      rcases le_total (f x) (g x) with h | h
      · rw [max_eq_left (neg_le_neg h), min_eq_left h, neg_neg]
      · rw [max_eq_right (neg_le_neg h), min_eq_right h, neg_neg])

theorem PLDomain.exists_same_signs_relative (he : PLDomain e R) (hR : IsCompact R)
    {f old : X → ℝ} (hfc : Continuous f) (hoc : Continuous old)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (ho : ∀ i, LocallyPiecewiseAffineOn (old ∘ (e i).symm) (e i).target)
    (hpos : ∀ x ∈ R, 0 < old x ↔ 0 < f x)
    (hzero : ∀ x ∈ R, old x = 0 ↔ f x = 0) :
    ∃ g : X → ℝ, Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g old R ∧ ∀ x, (0 < g x ↔ 0 < f x) ∧
        (g x = 0 ↔ f x = 0) ∧ (g x < 0 ↔ f x < 0) := by
  have habsf (i : ι) : LocallyPiecewiseAffineOn
      ((fun x => |f x|) ∘ (e i).symm) (e i).target :=
    ((hf i).max (localPL_neg (hf i))).congr (fun _ _ => abs_eq_max_neg.symm)
  have habso (i : ι) : LocallyPiecewiseAffineOn
      ((fun x => |old x|) ∘ (e i).symm) (e i).target :=
    ((ho i).max (localPL_neg (ho i))).congr (fun _ _ => abs_eq_max_neg.symm)
  obtain ⟨C, hC, hCf⟩ := he.exists_le_pos_mul hR habsf habso
    (fun x _ => abs_nonneg (old x))
    (fun x hx hz => by rw [(hzero x hx).mp (abs_eq_zero.mp hz), abs_zero])
  obtain ⟨D, hD, hDo⟩ := he.exists_le_pos_mul hR habso habsf
    (fun x _ => abs_nonneg (f x))
    (fun x hx hz => by rw [(hzero x hx).mpr (abs_eq_zero.mp hz), abs_zero])
  let a := C⁻¹
  have ha : 0 < a := inv_pos.mpr hC
  let lo := fun x => Min.min (a * f x) (D * f x)
  let hi := fun x => Max.max (a * f x) (D * f x)
  let g := fun x => Max.max (lo x) (Min.min (hi x) (old x))
  have hlh (x : X) : lo x ≤ hi x := (min_le_left _ _).trans (le_max_left _ _)
  have hglo (x : X) : lo x ≤ g x := le_max_left _ _
  have hghi (x : X) : g x ≤ hi x := max_le (hlh x) (min_le_left _ _)
  have hscale (c : ℝ) : Continuous (fun x => c * f x) := continuous_const.mul hfc
  refine ⟨g, ((hscale a).min (hscale D)).max (((hscale a).max (hscale D)).min hoc),
    fun i => (localPL_min (localPL_scale (hf i) a) (localPL_scale (hf i) D)).max
      (localPL_min ((localPL_scale (hf i) a).max (localPL_scale (hf i) D)) (ho i)),
    ?_, ?_⟩
  · intro x hx
    have hsmall : a * |f x| ≤ |old x| := (inv_mul_le_iff₀ hC).mpr (hCf x hx)
    have hlarge := hDo x hx
    have hbounds : lo x ≤ old x ∧ old x ≤ hi x := by
      rcases lt_trichotomy (f x) 0 with hn | hz | hp
      · have hon : old x < 0 := by
          have hnp : ¬ 0 < old x := fun hp => (hpos x hx).mp hp |>.not_ge hn.le
          have hnz : old x ≠ 0 := fun hz => hn.ne ((hzero x hx).mp hz)
          exact lt_of_le_of_ne (le_of_not_gt hnp) hnz
        rw [abs_of_neg hn, abs_of_neg hon] at hsmall hlarge
        exact ⟨(min_le_right _ _).trans (by nlinarith),
          (show old x ≤ a * f x by nlinarith).trans (le_max_left _ _)⟩
      · have hozero := (hzero x hx).mpr hz
        simp only [lo, hi, hz, hozero, mul_zero, min_self, max_self, le_refl, and_self]
      · rw [abs_of_pos hp, abs_of_pos ((hpos x hx).mpr hp)] at hsmall hlarge
        exact ⟨(min_le_left _ _).trans hsmall, hlarge.trans (le_max_right _ _)⟩
    change Max.max (lo x) (Min.min (hi x) (old x)) = old x
    rw [min_eq_right hbounds.2, max_eq_right hbounds.1]
  · intro x
    have hspos : 0 < f x → 0 < g x := fun hp =>
      (lt_min (mul_pos ha hp) (mul_pos hD hp)).trans_le (hglo x)
    have hsneg : f x < 0 → g x < 0 := fun hn =>
      (hghi x).trans_lt (max_lt (mul_neg_of_pos_of_neg ha hn) (mul_neg_of_pos_of_neg hD hn))
    have hszero : f x = 0 → g x = 0 := by
      intro hz
      have hl : lo x = 0 := by simp [lo, hz]
      have hh : hi x = 0 := by simp [hi, hz]
      exact le_antisymm (hh ▸ hghi x) (hl ▸ hglo x)
    rcases lt_trichotomy (f x) 0 with hn | hz | hp
    · have hgn := hsneg hn
      exact ⟨iff_of_false (not_lt_of_ge hgn.le) (not_lt_of_ge hn.le),
        iff_of_false hgn.ne hn.ne, iff_of_true hgn hn⟩
    · rw [hz, hszero hz]
      simp
    · have hgp := hspos hp
      exact ⟨iff_of_true hgp hp, iff_of_false hgp.ne' hp.ne',
        iff_of_false (not_lt_of_ge hgp.le) (not_lt_of_ge hp.le)⟩

theorem PLDomain.exists_bounded_same_signs_relative (he : PLDomain e R) (hR : IsCompact R)
    {f old : X → ℝ} (hfc : Continuous f) (hoc : Continuous old)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (ho : ∀ i, LocallyPiecewiseAffineOn (old ∘ (e i).symm) (e i).target)
    (hpos : ∀ x ∈ R, 0 < old x ↔ 0 < f x)
    (hzero : ∀ x ∈ R, old x = 0 ↔ f x = 0)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ x ∈ R, |old x| ≤ r) :
    ∃ g : X → ℝ, Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g old R ∧ ∀ x, |g x| ≤ r ∧ (0 < g x ↔ 0 < f x) ∧
        (g x = 0 ↔ f x = 0) ∧ (g x < 0 ↔ f x < 0) := by
  obtain ⟨g, hgc, hg, heq, hs⟩ := he.exists_same_signs_relative hR hfc hoc hf ho hpos hzero
  let G := fun x => Max.max (-r) (Min.min r (g x))
  have hc (c : ℝ) (i : ι) : LocallyPiecewiseAffineOn (fun _ : V3 => c) (e i).target :=
    locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 c) (e i).open_target
  refine ⟨G, continuous_const.max (continuous_const.min hgc),
    fun i => (hc (-r) i).max (localPL_min (hc r i) (hg i)), ?_, ?_⟩
  · intro x hx
    have hb := abs_le.mp (hbound x hx)
    change Max.max (-r) (Min.min r (g x)) = old x
    rw [heq hx, min_eq_right hb.2, max_eq_right hb.1]
  · intro x
    have hl : -r ≤ G x := le_max_left _ _
    have hu : G x ≤ r := max_le (by linarith) (min_le_left _ _)
    have hp : 0 < G x ↔ 0 < g x := by
      change 0 < Max.max (-r) (Min.min r (g x)) ↔ 0 < g x
      simp only [lt_max_iff, lt_min_iff]
      constructor
      · rintro (h | ⟨_, h⟩)
        · linarith
        · exact h
      · exact fun h => Or.inr ⟨hr, h⟩
    have hn : G x < 0 ↔ g x < 0 := by
      change Max.max (-r) (Min.min r (g x)) < 0 ↔ g x < 0
      simp only [max_lt_iff, min_lt_iff]
      constructor
      · rintro ⟨_, h | h⟩
        · linarith
        · exact h
      · exact fun h => ⟨by linarith, Or.inr h⟩
    have hz : G x = 0 ↔ g x = 0 := by
      constructor
      · intro h
        apply le_antisymm <;> apply le_of_not_gt
        · intro hgp
          exact (hp.mpr hgp).ne' h
        · intro hgn
          exact (hn.mpr hgn).ne h
      · intro h
        simp only [G, h, min_eq_right hr.le, max_eq_right (by linarith : -r ≤ 0)]
    exact ⟨abs_le.mpr ⟨hl, hu⟩, hp.trans (hs x).1,
      hz.trans (hs x).2.1, hn.trans (hs x).2.2⟩

end PoincareConjecture.M76
