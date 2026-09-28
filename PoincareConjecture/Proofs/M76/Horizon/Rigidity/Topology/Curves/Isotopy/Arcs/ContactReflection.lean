import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.GenericAxis
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.HighestAxis

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem regular_contact_has_strict_sides
    {f : ℝ → ℝ} {x c a b m : ℝ}
    (ha : 0 ≤ a) (hax : a < x) (hxb : x < b) (hb : b ≤ 1) (hm : m ≠ 0)
    (hformula : ∀ y ∈ Icc a b, f y - c = m * (y - x)) :
    (∃ u ∈ Icc (0 : ℝ) 1, f u < c) ∧
      (∃ v ∈ Icc (0 : ℝ) 1, c < f v) := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, (hax.trans hxb).le.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans (hax.trans hxb).le, hb⟩
  have hfa := hformula a ⟨le_rfl, (hax.trans hxb).le⟩
  have hfb := hformula b ⟨(hax.trans hxb).le, le_rfl⟩
  rcases lt_or_gt_of_ne hm with hm | hm
  · have hp := mul_pos_of_neg_of_neg hm (sub_neg.mpr hax)
    have hn := mul_neg_of_neg_of_pos hm (sub_pos.mpr hxb)
    exact ⟨⟨b, hbI, by linarith⟩, ⟨a, haI, by linarith⟩⟩
  · have hn := mul_neg_of_pos_of_neg hm (sub_neg.mpr hax)
    have hp := mul_pos hm (sub_pos.mpr hxb)
    exact ⟨⟨a, haI, by linarith⟩, ⟨b, hbI, by linarith⟩⟩

theorem contact_has_strict_periodic_excursion
    {f : ℝ → ℝ} {c : ℝ}
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → f x = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, f y - (c + 32 * (k : ℝ)) = m * (y - x))
    (hcontact : ∃ x ∈ Icc (0 : ℝ) 1, ∃ k : ℤ, f x = c + 32 * (k : ℝ)) :
    (∃ t ∈ Icc (0 : ℝ) 1, c < f t) ∨
      (∃ t ∈ Icc (0 : ℝ) 1, f t < c - 32) := by
  obtain ⟨x, hx, k, hk⟩ := hcontact
  obtain ⟨a, b, m, ha, hax, hxb, hb, hm, hformula⟩ := hreg x k hx hk
  obtain ⟨⟨u, hu, hlow⟩, ⟨v, hv, hhigh⟩⟩ :=
    regular_contact_has_strict_sides ha hax hxb hb hm hformula
  by_cases hk0 : 0 ≤ k
  · have hk0' : (0 : ℝ) ≤ k := by exact_mod_cast hk0
    exact Or.inl ⟨v, hv, by linarith⟩
  · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    exact Or.inr ⟨u, hu, by linarith⟩

def reflectedAnnularLift (r : ℝ → ℝ × ℝ) : ℝ → ℝ × ℝ :=
  fun t => (-(r t).1, (r t).2)

@[simp] theorem reflectedAnnularLift_apply (r : ℝ → ℝ × ℝ) (t : ℝ) :
    reflectedAnnularLift r t = (-(r t).1, (r t).2) := rfl

@[simp] theorem reflectedAnnularLift_twice (r : ℝ → ℝ × ℝ) :
    reflectedAnnularLift (reflectedAnnularLift r) = r := by
  funext t
  simp only [reflectedAnnularLift_apply, neg_neg, Prod.eta]

theorem finitePiecewiseAffineOn_reflectedAnnularLift {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) :
    FinitePiecewiseAffineOn (reflectedAnnularLift r) (Icc 0 1) :=
  hr.postcomp ((-ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)).toContinuousAffineMap

theorem injOn_reflectedAnnularLift {r : ℝ → ℝ × ℝ} (hi : InjOn r (Icc 0 1)) :
    InjOn (reflectedAnnularLift r) (Icc 0 1) := by
  intro s hs t ht heq
  apply hi hs ht
  apply Prod.ext
  · exact neg_injective (congrArg Prod.fst heq)
  · simpa only [reflectedAnnularLift_apply] using congrArg Prod.snd heq

theorem reflectedAnnularLift_periodic_contact_iff {r : ℝ → ℝ × ℝ}
    (c t : ℝ) (k : ℤ) :
    (reflectedAnnularLift r t).1 = (32 - c) + 32 * (k : ℝ) ↔
      (r t).1 = c + 32 * ((-k - 1 : ℤ) : ℝ) := by
  simp only [reflectedAnnularLift_apply, Int.cast_sub, Int.cast_neg, Int.cast_one]
  constructor <;> intro h <;> linarith

theorem reflectedAnnularLift_periodic_contacts_eq (r : ℝ → ℝ × ℝ) (c : ℝ) :
    {t ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (reflectedAnnularLift r t).1 = (32 - c) + 32 * (k : ℝ)} =
      {t ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r t).1 = c + 32 * (k : ℝ)} := by
  ext t
  constructor
  · rintro ⟨ht, k, hk⟩
    exact ⟨ht, -k - 1, (reflectedAnnularLift_periodic_contact_iff c t k).mp hk⟩
  · rintro ⟨ht, k, hk⟩
    refine ⟨ht, -k - 1, (reflectedAnnularLift_periodic_contact_iff c t (-k - 1)).mpr ?_⟩
    have hi : -(-k - 1) - 1 = k := by omega
    rwa [hi]

theorem reflectedAnnularLift_regular_contacts {r : ℝ → ℝ × ℝ} {c : ℝ}
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x)) :
    ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 →
      (reflectedAnnularLift r x).1 = (32 - c) + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b,
          (reflectedAnnularLift r y).1 - ((32 - c) + 32 * (k : ℝ)) = m * (y - x) := by
  intro x k hx hk
  obtain ⟨a, b, m, ha, hax, hxb, hb, hm, hformula⟩ :=
    hreg x (-k - 1) hx ((reflectedAnnularLift_periodic_contact_iff c x k).mp hk)
  refine ⟨a, b, -m, ha, hax, hxb, hb, neg_ne_zero.mpr hm, ?_⟩
  intro y hy
  have h := hformula y hy
  simp only [Int.cast_sub, Int.cast_neg, Int.cast_one] at h
  change -(r y).1 - ((32 - c) + 32 * (k : ℝ)) = -m * (y - x)
  nlinarith

theorem reflectedAnnularLift_translates_disjoint {r : ℝ → ℝ × ℝ}
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0) :
    ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, reflectedAnnularLift r s = reflectedAnnularLift r t + (32 * (k : ℝ), 0) →
        s = t ∧ k = 0 := by
  intro s t hs ht k heq
  have hangle := congrArg Prod.fst heq
  have hheight := congrArg Prod.snd heq
  have hrev : r s = r t + (32 * ((-k : ℤ) : ℝ), 0) := by
    apply Prod.ext
    · change (r s).1 = (r t).1 + 32 * ((-k : ℤ) : ℝ)
      rw [Int.cast_neg]
      change -(r s).1 = -(r t).1 + 32 * (k : ℝ) at hangle
      linarith
    · exact hheight
  obtain ⟨hst, hk⟩ := htranslate s t hs ht (-k) hrev
  exact ⟨hst, neg_eq_zero.mp hk⟩

theorem finite_reflectedAnnularLift_contacts {r : ℝ → ℝ × ℝ} {c : ℝ}
    (hfinite : {t ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r t).1 = c + 32 * (k : ℝ)}.Finite) :
    {t ∈ Icc (0 : ℝ) 1 |
      ∃ k : ℤ, (reflectedAnnularLift r t).1 = (32 - c) + 32 * (k : ℝ)}.Finite := by
  rw [reflectedAnnularLift_periodic_contacts_eq]
  exact hfinite

theorem contact_has_positive_or_reflected_excursion {r : ℝ → ℝ × ℝ} {c : ℝ}
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x))
    (hcontact : ∃ x ∈ Icc (0 : ℝ) 1, ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)) :
    (∃ t ∈ Icc (0 : ℝ) 1, c < (r t).1) ∨
      (∃ t ∈ Icc (0 : ℝ) 1, 32 - c < (reflectedAnnularLift r t).1) := by
  rcases contact_has_strict_periodic_excursion hreg hcontact with h | ⟨t, ht, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, ht, by change 32 - c < -(r t).1; linarith⟩

theorem reflectedAnnularLift_zero_winding_geometry {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hr0 : r 0 = (0, -1)) (hr1 : r 1 = (0, 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 32)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)}.Finite)
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x)) :
    (32 - c) ∈ Ioo (0 : ℝ) 32 ∧
      FinitePiecewiseAffineOn (reflectedAnnularLift r) (Icc 0 1) ∧
      InjOn (reflectedAnnularLift r) (Icc 0 1) ∧
      reflectedAnnularLift r 0 = (0, -1) ∧ reflectedAnnularLift r 1 = (0, 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (reflectedAnnularLift r t).2 ∈ Icc (-1 : ℝ) 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (reflectedAnnularLift r t).2 ∈ Ioo (-1 : ℝ) 1) ∧
      (∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        ∀ k : ℤ, reflectedAnnularLift r s = reflectedAnnularLift r t + (32 * (k : ℝ), 0) →
          s = t ∧ k = 0) ∧
      {x ∈ Icc (0 : ℝ) 1 |
        ∃ k : ℤ, (reflectedAnnularLift r x).1 = (32 - c) + 32 * (k : ℝ)}.Finite ∧
      ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 →
        (reflectedAnnularLift r x).1 = (32 - c) + 32 * (k : ℝ) →
        ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
          ∀ y ∈ Icc a b,
            (reflectedAnnularLift r y).1 - ((32 - c) + 32 * (k : ℝ)) = m * (y - x) := by
  refine ⟨⟨by linarith [hc.2], by linarith [hc.1]⟩,
    finitePiecewiseAffineOn_reflectedAnnularLift hr, injOn_reflectedAnnularLift hi,
    ?_, ?_, hheight, hproper, reflectedAnnularLift_translates_disjoint htranslate,
    finite_reflectedAnnularLift_contacts hfinite, reflectedAnnularLift_regular_contacts hreg⟩
  · simp only [reflectedAnnularLift_apply, hr0, neg_zero]
  · simp only [reflectedAnnularLift_apply, hr1, neg_zero]

theorem exists_highest_generic_annular_axis_of_negative_excursion {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) {c : ℝ}
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x))
    (hbelow : ∃ t ∈ Icc (0 : ℝ) 1, (r t).1 < c - 32) :
    ∃ (k : ℤ) (d : ℝ), 0 ≤ k ∧ 0 < d ∧ d < 32 ∧
      (∃ t ∈ Icc (0 : ℝ) 1, (32 - c) + 32 * (k : ℝ) < (reflectedAnnularLift r t).1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (reflectedAnnularLift r t).1 - ((32 - c) + 32 * (k : ℝ)) ≤ d := by
  have hf := (finitePiecewiseAffineOn_reflectedAnnularLift hr).postcomp
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  apply exists_highest_generic_annular_axis hf (reflectedAnnularLift_regular_contacts hreg)
  obtain ⟨t, ht, hlt⟩ := hbelow
  exact ⟨t, ht, by change 32 - c < -(r t).1; linarith⟩

end PoincareConjecture.M76.Dehn
