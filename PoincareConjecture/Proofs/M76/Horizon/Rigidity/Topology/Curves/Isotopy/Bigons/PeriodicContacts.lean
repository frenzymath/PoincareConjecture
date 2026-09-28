import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.UpperComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ContactDeletion

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem annular_axis_label_unique {r : ℝ → V} {c x : ℝ} {j k : ℤ}
    (hj : (annularLiftAboveAxis r (c + 32 * (j : ℝ)) x).2 = 0)
    (hk : (annularLiftAboveAxis r (c + 32 * (k : ℝ)) x).2 = 0) : j = k := by
  change (r x).1 - (c + 32 * (j : ℝ)) = 0 at hj
  change (r x).1 - (c + 32 * (k : ℝ)) = 0 at hk
  have he : (j : ℝ) = (k : ℝ) := by linarith
  exact_mod_cast he

theorem periodic_contacts_eq_sdiff_of_selected_copy_deletion
    {r : ℝ → V} {f : ℤ → ℝ → V} {c a b : ℝ} {k : ℤ}
    (ha : (r a).1 = c + 32 * (k : ℝ))
    (hb : (r b).1 = c + 32 * (k : ℝ))
    (hunchanged : ∀ j : ℤ, j ≠ k → ∀ x ∈ Icc (0 : ℝ) 1,
      f j x = annularLiftAboveAxis r (c + 32 * (j : ℝ)) x)
    (hdelete : {x ∈ Icc (0 : ℝ) 1 | (f k x).2 = 0} =
      {x ∈ Icc (0 : ℝ) 1 | (annularLiftAboveAxis r (c + 32 * (k : ℝ)) x).2 = 0} \ {a, b}) :
    {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (f j x).2 = 0} =
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)} \ {a, b} := by
  have ha0 : (annularLiftAboveAxis r (c + 32 * (k : ℝ)) a).2 = 0 := by
    change (r a).1 - (c + 32 * (k : ℝ)) = 0
    rw [ha, sub_self]
  have hb0 : (annularLiftAboveAxis r (c + 32 * (k : ℝ)) b).2 = 0 := by
    change (r b).1 - (c + 32 * (k : ℝ)) = 0
    rw [hb, sub_self]
  ext x
  constructor
  · rintro ⟨hx, j, hj⟩
    by_cases hjk : j = k
    · subst j
      have hh := hdelete.subset ⟨hx, hj⟩
      exact ⟨⟨hx, k, sub_eq_zero.mp hh.1.2⟩, hh.2⟩
    · have hj0 : (annularLiftAboveAxis r (c + 32 * (j : ℝ)) x).2 = 0 := by
        rwa [hunchanged j hjk x hx] at hj
      refine ⟨⟨hx, j, sub_eq_zero.mp hj0⟩, ?_⟩
      rintro (rfl | rfl)
      · exact hjk (annular_axis_label_unique hj0 ha0)
      · exact hjk (annular_axis_label_unique hj0 hb0)
  · rintro ⟨⟨hx, j, hj⟩, hends⟩
    refine ⟨hx, j, ?_⟩
    have hj0 : (annularLiftAboveAxis r (c + 32 * (j : ℝ)) x).2 = 0 :=
      sub_eq_zero.mpr hj
    by_cases hjk : j = k
    · subst j
      exact (hdelete.symm.subset ⟨⟨hx, hj0⟩, hends⟩).2
    · rw [hunchanged j hjk x hx]
      exact hj0

theorem periodic_contact_count_decreases_of_selected_copy_deletion
    {r : ℝ → V} {f : ℤ → ℝ → V} {c a b : ℝ} {k : ℤ}
    (hab : a ≠ b) (haI : a ∈ Icc (0 : ℝ) 1) (hbI : b ∈ Icc (0 : ℝ) 1)
    (ha : (r a).1 = c + 32 * (k : ℝ))
    (hb : (r b).1 = c + 32 * (k : ℝ))
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.Finite)
    (hunchanged : ∀ j : ℤ, j ≠ k → ∀ x ∈ Icc (0 : ℝ) 1,
      f j x = annularLiftAboveAxis r (c + 32 * (j : ℝ)) x)
    (hdelete : {x ∈ Icc (0 : ℝ) 1 | (f k x).2 = 0} =
      {x ∈ Icc (0 : ℝ) 1 | (annularLiftAboveAxis r (c + 32 * (k : ℝ)) x).2 = 0} \ {a, b}) :
    {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (f j x).2 = 0}.Finite ∧
    {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (f j x).2 = 0}.ncard + 2 =
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.ncard ∧
    {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (f j x).2 = 0}.ncard <
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.ncard := by
  have he := periodic_contacts_eq_sdiff_of_selected_copy_deletion ha hb hunchanged hdelete
  have hsub : ({a, b} : Set ℝ) ⊆
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)} := by
    rintro x (rfl | rfl)
    · exact ⟨haI, k, ha⟩
    · exact ⟨hbI, k, hb⟩
  have hcount := ncard_sdiff_add_ncard_of_subset hsub hfinite
  rw [ncard_pair hab, ← he] at hcount
  refine ⟨?_, hcount, by omega⟩
  rw [he]
  exact hfinite.sdiff

theorem periodic_axis_germs_of_selected_copy_deletion
    {r : ℝ → V} {f : ℤ → ℝ → V} {c a b : ℝ} {k : ℤ}
    (hregular : ∀ x ∈ Icc (0 : ℝ) 1, ∀ j : ℤ, (r x).1 = c + 32 * (j : ℝ) →
      ∃ u v m : ℝ, 0 ≤ u ∧ u < x ∧ x < v ∧ v ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, (r y).1 - (c + 32 * (j : ℝ)) = m * (y - x))
    (hunchanged : ∀ j : ℤ, j ≠ k → ∀ x ∈ Icc (0 : ℝ) 1,
      f j x = annularLiftAboveAxis r (c + 32 * (j : ℝ)) x)
    (hdelete : {x ∈ Icc (0 : ℝ) 1 | (f k x).2 = 0} =
      {x ∈ Icc (0 : ℝ) 1 | (annularLiftAboveAxis r (c + 32 * (k : ℝ)) x).2 = 0} \ {a, b})
    (hlocal : ∀ x ∈ Icc (0 : ℝ) 1, (f k x).2 = 0 →
      ∃ η : ℝ, 0 < η ∧ ∀ y ∈ Icc (0 : ℝ) 1, |y - x| < η →
        f k y = annularLiftAboveAxis r (c + 32 * (k : ℝ)) y) :
    ∀ j : ℤ, ∀ x ∈ Icc (0 : ℝ) 1, (f j x).2 = 0 →
      ∃ u v m : ℝ, 0 ≤ u ∧ u < x ∧ x < v ∧ v ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, (f j y).2 = m * (y - x) := by
  intro j
  by_cases hjk : j = k
  · subst j
    apply transverse_axis_germs_of_contact_deletion
      (r := annularLiftAboveAxis r (c + 32 * (k : ℝ)))
    · exact fun x hx => (hdelete.subset hx).1
    · intro x hx hz
      exact hregular x hx k (sub_eq_zero.mp hz)
    · exact hlocal
  · intro x hx hz
    have hxphase : (r x).1 = c + 32 * (j : ℝ) := by
      rw [hunchanged j hjk x hx] at hz
      exact sub_eq_zero.mp hz
    obtain ⟨u, v, m, hu, hux, hxv, hv, hm, hf⟩ := hregular x hx j hxphase
    refine ⟨u, v, m, hu, hux, hxv, hv, hm, ?_⟩
    intro y hy
    rw [hunchanged j hjk y ⟨hu.trans hy.1, hy.2.trans hv⟩]
    exact hf y hy

end PoincareConjecture.M76.Dehn
