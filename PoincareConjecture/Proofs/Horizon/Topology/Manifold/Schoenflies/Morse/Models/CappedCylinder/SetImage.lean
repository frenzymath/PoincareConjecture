import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.HeightStretch

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.CappedCylinder

theorem image_heightMap_eq_caps_union_cylinder
    {P : Type*} (B : Set (Real × P)) (Q : Set P)
    (hbelt : ∀ t q, |t| ≤ 1 / 4 → ((t, q) ∈ B ↔ q ∈ Q))
    (hsym : ∀ t q, (t, q) ∈ B ↔ (-t, q) ∈ B)
    {a b u w : Real} (hab : a ≤ b) (hu : 0 < u) (hw : 0 < w)
    (H : Real -> Real) (hH : Continuous H) (hmono : Monotone H)
    (hlow : ∀ t, t ≤ -(1 / 4) -> H t = a + u * t)
    (hhigh : ∀ t, 1 / 4 ≤ t -> H t = b + w * t) :
    (fun z : Real × P => (H z.1, z.2)) '' B =
      ((fun z : Real × P => (a - u * z.1, z.2)) '' {z | z ∈ B ∧ 0 ≤ z.1}) ∪
        (Icc a b ×ˢ Q) ∪
      ((fun z : Real × P => (b + w * z.1, z.2)) '' {z | z ∈ B ∧ 0 ≤ z.1}) := by
  have hl : H (-(1 / 4)) = a - u / 4 := by
    rw [hlow _ le_rfl]
    ring
  have hr : H (1 / 4) = b + w / 4 := by
    rw [hhigh _ le_rfl]
    ring
  have hcentral (q : P) (hq : q ∈ Q) (y : Real)
      (hy : y ∈ Icc (a - u / 4) (b + w / 4)) :
      (y, q) ∈ (fun z : Real × P => (H z.1, z.2)) '' B := by
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc
      (show (-(1 / 4) : Real) ≤ 1 / 4 by norm_num)
      hH.continuousOn
      (show y ∈ Icc (H (-(1 / 4))) (H (1 / 4)) by rwa [hl, hr])
    exact ⟨(t, q), (hbelt t q (abs_le.mpr ht)).mpr hq, Prod.ext hty rfl⟩
  apply Subset.antisymm
  · rintro z ⟨⟨t, q⟩, htB, rfl⟩
    by_cases htlow : t ≤ -(1 / 4)
    · refine Or.inl (Or.inl ⟨(-t, q), ⟨(hsym t q).mp htB, by dsimp; linarith⟩, ?_⟩)
      refine Prod.ext ?_ rfl
      dsimp only
      rw [hlow t htlow]
      ring
    by_cases hthigh : 1 / 4 ≤ t
    · refine Or.inr ⟨(t, q), ⟨htB, by dsimp; linarith⟩, ?_⟩
      exact Prod.ext (hhigh t hthigh).symm rfl
    have ht : |t| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hq : q ∈ Q := (hbelt t q ht).mp htB
    have hylo : a - u / 4 ≤ H t := by
      rw [← hl]
      exact hmono (abs_le.mp ht).1
    have hyhi : H t ≤ b + w / 4 := by
      rw [← hr]
      exact hmono (abs_le.mp ht).2
    by_cases hya : H t ≤ a
    · let z := (a - H t) / u
      have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hya) hu.le
      have hz1 : z ≤ 1 / 4 := (div_le_iff₀ hu).mpr (by linarith)
      refine Or.inl (Or.inl ⟨(z, q),
        ⟨(hbelt z q (abs_le.mpr ⟨by linarith, hz1⟩)).mpr hq, hz0⟩, ?_⟩)
      refine Prod.ext ?_ rfl
      change a - u * ((a - H t) / u) = H t
      field_simp
      ring
    by_cases hyb : b ≤ H t
    · let z := (H t - b) / w
      have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hyb) hw.le
      have hz1 : z ≤ 1 / 4 := (div_le_iff₀ hw).mpr (by linarith)
      refine Or.inr ⟨(z, q),
        ⟨(hbelt z q (abs_le.mpr ⟨by linarith, hz1⟩)).mpr hq, hz0⟩, ?_⟩
      refine Prod.ext ?_ rfl
      change b + w * ((H t - b) / w) = H t
      field_simp
      ring
    exact Or.inl (Or.inr ⟨⟨le_of_lt (lt_of_not_ge hya), le_of_lt (lt_of_not_ge hyb)⟩, hq⟩)
  · intro z hz
    rcases hz with (hz | hz) | hz
    · rcases hz with ⟨⟨t, q⟩, ⟨htB, ht0⟩, rfl⟩
      by_cases ht : 1 / 4 ≤ t
      · refine ⟨(-t, q), (hsym t q).mp htB, ?_⟩
        refine Prod.ext ?_ rfl
        dsimp only
        rw [hlow (-t) (by linarith)]
        ring
      · have hq : q ∈ Q := (hbelt t q (abs_le.mpr ⟨by dsimp at ht0; linarith,
          le_of_lt (lt_of_not_ge ht)⟩)).mp htB
        exact hcentral q hq (a - u * t) ⟨by nlinarith, by nlinarith⟩
    · exact hcentral z.2 hz.2 z.1 ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    · rcases hz with ⟨⟨t, q⟩, ⟨htB, ht0⟩, rfl⟩
      by_cases ht : 1 / 4 ≤ t
      · refine ⟨(t, q), htB, ?_⟩
        exact Prod.ext (hhigh t ht) rfl
      · have hq : q ∈ Q := (hbelt t q (abs_le.mpr ⟨by dsimp at ht0; linarith,
          le_of_lt (lt_of_not_ge ht)⟩)).mp htB
        exact hcentral q hq (b + w * t) ⟨by nlinarith, by nlinarith⟩

theorem image_heightStretch_eq_caps_union_cylinder
    {P : Type*} (B : Set (Real × P)) (Q : Set P)
    (hbelt : ∀ t q, |t| ≤ 1 / 4 → ((t, q) ∈ B ↔ q ∈ Q))
    (hsym : ∀ t q, (t, q) ∈ B ↔ (-t, q) ∈ B)
    {a b s : Real} (hab : a ≤ b) (hs : 0 < s) :
    (fun z : Real × P => (cappedCylinderHeight a b s z.1, z.2)) '' B =
      ((fun z : Real × P => (a - s * z.1, z.2)) '' {z | z ∈ B ∧ 0 ≤ z.1}) ∪
        (Icc a b ×ˢ Q) ∪
      ((fun z : Real × P => (b + s * z.1, z.2)) '' {z | z ∈ B ∧ 0 ≤ z.1}) :=
  image_heightMap_eq_caps_union_cylinder B Q hbelt hsym hab hs hs _
    (contDiff_cappedCylinderHeight a b s).continuous
    (strictMono_cappedCylinderHeight hab hs).monotone
    (cappedCylinderHeight_of_le a b s) (cappedCylinderHeight_of_ge a b s)

end Poincare.Manifold.Schoenflies.CappedCylinder
