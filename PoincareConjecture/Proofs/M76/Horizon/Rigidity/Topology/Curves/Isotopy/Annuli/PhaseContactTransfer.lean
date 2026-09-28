import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.ProjectedDiskMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.UpperComponents



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem supported_homeomorph_mem_iff {D T : Set P2} (hDT : D ⊆ T)
    (H : P2 ≃ₜ P2) (hfix : ∀ x, x ∉ interior D → H x = x) (x : P2) :
    x ∈ T ↔ H x ∈ T := by
  have hmaps : MapsTo H D D := by
    intro y hy
    by_contra hn
    have he : H y = y := H.injective (hfix (H y) (fun hi => hn (interior_subset hi)))
    exact hn (he.symm ▸ hy)
  by_cases hx : x ∈ D
  · exact ⟨fun _ => hDT (hmaps hx), fun _ => hDT hx⟩
  · rw [hfix x (fun hi => hx (interior_subset hi))]

theorem projected_motion_eq_on_window
    {D : Set P2} {a b c : ℝ} (hwidth : b - a < 32)
    (hD : D ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (H : P2 ≃ₜ P2) (hfix : ∀ y, y ∉ interior D → H y = y)
    (A : Ann ≃ₜ Ann)
    (hoff : ∀ x : Ann, (x : P2) ∉ interior (annularLiftProjectionAt c '' D) → A x = x)
    (hact : ∀ (x : Ann) (y : P2), y ∈ D → (x : P2) = annularLiftProjectionAt c y →
      (A x : P2) = annularLiftProjectionAt c (H y))
    (x : Ann) (y : P2) (hy : y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (hxy : (x : P2) = annularLiftProjectionAt c y) :
    (A x : P2) = annularLiftProjectionAt c (H y) := by
  by_cases hyD : y ∈ D
  · exact hact x y hyD hxy
  · have hout : (x : P2) ∉ annularLiftProjectionAt c '' D := by
      rintro ⟨z, hz, heq⟩
      have hzy := (injOn_annularLiftProjectionAt_strip c hwidth) (hD hz) hy (heq.trans hxy)
      exact hyD (hzy ▸ hz)
    rw [hoff x (fun hi => hout (interior_subset hi)), hfix y (fun hi => hyD (interior_subset hi))]
    exact hxy

theorem projected_two_moves_eq_on_window
    {D E : Set P2} {a b c : ℝ} (hwidth : b - a < 32)
    (hD : D ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (hE : E ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (H J : P2 ≃ₜ P2)
    (hfix : ∀ y, y ∉ interior D → H y = y)
    (jfix : ∀ y, y ∉ interior E → J y = y)
    (A B : Ann ≃ₜ Ann)
    (hoff : ∀ x : Ann, (x : P2) ∉ interior (annularLiftProjectionAt c '' D) → A x = x)
    (joff : ∀ x : Ann, (x : P2) ∉ interior (annularLiftProjectionAt c '' E) → B x = x)
    (hact : ∀ (x : Ann) (y : P2), y ∈ D → (x : P2) = annularLiftProjectionAt c y →
      (A x : P2) = annularLiftProjectionAt c (H y))
    (jact : ∀ (x : Ann) (y : P2), y ∈ E → (x : P2) = annularLiftProjectionAt c y →
      (B x : P2) = annularLiftProjectionAt c (J y))
    (x : Ann) (y : P2) (hy : y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (hxy : (x : P2) = annularLiftProjectionAt c y) :
    (B (A x) : P2) = annularLiftProjectionAt c (J (H y)) :=
  projected_motion_eq_on_window hwidth hE J jfix B joff jact (A x) (H y)
    ((supported_homeomorph_mem_iff hD H hfix y).mp hy)
    (projected_motion_eq_on_window hwidth hD H hfix A hoff hact x y hy hxy)

theorem projected_two_moves_radial_contact_iff
    {D E : Set P2} {a b c : ℝ} (hwidth : b - a < 32) (ha : a ≤ 0) (hb : 0 ≤ b)
    (hD : D ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (hE : E ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (H J : P2 ≃ₜ P2)
    (hfix : ∀ y, y ∉ interior D → H y = y)
    (jfix : ∀ y, y ∉ interior E → J y = y)
    (A B : Ann ≃ₜ Ann)
    (hoff : ∀ x : Ann, (x : P2) ∉ interior (annularLiftProjectionAt c '' D) → A x = x)
    (joff : ∀ x : Ann, (x : P2) ∉ interior (annularLiftProjectionAt c '' E) → B x = x)
    (hact : ∀ (x : Ann) (y : P2), y ∈ D → (x : P2) = annularLiftProjectionAt c y →
      (A x : P2) = annularLiftProjectionAt c (H y))
    (jact : ∀ (x : Ann) (y : P2), y ∈ E → (x : P2) = annularLiftProjectionAt c y →
      (B x : P2) = annularLiftProjectionAt c (J y))
    (x : Ann) (r : P2) (hr : r.2 ∈ Icc (-1 : ℝ) 1)
    (hxr : (x : P2) = annulusMap 8 (by norm_num) ((r.1 : Circle), r.2)) :
    B (A x) ∈ range (fun t : I => annulusCylinderHomeomorph (t, (c : Circle))) ↔
      ∃ k : ℤ, (J (H (r.2, r.1 - (c + 32 * (k : ℝ))))).2 = 0 := by
  let T := Icc (-1 : ℝ) 1 ×ˢ Icc a b
  have hheight (y : P2) (hy : y.1 ∈ Icc (-1 : ℝ) 1) :
      (J (H y)).1 ∈ Icc (-1 : ℝ) 1 := by
    exact (supported_homeomorph_mem_iff (fun z hz => (hE hz).1) J jfix (H y)).mp
      ((supported_homeomorph_mem_iff (fun z hz => (hD hz).1) H hfix y).mp hy)
  have hmem (y : P2) : y ∈ T ↔ J (H y) ∈ T :=
    (supported_homeomorph_mem_iff hD H hfix y).trans (supported_homeomorph_mem_iff hE J jfix (H y))
  have hparam (t : I) :
      (annulusCylinderHomeomorph (t, (c : Circle)) : P2) =
        annularLiftProjectionAt c (2 * (t : ℝ) - 1, 0) := by
    rw [annulusCylinderHomeomorph_apply]
    change annulusMap 8 (by norm_num) ((c : Circle), 2 * (t : ℝ) - 1) =
      annulusMap 8 (by norm_num) (((c + 0 : ℝ) : Circle), 2 * (t : ℝ) - 1)
    rw [add_zero]
  have hproject (k : ℤ) : (x : P2) =
      annularLiftProjectionAt c (r.2, r.1 - (c + 32 * (k : ℝ))) := by
    have hp : ((32 * (k : ℝ) : ℝ) : Circle) = 0 :=
      (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨k, by simp [zsmul_eq_mul]; ring⟩
    rw [hxr]
    change annulusMap 8 (by norm_num) ((r.1 : Circle), r.2) =
      annulusMap 8 (by norm_num) (((c + (r.1 - (c + 32 * (k : ℝ))) : ℝ) : Circle), r.2)
    rw [show c + (r.1 - (c + 32 * (k : ℝ))) = r.1 - 32 * (k : ℝ) by ring,
      AddCircle.coe_sub, hp, sub_zero]
  constructor
  · rintro ⟨t, ht⟩
    let y : P2 := (2 * (t : ℝ) - 1, 0)
    have hy : y ∈ T := ⟨⟨by dsimp [y]; linarith [t.property.1],
      by dsimp [y]; linarith [t.property.2]⟩, ha, hb⟩
    let z := H.symm (J.symm y)
    have hz : z ∈ T := (hmem z).mpr (by simpa [z] using hy)
    have hzAnn : annularLiftProjectionAt c z ∈ Ann := by
      apply mem_squareAnnulus_iff_depth.mpr
      change depth 8 (annulusMap 8 (by norm_num) (((c + z.2 : ℝ) : Circle), z.1)) ∈ _
      rw [depth_annulusMap (by norm_num) (by have hh := abs_le.mpr hz.1; linarith)]
      exact hz.1
    let zA : Ann := ⟨annularLiftProjectionAt c z, hzAnn⟩
    have hsame : B (A zA) = B (A x) := by
      apply Subtype.ext
      rw [projected_two_moves_eq_on_window hwidth hD hE H J hfix jfix A B hoff joff hact jact
        zA z hz rfl]
      simp only [z, Homeomorph.apply_symm_apply]
      exact (hparam t).symm.trans (congrArg Subtype.val ht)
    have hzx : annularLiftProjectionAt c z = (x : P2) :=
      congrArg Subtype.val (A.injective (B.injective hsame))
    obtain ⟨k, hk⟩ := (annularLiftProjectionAt_fiber c hr hz.1).mp
      ((hproject 0).symm.trans hzx.symm)
    have hzk : z = (r.2, r.1 - (c + 32 * (k : ℝ))) := by
      apply Prod.ext
      · have hh := congrArg Prod.fst hk
        change r.2 = z.1 + 0 at hh
        linarith
      · have hh := congrArg Prod.snd hk
        change r.1 - (c + 32 * (0 : ℤ)) = z.2 + 32 * (k : ℝ) at hh
        norm_num at hh
        linarith
    refine ⟨k, ?_⟩
    rw [← hzk]
    simp [z, y]
  · rintro ⟨k, hk⟩
    let z : P2 := (r.2, r.1 - (c + 32 * (k : ℝ)))
    have hm : J (H z) ∈ T := ⟨hheight z hr, by rw [hk]; exact ⟨ha, hb⟩⟩
    have hz := (hmem z).mpr hm
    let t : I := ⟨((J (H z)).1 + 1) / 2, by constructor <;> linarith [hm.1.1, hm.1.2]⟩
    refine ⟨t, Subtype.ext ?_⟩
    rw [hparam, projected_two_moves_eq_on_window hwidth hD hE H J hfix jfix A B hoff joff hact jact
      x z hz (hproject k)]
    congr 1
    apply Prod.ext
    · change 2 * (((J (H z)).1 + 1) / 2) - 1 = (J (H z)).1
      ring
    · exact hk.symm

end PoincareConjecture.M76.Dehn
