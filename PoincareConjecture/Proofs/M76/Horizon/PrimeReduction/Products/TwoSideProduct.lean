import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates









set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_reflected_unit_product
    {N U : Set E} (C : (N ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)) ≃ₜ U)
    (hC : C.IsFinitePL) :
    ∃ D : (N ×ˢ Icc (-1 : ℝ) 0 : Set (E × ℝ)) ≃ₜ U,
      D.IsFinitePL ∧ ∀ z,
        (D z : E) = C ⟨((z : E × ℝ).1, -(z : E × ℝ).2),
          ⟨z.property.1, by constructor <;> linarith [z.property.2.1, z.property.2.2]⟩⟩ := by
  let a : (E × ℝ) ≃ᴬ[ℝ] (E × ℝ) :=
    ((ContinuousLinearEquiv.refl ℝ E).prodCongr (ContinuousLinearEquiv.neg ℝ)).toContinuousAffineEquiv
  let b : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.refl ℝ E
  have hsource : a '' (N ×ˢ Icc (0 : ℝ) 1) = N ×ˢ Icc (-1 : ℝ) 0 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x.1 ∈ N ∧ -1 ≤ -x.2 ∧ -x.2 ≤ 0
      exact ⟨hx.1, by linarith [hx.2.2], by linarith [hx.2.1]⟩
    · intro hz
      refine ⟨(z.1, -z.2), ⟨hz.1, ?_, ?_⟩, ?_⟩
      · linarith [hz.2.2]
      · linarith [hz.2.1]
      · change (z.1, - -z.2) = z
        simp only [neg_neg, Prod.eta]
  have htarget : b '' U = U := image_id U
  let G := (a.toHomeomorph.image (N ×ˢ Icc (0 : ℝ) 1)).symm.trans
    (C.trans (b.toHomeomorph.image U))
  let D := (Homeomorph.setCongr hsource.symm).trans (G.trans (Homeomorph.setCongr htarget))
  refine ⟨D, (hC.affine_conjugate a b).setCongr hsource htarget, ?_⟩
  intro z
  rfl




theorem exists_two_side_product
    (N : Set E) (U : Bool → Set E)
    (C : ∀ b, (N ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)) ≃ₜ U b)
    (hC : ∀ b, (C b).IsFinitePL)
    (hbase : ∀ b (x : E) (hx : x ∈ N),
      (C b ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x)
    (hzero : ∀ b z, (C b z : E) ∈ N ↔ (z : E × ℝ).2 = 0)
    (hU : U true ∩ U false = N) :
    ∃ H : (N ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) ≃ₜ ↥(U true ∪ U false),
      H.IsFinitePL ∧
      (∀ z : (N ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)),
        (H ⟨z, ⟨z.property.1, by linarith [z.property.2.1], z.property.2.2⟩⟩ : E) = C true z) ∧
      (∀ z : (N ×ˢ Icc (-1 : ℝ) 0 : Set (E × ℝ)),
        (H ⟨z, ⟨z.property.1, z.property.2.1, by linarith [z.property.2.2]⟩⟩ : E) =
          C false ⟨((z : E × ℝ).1, -(z : E × ℝ).2),
            ⟨z.property.1, by constructor <;> linarith [z.property.2.1, z.property.2.2]⟩⟩) ∧
      (∀ (x : E) (hx : x ∈ N),
        (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x) ∧
      ∀ z, (H z : E) ∈ N ↔ (z : E × ℝ).2 = 0 := by
  classical
  obtain ⟨D, hD, hDval⟩ := exists_reflected_unit_product (C false) (hC false)
  let S : Bool → Set (E × ℝ) := fun b => if b then N ×ˢ Icc (0 : ℝ) 1 else N ×ˢ Icc (-1 : ℝ) 0
  let F : ∀ b, S b ≃ₜ U b := fun b => Bool.rec D (C true) b
  have hF : ∀ b, (F b).IsFinitePL := by
    intro b
    cases b
    · exact hD
    · exact hC true
  have hFzero (b : Bool) (z : S b) : (F b z : E) ∈ N ↔ (z : E × ℝ).2 = 0 := by
    cases b
    · change (D z : E) ∈ N ↔ (z : E × ℝ).2 = 0
      rw [hDval, hzero]
      exact neg_eq_zero
    · exact hzero true z
  have hFbase (b : Bool) (x : E) (hx : x ∈ N) :
      (F b ⟨(x, 0), by cases b <;> simp [S, hx]⟩ : E) = x := by
    cases b
    · change (D ⟨(x, 0), _⟩ : E) = x
      rw [hDval]
      simpa only [neg_zero] using hbase false x hx
    · exact hbase true x hx
  have hoverlap (b c : Bool) (z : S b) : (z : E × ℝ) ∈ S c ↔ (F b z : E) ∈ U c := by
    by_cases hbc : b = c
    · subst c
      exact iff_of_true z.property (F b z).property
    have hcross : (F b z : E) ∈ U c ↔ (F b z : E) ∈ N := by
      rw [← hU]
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · exact (and_iff_left (F false z).property).symm
      · exact (and_iff_right (F true z).property).symm
      · exact False.elim (hbc rfl)
    rw [hcross, hFzero]
    cases b <;> cases c
    · exact False.elim (hbc rfl)
    · change ((z : E × ℝ).1 ∈ N ∧ 0 ≤ (z : E × ℝ).2 ∧ (z : E × ℝ).2 ≤ 1) ↔ _
      have hz := z.property
      change (z : E × ℝ).1 ∈ N ∧ -1 ≤ (z : E × ℝ).2 ∧ (z : E × ℝ).2 ≤ 0 at hz
      constructor
      · intro h
        linarith [h.2.1, hz.2.2]
      · intro h
        exact ⟨hz.1, by linarith, by linarith⟩
    · change ((z : E × ℝ).1 ∈ N ∧ -1 ≤ (z : E × ℝ).2 ∧ (z : E × ℝ).2 ≤ 0) ↔ _
      have hz := z.property
      change (z : E × ℝ).1 ∈ N ∧ 0 ≤ (z : E × ℝ).2 ∧ (z : E × ℝ).2 ≤ 1 at hz
      constructor
      · intro h
        linarith [h.2.2, hz.2.1]
      · intro h
        exact ⟨hz.1, by linarith, by linarith⟩
    · exact False.elim (hbc rfl)
  have hagree (b c : Bool) (z : E × ℝ) (hb : z ∈ S b) (hc : z ∈ S c) :
      (F b ⟨z, hb⟩ : E) = F c ⟨z, hc⟩ := by
    by_cases hbc : b = c
    · subst c
      rfl
    have ht : z.2 = 0 := by
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · exact le_antisymm hb.2.2 hc.2.1
      · exact le_antisymm hc.2.2 hb.2.1
      · exact False.elim (hbc rfl)
    have hx : z.1 ∈ N := by cases b <;> exact hb.1
    rcases z with ⟨x, t⟩
    change t = 0 at ht
    subst t
    exact (hFbase b _ hx).trans (hFbase c _ hx).symm
  have hsource : (⋃ b, S b) = N ×ˢ Icc (-1 : ℝ) 1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, hb⟩ := mem_iUnion.mp hz
      cases b
      · exact ⟨hb.1, hb.2.1, by linarith [hb.2.2]⟩
      · exact ⟨hb.1, by linarith [hb.2.1], hb.2.2⟩
    · intro hz
      rcases le_total 0 z.2 with h | h
      · exact mem_iUnion.mpr ⟨true, ⟨hz.1, h, hz.2.2⟩⟩
      · exact mem_iUnion.mpr ⟨false, ⟨hz.1, hz.2.1, h⟩⟩
  have htarget : (⋃ b, U b) = U true ∪ U false := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      cases b
      · exact Or.inr hb
      · exact Or.inl hb
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨true, hx⟩
      · exact mem_iUnion.mpr ⟨false, hx⟩
  obtain ⟨G, hG, hGval⟩ := exists_iUnion_finitePL S U F hF hoverlap hagree
  let H := (Homeomorph.setCongr hsource.symm).trans (G.trans (Homeomorph.setCongr htarget))
  have hres (b : Bool) (z : S b) :
      (H ⟨z, hsource.subset (mem_iUnion.mpr ⟨b, z.property⟩)⟩ : E) = F b z := hGval b z
  refine ⟨H, hG.setCongr hsource htarget, ?_, ?_, ?_, ?_⟩
  · intro z
    exact hres true z
  · intro z
    exact (hres false z).trans (hDval z)
  · intro x hx
    exact (hres true ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩).trans (hbase true x hx)
  · intro z
    obtain ⟨b, hb⟩ := mem_iUnion.mp (hsource.symm.subset z.property)
    have hv := hres b ⟨z, hb⟩
    change (H z : E) = F b ⟨z, hb⟩ at hv
    rw [hv]
    exact hFzero b ⟨z, hb⟩

end Homeomorph
