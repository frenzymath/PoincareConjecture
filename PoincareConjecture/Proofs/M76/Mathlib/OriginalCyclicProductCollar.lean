import PoincareConjecture.Proofs.M76.Mathlib.OriginalCoreProductBox
import PoincareConjecture.Proofs.M76.Mathlib.CyclicBoxCoreAgreement
import PoincareConjecture.Proofs.M76.Mathlib.PolygonInteriorCutArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem exists_original_cyclic_product_collar
    (P : Polygon E (n + 3)) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    (F f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → E)
    {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box r))
    (hinj : ∀ i, InjOn (F i) (box r))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = P.cutArc t i)
    (hlateral : ∀ i (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F i ((u, if j then r else -r), z) =
        f (if j then finRotate (n + 3) i else i) ((u, 0), z))
    (hcontact : ∀ i, (F i '' box r) ∩ (F (finRotate (n + 3) i) '' box r) =
      f (finRotate (n + 3) i) '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r))
    (hdisjoint : ∀ i j, i ≠ j → finRotate (n + 3) i ≠ j → finRotate (n + 3) j ≠ i →
      Disjoint (F i '' box r) (F j '' box r)) :
    ∃ e : (P.boundary ℝ ×ˢ base r : Set (E × (ℝ × ℝ))) ≃ₜ (⋃ i, F i '' box r),
      e.IsFinitePL ∧
      ∀ (i : Fin (n + 3)) (x : box r),
        (e.symm ⟨F i x, mem_iUnion.mpr ⟨i, mem_image_of_mem (F i) x.property⟩⟩ :
          E × (ℝ × ℝ)) =
            (F i ((0, (x : (ℝ × ℝ) × ℝ).1.2), 0),
              ((x : (ℝ × ℝ) × ℝ).1.1, (x : (ℝ × ℝ) × ℝ).2)) := by
  let S (i : Fin (n + 3)) : Set (E × (ℝ × ℝ)) := P.cutArc t i ×ˢ base r
  let T (i : Fin (n + 3)) : Set E := F i '' box r
  choose e he heinv using fun i : Fin (n + 3) =>
    exists_original_core_product_box (F i) hr (hF i) (hinj i) (hcore i)
  let α (i : Fin (n + 3)) (x : (ℝ × ℝ) × ℝ) : E × (ℝ × ℝ) :=
    (F i ((0, x.1.2), 0), (x.1.1, x.2))
  have hα (i j : Fin (n + 3)) (x y : (ℝ × ℝ) × ℝ)
      (hx : x ∈ box r) (hy : y ∈ box r) : F i x = F j y ↔ α i x = α j y :=
    cyclic_box_eq_iff_core_coordinates (finRotate (n + 3)) F f hr hinj hlateral
      hcontact hdisjoint i j hx hy
  have hrepresentation (i : Fin (n + 3)) (y : S i) :
      ∃ x : box r, F i x = (e i y : E) ∧ α i x = (y : E × (ℝ × ℝ)) := by
    obtain ⟨x, hx, hxy⟩ := (e i y).property
    refine ⟨⟨x, hx⟩, hxy, ?_⟩
    have hpoint : (⟨F i x, mem_image_of_mem (F i) hx⟩ : T i) = e i y :=
      Subtype.ext hxy
    have h := heinv i ⟨x, hx⟩
    rw [hpoint, (e i).symm_apply_apply] at h
    exact h.symm
  have hoverlap (i j : Fin (n + 3)) (y : S i) :
      (y : E × (ℝ × ℝ)) ∈ S j ↔ (e i y : E) ∈ T j := by
    obtain ⟨x, hxi, hxα⟩ := hrepresentation i y
    constructor
    · intro hyj
      obtain ⟨z, hzj, hzα⟩ := hrepresentation j ⟨y, hyj⟩
      have hFij : F i x = F j z := (hα i j x z x.property z.property).mpr
        (hxα.trans hzα.symm)
      exact ⟨z, z.property, hFij.symm.trans hxi⟩
    · intro hyj
      obtain ⟨z, hz, hzi⟩ := hyj
      have hαxz : α i x = α j z := (hα i j x z x.property hz).mp
        (hxi.trans hzi.symm)
      let hright := (e j).symm ⟨F j z, mem_image_of_mem (F j) hz⟩
      have hcoord : (hright : E × (ℝ × ℝ)) = (y : E × (ℝ × ℝ)) := by
        dsimp only [hright]
        exact (heinv j ⟨z, hz⟩).trans (hαxz.symm.trans hxα)
      exact hcoord ▸ hright.property
  have hagree (i j : Fin (n + 3)) (y : E × (ℝ × ℝ))
      (hyi : y ∈ S i) (hyj : y ∈ S j) : (e i ⟨y, hyi⟩ : E) = e j ⟨y, hyj⟩ := by
    obtain ⟨x, hxi, hxα⟩ := hrepresentation i ⟨y, hyi⟩
    obtain ⟨z, hzj, hzα⟩ := hrepresentation j ⟨y, hyj⟩
    exact hxi.symm.trans (((hα i j x z x.property z.property).mpr
      (hxα.trans hzα.symm)).trans hzj)
  obtain ⟨g, hg, hgval⟩ := Homeomorph.exists_iUnion_finitePL S T e he hoverlap hagree
  have hsource : (⋃ i, S i) = P.boundary ℝ ×ˢ base r := by
    ext y
    simp only [S, mem_iUnion, mem_prod]
    constructor
    · rintro ⟨i, hi, hy⟩
      exact ⟨(P.iUnion_cutArc t ht).subset (mem_iUnion.mpr ⟨i, hi⟩), hy⟩
    · rintro ⟨hy, hz⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp ((P.iUnion_cutArc t ht).symm.subset hy)
      exact ⟨i, hi, hz⟩
  let H := (Homeomorph.setCongr hsource.symm).trans
    (g.trans (Homeomorph.setCongr rfl))
  have hH : H.IsFinitePL := hg.setCongr hsource rfl
  refine ⟨H, hH, ?_⟩
  intro i x
  let y : T i := ⟨F i x, mem_image_of_mem (F i) x.property⟩
  let z : S i := (e i).symm y
  have hzval : (H ⟨z, hsource.subset (mem_iUnion.mpr ⟨i, z.property⟩)⟩ : E) = F i x := by
    change (g ⟨z, mem_iUnion.mpr ⟨i, z.property⟩⟩ : E) = F i x
    rw [hgval i z]
    exact congrArg Subtype.val ((e i).apply_symm_apply y)
  have hpoint : H ⟨z, hsource.subset (mem_iUnion.mpr ⟨i, z.property⟩)⟩ =
      ⟨F i x, mem_iUnion.mpr ⟨i, mem_image_of_mem (F i) x.property⟩⟩ := Subtype.ext hzval
  rw [← hpoint, H.symm_apply_apply]
  exact heinv i x

end Polygon
