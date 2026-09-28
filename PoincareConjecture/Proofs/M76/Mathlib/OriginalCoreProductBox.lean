import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_original_core_product_box
    (F : ((ℝ × ℝ) × ℝ) → E) {r : ℝ} (hr : 0 < r)
    (hF : FinitePiecewiseAffineOn F (box r)) (hinj : InjOn F (box r))
    {C : Set E} (hcore : F '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = C) :
    ∃ e : (C ×ˢ base r : Set (E × (ℝ × ℝ))) ≃ₜ (F '' box r),
      e.IsFinitePL ∧
      ∀ x : box r,
        (e.symm ⟨F x, mem_image_of_mem F x.property⟩ : E × (ℝ × ℝ)) =
          (F ((0, (x : (ℝ × ℝ) × ℝ).1.2), 0),
            ((x : (ℝ × ℝ) × ℝ).1.1, (x : (ℝ × ℝ) × ℝ).2)) := by
  let p : ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ) :=
    ((0 : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))).prod 0
  let q : ((ℝ × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).prod
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)
  let α : ((ℝ × ℝ) × ℝ) → E × (ℝ × ℝ) := fun x => (F (p x), q x)
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hpbox (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box r) : p x ∈ box r :=
    ⟨⟨hzero, hx.1.2⟩, hzero⟩
  have hpcore (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box r) : F (p x) ∈ C :=
    hcore.subset ⟨p x, ⟨⟨rfl, hx.1.2⟩, rfl⟩, rfl⟩
  have hFcopy := hF
  obtain ⟨K, hK, hKs, _⟩ := hFcopy
  have hpPL : FinitePiecewiseAffineOn p (box r) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine p.toContinuousAffineMap⟩
  have hFp := hF.comp hpPL hpbox
  obtain ⟨J, hJ, hJs, hJf⟩ := hFp
  have hα : FinitePiecewiseAffineOn α (box r) := by
    refine ⟨J, hJ, hJs, ?_⟩
    intro s hs
    obtain ⟨a, ha⟩ := hJf s hs
    exact ⟨a.prod q.toContinuousAffineMap, fun x hx => Prod.ext (ha hx) rfl⟩
  have hαinj : InjOn α (box r) := by
    intro x hx y hy hxy
    have hFxy := congrArg Prod.fst hxy
    change F (p x) = F (p y) at hFxy
    have hmiddle := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.2)
      (hinj (hpbox x hx) (hpbox y hy) hFxy)
    change x.1.2 = y.1.2 at hmiddle
    have hqxy := congrArg Prod.snd hxy
    change q x = q y at hqxy
    have hfirst := congrArg Prod.fst hqxy
    change x.1.1 = y.1.1 at hfirst
    have hlast := congrArg Prod.snd hqxy
    change x.2 = y.2 at hlast
    exact Prod.ext (Prod.ext hfirst hmiddle) hlast
  have hαimage : α '' box r = C ×ˢ base r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hpcore x hx, hx.1.1, hx.2⟩
    · intro hy
      obtain ⟨x, hx, hFx⟩ := hcore.symm.subset hy.1
      have hxfirst : x.1.1 = 0 := hx.1.1
      have hxlast : x.2 = 0 := hx.2
      have hpx : p ((y.2.1, x.1.2), y.2.2) = x :=
        Prod.ext (Prod.ext hxfirst.symm rfl) hxlast.symm
      refine ⟨((y.2.1, x.1.2), y.2.2), ⟨⟨hy.2.1, hx.1.2⟩, hy.2.2⟩, ?_⟩
      exact Prod.ext ((congrArg F hpx).trans hFx) rfl
  obtain ⟨a, ha, haval⟩ := hα.exists_homeomorph_image hαinj
  obtain ⟨b, hb, hbval⟩ := hF.exists_homeomorph_image hinj
  let e := (Homeomorph.setCongr hαimage.symm).trans
    ((a.symm.trans b).trans (Homeomorph.setCongr rfl))
  have he : e.IsFinitePL := (ha.symm.trans hb).setCongr hαimage rfl
  refine ⟨e, he, ?_⟩
  intro x
  have hbx : b x = ⟨F x, mem_image_of_mem F x.property⟩ := Subtype.ext (hbval x)
  change (a (b.symm ⟨F x, mem_image_of_mem F x.property⟩) : E × (ℝ × ℝ)) = _
  rw [← hbx, b.symm_apply_apply]
  exact haval x

end Geometry
