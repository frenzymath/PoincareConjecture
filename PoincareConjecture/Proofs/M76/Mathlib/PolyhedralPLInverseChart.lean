import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace X]

theorem PolyhedralPLInCharts.locallyPiecewiseAffineOn_inverse_comp
    {e : ι → OpenPartialHomeomorph X F} {f : E → X} {S : Set E}
    (hf : PolyhedralPLInCharts e f S) (hinj : InjOn f S)
    (c : OpenPartialHomeomorph X F)
    (hcompat : ∀ i, c.symm.trans (e i) ∈ piecewiseAffineGroupoid F)
    {g : G → F} {q : G → E} {U : Set G}
    (hg : LocallyPiecewiseAffineOn g U) (hq : ContinuousOn q U)
    (hqS : MapsTo q U S) (hgt : MapsTo g U c.target)
    (heq : ∀ y ∈ U, f (q y) = c.symm (g y)) :
    LocallyPiecewiseAffineOn q U := by
  intro x hx
  obtain ⟨i, J, O, hJ, hJS, hO, hxO, hOJ, hfJ, hcoords⟩ :=
    hf.coordinates ⟨q x, hqS hx⟩
  let qS : U → S := fun y => ⟨q y, hqS y.property⟩
  have hqSc : Continuous qS := hq.domRestrict.subtype_mk _
  let V : Set G := (Subtype.val : U → G) '' (qS ⁻¹' O)
  have hV : IsOpen V := hg.isOpen.isOpenMap_subtype_val _ (hO.preimage hqSc)
  have hxV : x ∈ V := ⟨⟨x, hx⟩, hxO, rfl⟩
  have hVU : V ⊆ U := by rintro _ ⟨y, _, rfl⟩; exact y.property
  have hqJ : MapsTo q V J.space := by
    rintro y ⟨z, hz, rfl⟩
    exact hOJ ⟨qS z, hz, rfl⟩
  have hfinj : InjOn ((e i) ∘ f) J.space := by
    intro y hy z hz h
    exact hinj (hJS hy) (hJS hz) ((e i).injOn (hfJ hy) (hfJ hz) h)
  obtain ⟨b, hb, hbval⟩ := hcoords.exists_homeomorph_image hfinj
  obtain ⟨r, hr, hrval⟩ := hb.symm
  have hrleft (y : E) (hy : y ∈ J.space) : r (e i (f y)) = y := by
    have h := hrval (b ⟨y, hy⟩)
    rw [b.symm_apply_apply] at h
    simpa only [hbval, Function.comp_apply] using h.symm
  have hchange := ((mem_piecewiseAffineGroupoid_iff F (c.symm.trans (e i))).mp
    (hcompat i)).1
  have hsub : V ⊆ U ∩ g ⁻¹' (c.symm.trans (e i)).source := by
    intro y hy
    refine ⟨hVU hy, hgt (hVU hy), ?_⟩
    change c.symm (g y) ∈ (e i).source
    rw [← heq y (hVU hy)]
    exact hfJ (hqJ hy)
  have hlocal := (hchange.comp hg).mono hV hsub
  obtain ⟨K, hK, hxK, hKV, hmap⟩ := hlocal x hxV
  have hmap_image : MapsTo ((c.symm.trans (e i)) ∘ g) K.space
      (((e i) ∘ f) '' J.space) := by
    intro y hy
    refine ⟨q y, hqJ (hKV hy), ?_⟩
    change e i (f (q y)) = e i (c.symm (g y))
    rw [heq y (hVU (hKV hy))]
  have hqK := hr.comp (hmap.finitePiecewiseAffineOn hK) hmap_image
  have hqK' : FinitePiecewiseAffineOn q K.space := hqK.congr (by
    intro y hy
    change r (e i (c.symm (g y))) = q y
    rw [← heq y (hVU (hKV hy))]
    exact hrleft (q y) (hqJ (hKV hy)))
  obtain ⟨R, hR, hRs, hqR⟩ := hqK'
  exact ⟨R, hR, hRs.symm ▸ hxK, hRs.subset.trans (hKV.trans hVU), hqR⟩

end Geometry
