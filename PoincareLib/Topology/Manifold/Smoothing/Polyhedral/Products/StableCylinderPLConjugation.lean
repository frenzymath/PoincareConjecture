import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.PLChartPermutations
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.StableCylinderConjugation

/-!
# PL coordinates of the actual stable cylinder conjugation

Reassociation and swapping use literal real linear maps.
The old stable map, the supported circle-height rotation,
and its inverse compose on their whole actual cylinders.
See Hamilton 1976, p. 66 and M76 derivation270.
-/

set_option autoImplicit false

open Set Geometry

namespace StableCylinder

variable {E F D X Y C ι κ nu : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace C]

/-- The same supported circle-height map acts chartwise PL
over every base coordinate. See M76 derivation270. -/
theorem plInCharts_overBase
    {Q : ι → OpenPartialHomeomorph E X} {S : nu → OpenPartialHomeomorph D C}
    (hQ : PLInCharts Q Q id univ) (hS : PLInCharts S S id univ)
    (hQc : ∀ x, ∃ i, x ∈ (Q i).target) (hSc : ∀ z, ∃ k, z ∈ (S k).target)
    (L : (C × ℝ) ≃ₜ (C × ℝ))
    (hL : PLInCharts (prodCharts S (realCharts ℝ))
      (prodCharts S (realCharts ℝ)) L univ) :
    PLInCharts (prodCharts (prodCharts Q S) (realCharts ℝ))
      (prodCharts (prodCharts Q S) (realCharts ℝ)) (overBase X L) univ := by
  have hreal := plInCharts_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
  have hmid := (hQ.prodMap hL).mono isOpen_univ
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hcover := prodCharts_cover Q (prodCharts S (realCharts ℝ)) hQc
    (prodCharts_cover S (realCharts ℝ) hSc (realCharts_cover ℝ))
  have hfirst := hmid.comp_mapsTo (plInCharts_prodAssoc hQ hS hreal)
    hcover (fun _ _ => mem_univ _)
  exact (plInCharts_prodAssoc_symm hQ hS hreal).comp_mapsTo hfirst
    hcover (fun _ _ => mem_univ _)

/-- Applying the old stable map to its base and height
while leaving the new circle fixed is chartwise PL on the
whole original unit-height cylinder. See derivation270. -/
theorem plInCharts_middleMap
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    {S : nu → OpenPartialHomeomorph D C}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ)
    (hS : PLInCharts S S id univ)
    (hQc : ∀ x, ∃ i, x ∈ (Q i).target) (hRc : ∀ y, ∃ j, y ∈ (R j).target)
    (hSc : ∀ z, ∃ k, z ∈ (S k).target)
    (f : X × ℝ → Y × ℝ)
    (hf : PLInCharts (prodCharts Q (realCharts ℝ)) (prodCharts R (realCharts ℝ))
      f (univ ×ˢ Ioo (-1) 1)) :
    PLInCharts (prodCharts (prodCharts Q S) (realCharts ℝ))
      (prodCharts (prodCharts R S) (realCharts ℝ)) (middleMap (C := C) f)
        (univ ×ˢ Ioo (-1) 1) := by
  have hreal := plInCharts_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
  have hswap := (Geometry.plInCharts_swapLast hQ hS hreal hQc hSc (realCharts_cover ℝ)).mono
    (U' := (univ : Set (X × C)) ×ˢ Ioo (-1 : ℝ) 1)
    (isOpen_univ.prod isOpen_Ioo) (subset_univ _)
  have hprod := hf.prodMap hS
  have hfirst := hprod.comp_mapsTo hswap
    (prodCharts_cover (prodCharts Q (realCharts ℝ)) S
      (prodCharts_cover Q (realCharts ℝ) hQc (realCharts_cover ℝ)) hSc)
    (fun _ hz => ⟨⟨mem_univ _, hz.2⟩, mem_univ _⟩)
  exact (Geometry.plInCharts_swapLast hR hreal hS hRc (realCharts_cover ℝ) hSc).comp_mapsTo
    hfirst (prodCharts_cover (prodCharts R (realCharts ℝ)) S
      (prodCharts_cover R (realCharts ℝ) hRc (realCharts_cover ℝ)) hSc)
    (fun _ _ => mem_univ _)

/-- The actual cylinder conjugation has PL expressions
throughout its entire unit-height domain. The original
stable image and forward rotation remain inside the actual
unit cylinders before each composition. See derivation270. -/
theorem plInCharts_conjugation
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    {S : nu → OpenPartialHomeomorph D C}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ)
    (hS : PLInCharts S S id univ)
    (hQc : ∀ x, ∃ i, x ∈ (Q i).target) (hRc : ∀ y, ∃ j, y ∈ (R j).target)
    (hSc : ∀ z, ∃ k, z ∈ (S k).target)
    (L : (C × ℝ) ≃ₜ (C × ℝ))
    (hL : MapsTo L (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1))
    (hLPL : PLInCharts (prodCharts S (realCharts ℝ))
      (prodCharts S (realCharts ℝ)) L univ)
    (hLiPL : PLInCharts (prodCharts S (realCharts ℝ))
      (prodCharts S (realCharts ℝ)) L.symm univ)
    (f : X × ℝ → Y × ℝ)
    (hf : PLInCharts (prodCharts Q (realCharts ℝ)) (prodCharts R (realCharts ℝ))
      f (univ ×ˢ Ioo (-1) 1)) :
    PLInCharts (prodCharts (prodCharts Q S) (realCharts ℝ))
      (prodCharts (prodCharts R S) (realCharts ℝ)) (conjugation L f)
        (univ ×ˢ Ioo (-1) 1) := by
  have hpre := (plInCharts_overBase hQ hS hQc hSc L hLPL).mono
    (U' := (univ : Set (X × C)) ×ˢ Ioo (-1 : ℝ) 1)
    (isOpen_univ.prod isOpen_Ioo) (subset_univ _)
  have hmid := plInCharts_middleMap hQ hR hS hQc hRc hSc f hf
  have hfirst := hmid.comp_mapsTo hpre
    (prodCharts_cover (prodCharts Q S) (realCharts ℝ)
      (prodCharts_cover Q S hQc hSc) (realCharts_cover ℝ))
    (fun _ hz => ⟨mem_univ _, (hL ⟨mem_univ _, hz.2⟩).2⟩)
  exact (plInCharts_overBase hR hS hRc hSc L.symm hLiPL).comp_mapsTo hfirst
    (prodCharts_cover (prodCharts R S) (realCharts ℝ)
      (prodCharts_cover R S hRc hSc) (realCharts_cover ℝ))
    (fun _ _ => mem_univ _)

end StableCylinder
