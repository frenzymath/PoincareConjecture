import PoincareConjecture.Proofs.M76.Mathlib.PLChartMaps

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F G X Y Z ι κ nu : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem plInCharts_prodAssoc
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    {S : nu → OpenPartialHomeomorph G Z}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ)
    (hS : PLInCharts S S id univ) :
    PLInCharts (prodCharts (prodCharts Q R) S) (prodCharts Q (prodCharts R S))
      (Homeomorph.prodAssoc X Y Z) univ := by
  refine ⟨isOpen_univ, (Homeomorph.prodAssoc X Y Z).continuous.continuousOn, ?_⟩
  intro i j
  let A := ContinuousLinearEquiv.prodAssoc ℝ E F G
  have hA := locallyPiecewiseAffineOn_affine A.toContinuousLinearMap.toContinuousAffineMap
    isOpen_univ
  have hcoords := (hQ.coordinates i.1.1 j.1).prodMap
    ((hR.coordinates i.1.2 j.2.1).prodMap (hS.coordinates i.2 j.2.2))
  apply (hcoords.comp hA).mono
    (isOpen_chartMapDomain _ _ _ _ isOpen_univ
      (Homeomorph.prodAssoc X Y Z).continuous.continuousOn)
  intro z hz
  exact ⟨mem_univ _, ⟨⟨⟨hz.1.1.1.1, mem_univ _⟩, hz.2.1⟩,
    ⟨⟨⟨hz.1.1.1.2, mem_univ _⟩, hz.2.2.1⟩,
      ⟨⟨hz.1.1.2, mem_univ _⟩, hz.2.2.2⟩⟩⟩⟩

theorem plInCharts_prodAssoc_symm
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    {S : nu → OpenPartialHomeomorph G Z}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ)
    (hS : PLInCharts S S id univ) :
    PLInCharts (prodCharts Q (prodCharts R S)) (prodCharts (prodCharts Q R) S)
      (Homeomorph.prodAssoc X Y Z).symm univ := by
  refine ⟨isOpen_univ, (Homeomorph.prodAssoc X Y Z).symm.continuous.continuousOn, ?_⟩
  intro i j
  let A := (ContinuousLinearEquiv.prodAssoc ℝ E F G).symm
  have hA := locallyPiecewiseAffineOn_affine A.toContinuousLinearMap.toContinuousAffineMap
    isOpen_univ
  have hcoords := ((hQ.coordinates i.1 j.1.1).prodMap
    (hR.coordinates i.2.1 j.1.2)).prodMap (hS.coordinates i.2.2 j.2)
  apply (hcoords.comp hA).mono
    (isOpen_chartMapDomain _ _ _ _ isOpen_univ
      (Homeomorph.prodAssoc X Y Z).symm.continuous.continuousOn)
  intro z hz
  exact ⟨mem_univ _, ⟨⟨⟨⟨hz.1.1.1, mem_univ _⟩, hz.2.1.1⟩,
    ⟨⟨hz.1.1.2.1, mem_univ _⟩, hz.2.1.2⟩⟩,
      ⟨⟨hz.1.1.2.2, mem_univ _⟩, hz.2.2⟩⟩⟩

theorem plInCharts_prodComm
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ) :
    PLInCharts (prodCharts Q R) (prodCharts R Q) (Homeomorph.prodComm X Y) univ := by
  refine ⟨isOpen_univ, (Homeomorph.prodComm X Y).continuous.continuousOn, ?_⟩
  intro i j
  let A := ContinuousLinearEquiv.prodComm ℝ E F
  have hA := locallyPiecewiseAffineOn_affine A.toContinuousLinearMap.toContinuousAffineMap
    isOpen_univ
  have hcoords := (hR.coordinates i.2 j.1).prodMap (hQ.coordinates i.1 j.2)
  apply (hcoords.comp hA).mono
    (isOpen_chartMapDomain _ _ _ _ isOpen_univ
      (Homeomorph.prodComm X Y).continuous.continuousOn)
  intro z hz
  exact ⟨mem_univ _, ⟨⟨⟨hz.1.1.2, mem_univ _⟩, hz.2.1⟩,
    ⟨⟨hz.1.1.1, mem_univ _⟩, hz.2.2⟩⟩⟩

theorem plInCharts_swapLast
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    {S : nu → OpenPartialHomeomorph G Z}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ)
    (hS : PLInCharts S S id univ)
    (hQc : ∀ x, ∃ i, x ∈ (Q i).target) (hRc : ∀ y, ∃ j, y ∈ (R j).target)
    (hSc : ∀ z, ∃ k, z ∈ (S k).target) :
    PLInCharts (prodCharts (prodCharts Q R) S) (prodCharts (prodCharts Q S) R)
      (fun z : (X × Y) × Z => ((z.1.1, z.2), z.1.2)) univ := by
  have hmid := (hQ.prodMap (plInCharts_prodComm hR hS)).mono isOpen_univ
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hfirst := hmid.comp_mapsTo (plInCharts_prodAssoc hQ hR hS)
    (prodCharts_cover Q (prodCharts R S) hQc (prodCharts_cover R S hRc hSc))
    (fun _ _ => mem_univ _)
  exact (plInCharts_prodAssoc_symm hQ hS hR).comp_mapsTo hfirst
    (prodCharts_cover Q (prodCharts S R) hQc (prodCharts_cover S R hSc hRc))
    (fun _ _ => mem_univ _)

end Geometry
