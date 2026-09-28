import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryInteriorOldGerms
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.LocalCrossingLink

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 800000 in
theorem OriginalGeneralPositionData.boundary_interior_signed_approach
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (a : D) (w : TwoBranchWindow (step.projection ∘ step.inclusion))
    (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
    (J K : SimplicialComplex ℝ V3)
    (hJQ : J.space ⊆ Q.target)
    (hQPL : ∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hQzero : Q (step.projection (step.inclusion (data.initial.map a))) = 0)
    (hKs : K.space = (w.right.trans Q) ''
      (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space)
    (hplane : ∀ y ∈ Q.source,
      y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
        0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0)
    (hbad : ∀ y ∈ Q.source,
      y ∈ (fun z : V2 × V2 ↦
        step.projection (step.inclusion (data.initial.map z.1))) '' data.exceptional →
      y = step.projection (step.inclusion (data.initial.map a)))
    (v : V3) (hvK : v ∈ K.space) (hvJ : v ∈ interior J.space)
    (hvpositive : 0 < (c v).1.1) (hvzero : (c v).2 = 0) :
    v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
    v ∈ closure (K.space ∩ {z | (c z).2 < 0}) := by
  classical
  obtain ⟨H, hzeroH, hHcenter, _hHinv, hsheet, hflat⟩ :=
    data.boundary_interior_old_chart step a w c Q J K hJQ hQPL hQzero hKs
      hplane hbad v hvK hvJ hvpositive hvzero
  let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
  have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
  have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
  let Kshift := hshiftK.embeddedImage shift.injective.injOn
  have hKshifts : Kshift.space = shift '' K.space :=
    hshiftK.embeddedImage_space shift.injective.injOn
  let height : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hheight (z : V3) : height (shift z) = (c z).2 := by
    change (c (-v + z)).2 = (c z).2
    rw [map_add, map_neg]
    change -(c v).2 + (c z).2 = (c z).2
    rw [hvzero, neg_zero, zero_add]
  have hsigns := signed_approach_of_crossing_chart Kshift height
    (c.symm ((0, 0), 1)) (by change (c (c.symm ((0, 0), 1))).2 = 1; rw [c.apply_symm_apply])
    H hzeroH hHcenter hflat (fun z hz ↦ by rw [hKshifts]; exact hsheet z hz)
  have pull (test : ℝ → Prop)
      (hcl : (0 : V3) ∈ closure (Kshift.space ∩ {x | test (height x)})) :
      v ∈ closure (K.space ∩ {x | test ((c x).2)}) := by
    apply _root_.mem_closure_iff.mpr
    intro O hO hvO
    obtain ⟨z, hzO, hzK, hzt⟩ := _root_.mem_closure_iff.mp hcl (shift '' O)
      (shift.toHomeomorph.isOpenMap _ hO) ⟨v, hvO, hshift⟩
    obtain ⟨x, hxO, rfl⟩ := hzO
    have hxK : x ∈ K.space := shift.injective.mem_set_image.mp (hKshifts.subset hzK)
    have hxTest : test ((c x).2) := by
      rw [← hheight x]
      exact hzt
    exact ⟨x, hxO, hxK, hxTest⟩
  exact ⟨pull (fun x ↦ 0 < x) hsigns.1, pull (fun x ↦ x < 0) hsigns.2⟩

set_option maxHeartbeats 800000 in
theorem OriginalGeneralPositionData.boundary_interior_link_sections
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (a : D) (w : TwoBranchWindow (step.projection ∘ step.inclusion))
    (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
    (J K : SimplicialComplex ℝ V3)
    (hJQ : J.space ⊆ Q.target)
    (hQPL : ∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hQzero : Q (step.projection (step.inclusion (data.initial.map a))) = 0)
    (hKs : K.space = (w.right.trans Q) ''
      (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space)
    (hplane : ∀ y ∈ Q.source,
      y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
        0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0)
    (hbad : ∀ y ∈ Q.source,
      y ∈ (fun z : V2 × V2 ↦
        step.projection (step.inclusion (data.initial.map z.1))) '' data.exceptional →
      y = step.projection (step.inclusion (data.initial.map a)))
    (hK : K.faces.Finite)
    (v : V3) (hvK : v ∈ K.vertices) (hvJ : v ∈ interior J.space)
    (hvpositive : 0 < (c v).1.1) (hvzero : (c v).2 = 0) :
    ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
    (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
    ∃ z ∈ (K.link v).space, (c z).2 < 0 := by
  classical
  obtain ⟨H, hzeroH, hHcenter, hHinv, hsheet, hflat⟩ :=
    data.boundary_interior_old_chart step a w c Q J K hJQ hQPL hQzero hKs
      hplane hbad v (K.vertices_subset_space hvK) hvJ hvpositive hvzero
  let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
  have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
  have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
  let Kshift := hshiftK.embeddedImage shift.injective.injOn
  have hKshift : Kshift.faces.Finite := hshiftK.embeddedImage_finite shift.injective.injOn hK
  have hKshifts : Kshift.space = shift '' K.space :=
    hshiftK.embeddedImage_space shift.injective.injOn
  have hzeroKshift : (0 : V3) ∈ Kshift.vertices := by
    rw [hshiftK.embeddedImage_vertices shift.injective.injOn]
    exact ⟨v, hvK, hshift⟩
  let height : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hheight (z : V3) : height (shift z) = (c z).2 := by
    change (c (-v + z)).2 = (c z).2
    rw [map_add, map_neg]
    change -(c v).2 + (c z).2 = (c z).2
    rw [hvzero, neg_zero, zero_add]
  have hparts (z : V3) (hz : z ∈ H.source) :
      (z ∈ Kshift.space ↔ (H z).1.1 = 0) ∧ (height z = 0 ↔ (H z).2 = 0) := by
    refine ⟨?_, hflat z hz⟩
    rw [hKshifts]
    exact hsheet z hz
  have hzeroCount := link_zero_ncard_of_crossing_chart Kshift hKshift hzeroKshift
    height.toLinearMap
    H hzeroH hHcenter hHinv (fun z hz ↦ and_congr (hparts z hz).1 (hparts z hz).2)
  have hsurface := signed_approach_of_crossing_chart Kshift height
    (c.symm ((0, 0), 1)) (by change (c (c.symm ((0, 0), 1))).2 = 1; rw [c.apply_symm_apply])
    H hzeroH hHcenter (fun z hz ↦ (hparts z hz).2) (fun z hz ↦ (hparts z hz).1)
  have hsigns := Kshift.exists_both_link_signs_of_surface_accumulation
    hKshift hzeroKshift height.toLinearMap hsurface.1 hsurface.2
  have hlink : (Kshift.link 0).space = shift '' (K.link v).space := by
    have h := hshiftK.embeddedImage_link_space shift.injective.injOn hvK
    change (Kshift.link (shift v)).space = shift '' (K.link v).space at h
    simpa only [hshift] using h
  have hzeros : shift '' ((K.link v).space ∩ {z | (c z).2 = 0}) =
      (Kshift.link 0).space ∩ {z | height z = 0} := by
    rw [hlink]
    ext x
    constructor
    · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
      exact ⟨mem_image_of_mem shift hz, (hheight z).trans hz0⟩
    · rintro ⟨⟨z, hz, rfl⟩, hz0⟩
      exact ⟨z, ⟨hz, (hheight z).symm.trans hz0⟩, rfl⟩
  change ((Kshift.link 0).space ∩ {z | height z = 0}).ncard = 2 at hzeroCount
  rw [← hzeros, shift.injective.injOn.ncard_image] at hzeroCount
  obtain ⟨⟨u, hu, hupos⟩, v', hv', hvneg⟩ := hsigns
  obtain ⟨u', hu', rfl⟩ := hlink.subset hu
  obtain ⟨v'', hv'', rfl⟩ := hlink.subset hv'
  exact ⟨hzeroCount, ⟨u', hu', by
    calc
      0 < height (shift u') := hupos
      _ = (c u').2 := hheight u'⟩,
    v'', hv'', by
      calc
        (c v'').2 = height (shift v'') := (hheight v'').symm
        _ < 0 := hvneg⟩

end Geometry.OriginalPLTower
