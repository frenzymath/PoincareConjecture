import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.ProtectedCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.LocalCrossingLink
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.MovedVertexCrossing










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.PlanarSurfaceBranchMotion

local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ A} {j : A → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}
  {a b : D.K.space} {W : Set s.Carrier} {ε : ℝ}
  (N : PlanarSurfaceBranchMotion step D.K D.endpoint R a b W ε)

theorem protected_signed_approach
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    {v : V3} (hv : v ∈ N.fixed.space) (hvJ : v ∈ interior N.support.space)
    (hvzero : (N.coordinates v).2 = 0) :
    v ∈ closure (N.branchComplex.space ∩ {z | 0 < (N.coordinates z).2}) ∧
      v ∈ closure (N.branchComplex.space ∩ {z | (N.coordinates z).2 < 0}) := by
  obtain ⟨H, hzeroH, hHcenter, _, hsheet, hflat⟩ :=
    N.exists_protected_carrier_chart hW hv hvJ hvzero
  let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
  have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
  have hshiftK := N.branchComplex.affineOnFaces_affine shift.toContinuousAffineMap
  let Kshift := hshiftK.embeddedImage shift.injective.injOn
  have hKshifts : Kshift.space = shift '' N.branchComplex.space :=
    hshiftK.embeddedImage_space shift.injective.injOn
  let height : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp N.coordinates.toContinuousLinearMap
  have hheight (z : V3) : height (shift z) = (N.coordinates z).2 := by
    change (N.coordinates (-v + z)).2 = (N.coordinates z).2
    rw [map_add, map_neg]
    change -(N.coordinates v).2 + (N.coordinates z).2 = (N.coordinates z).2
    rw [hvzero, neg_zero, zero_add]
  have hsigns := signed_approach_of_crossing_chart Kshift height
    (N.coordinates.symm ((0, 0), 1))
    (by change (N.coordinates (N.coordinates.symm ((0, 0), 1))).2 = 1
        rw [N.coordinates.apply_symm_apply])
    H hzeroH hHcenter hflat (fun z hz ↦ by rw [hKshifts]; exact hsheet z hz)
  have pull (test : ℝ → Prop)
      (hcl : (0 : V3) ∈ closure (Kshift.space ∩ {x | test (height x)})) :
      v ∈ closure (N.branchComplex.space ∩ {x | test ((N.coordinates x).2)}) := by
    apply _root_.mem_closure_iff.mpr
    intro O hO hvO
    obtain ⟨z, hzO, hzK, hzt⟩ := _root_.mem_closure_iff.mp hcl (shift '' O)
      (shift.toHomeomorph.isOpenMap _ hO) ⟨v, hvO, hshift⟩
    obtain ⟨x, hxO, rfl⟩ := hzO
    have hxK : x ∈ N.branchComplex.space :=
      shift.injective.mem_set_image.mp (hKshifts.subset hzK)
    have hxTest : test ((N.coordinates x).2) := by
      rw [← hheight x]
      exact hzt
    exact ⟨x, hxO, hxK, hxTest⟩
  exact ⟨pull (fun x ↦ 0 < x) hsigns.1, pull (fun x ↦ x < 0) hsigns.2⟩

theorem protected_link_sections
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    {v : V3} (hv : v ∈ N.fixedComplex.vertices)
    (hvJ : v ∈ interior N.support.space) (hvzero : (N.coordinates v).2 = 0) :
    ((N.branchComplex.link v).space ∩ {z | (N.coordinates z).2 = 0}).ncard = 2 ∧
      (∃ z ∈ (N.branchComplex.link v).space, 0 < (N.coordinates z).2) ∧
      ∃ z ∈ (N.branchComplex.link v).space, (N.coordinates z).2 < 0 := by
  have hvK : v ∈ N.branchComplex.vertices := N.fixed_le hv
  have hvP : v ∈ N.fixed.space :=
    N.fixed_carrier.subset (N.fixedComplex.vertices_subset_space hv)
  obtain ⟨H, hzeroH, hHcenter, hHinv, hsheet, hflat⟩ :=
    N.exists_protected_carrier_chart hW hvP hvJ hvzero
  let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
  have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
  have hshiftK := N.branchComplex.affineOnFaces_affine shift.toContinuousAffineMap
  let Kshift := hshiftK.embeddedImage shift.injective.injOn
  have hKshift : Kshift.faces.Finite := hshiftK.embeddedImage_finite shift.injective.injOn
    (N.ambient_finite.subset N.branch_le)
  have hKshifts : Kshift.space = shift '' N.branchComplex.space :=
    hshiftK.embeddedImage_space shift.injective.injOn
  have hzeroKshift : (0 : V3) ∈ Kshift.vertices := by
    rw [hshiftK.embeddedImage_vertices shift.injective.injOn]
    exact ⟨v, hvK, hshift⟩
  let height : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp N.coordinates.toContinuousLinearMap
  have hheight (z : V3) : height (shift z) = (N.coordinates z).2 := by
    change (N.coordinates (-v + z)).2 = (N.coordinates z).2
    rw [map_add, map_neg]
    change -(N.coordinates v).2 + (N.coordinates z).2 = (N.coordinates z).2
    rw [hvzero, neg_zero, zero_add]
  have hparts (z : V3) (hz : z ∈ H.source) :
      (z ∈ Kshift.space ↔ (H z).1.1 = 0) ∧ (height z = 0 ↔ (H z).2 = 0) := by
    refine ⟨?_, hflat z hz⟩
    rw [hKshifts]
    exact hsheet z hz
  have hzeroCount := link_zero_ncard_of_crossing_chart Kshift hKshift hzeroKshift
    height.toLinearMap H hzeroH hHcenter hHinv
      (fun z hz ↦ and_congr (hparts z hz).1 (hparts z hz).2)
  have hsurface := signed_approach_of_crossing_chart Kshift height
    (N.coordinates.symm ((0, 0), 1))
    (by change (N.coordinates (N.coordinates.symm ((0, 0), 1))).2 = 1
        rw [N.coordinates.apply_symm_apply])
    H hzeroH hHcenter (fun z hz ↦ (hparts z hz).2) (fun z hz ↦ (hparts z hz).1)
  have hsigns := Kshift.exists_both_link_signs_of_surface_accumulation
    hKshift hzeroKshift height.toLinearMap hsurface.1 hsurface.2
  have hlink : (Kshift.link 0).space = shift '' (N.branchComplex.link v).space := by
    have h := hshiftK.embeddedImage_link_space shift.injective.injOn hvK
    change (Kshift.link (shift v)).space = shift '' (N.branchComplex.link v).space at h
    simpa only [hshift] using h
  have hzeros : shift '' ((N.branchComplex.link v).space ∩
      {z | (N.coordinates z).2 = 0}) =
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
      _ = (N.coordinates u').2 := hheight u'⟩,
    v'', hv'', by
      calc
        (N.coordinates v'').2 = height (shift v'') := (hheight v'').symm
        _ < 0 := hvneg⟩

end Geometry.OriginalPLTower.PlanarSurfaceBranchMotion

