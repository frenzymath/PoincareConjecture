import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.ProtectedLinks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.MovedEdgeCrossing
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.InteriorContactFaces
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.LocalBranchCharts

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.PlanarSurfaceBranchMotion

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ A} {j : A → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}
  {a b : D.K.space} {W : Set s.Carrier} {ε : ℝ}
  (N : PlanarSurfaceBranchMotion step D.K D.endpoint R a b W ε)

theorem exists_carrier_crossing
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    {z : V3} (hz : z ∈ N.movedBranch.space)
    (hzJ : z ∈ interior N.support.space) (hz0 : (N.coordinates z).2 = 0)
    (O : Set V3) (hO : IsOpen O) (hzO : z ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      z ∈ T.source ∧ T.source ⊆ O ∧ T z = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, (N.coordinates x).2 = 0 ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, x ∈ N.movedBranch.space ↔ (T x).2 = 0 := by
  classical
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp N.coordinates.toContinuousLinearMap
  have hK : N.branchComplex.faces.Finite := N.ambient_finite.subset N.branch_le
  have hH : N.branchComplex.AffineOnFaces (N.motion.map 1) :=
    fun face hf ↦ N.endpoint_affine face (N.branch_le hf)
  have hi : InjOn N.parameter N.branchComplex.space :=
    N.parameter_injective.mono N.branch_space.subset
  have hint (x : V3) (hx : x ∈ N.branchComplex.space)
      (hxJ : x ∈ interior N.support.space) :
      N.parameter x ∈ interior (N.parameter '' N.branchComplex.space) := by
    rw [N.branch_space]
    exact N.parameter_interior x (N.branch_space.subset hx) hxJ
  obtain ⟨B, _hB, hBs, hcases⟩ := exists_protected_motion_interior_contact_cases
    N.support N.branchComplex N.fixedComplex hK N.fixed_carrier
    N.parameter N.parameter_affine hi hint ell N.motion hH
    (fun face hf hzero ↦ (N.zero_faces face hf).mp hzero)
    (fun p hp hpJ hp0 ↦ (N.protected_signed_approach hW hp hpJ hp0).1)
  have hBmoved : B.space = N.movedBranch.space := by
    rw [hBs, N.moved_space, N.branch_space]
  have hsigns (v : V3) (hv : v ∈ N.branchComplex.vertices)
      (hv0 : (N.coordinates v).2 ≠ 0) := N.signs v (N.branch_le hv) hv0 (1 : I)
  rcases hcases z (hBmoved.symm.subset hz) hzJ hz0 with hv | he | hfree
  · have hzfixed : z ∈ N.fixed.space :=
      N.fixed_carrier.subset (N.fixedComplex.vertices_subset_space hv)
    have hfix : N.motion.map 1 z = z := N.motion.fixed_protected 1 z hzfixed
    have hzK : z ∈ N.branchComplex.vertices := N.fixed_le hv
    obtain ⟨n, P, hPi, hP, hPs⟩ := N.old_links z hzK hzJ
    obtain ⟨hcount, hpos, hneg⟩ := N.protected_link_sections hW hv hzJ hz0
    have hnewv : N.motion.map 1 z ∈ N.movedBranch.vertices :=
      hfix.symm ▸ N.fixed_moved hv
    have hnewint : N.motion.map 1 z ∈ interior N.movedAmbient.space := by
      rw [N.moved_ambient_space, hfix]
      exact hzJ
    have hnewzero : (N.coordinates (N.motion.map 1 z)).2 = 0 := hfix.symm ▸ hz0
    obtain ⟨T, hzT, hTs, hTz, hTPL, hflat, hbranch⟩ :=
      exists_moved_zero_vertex_crossing N.branchComplex N.movedBranch N.movedAmbient
        hK N.moved_finite N.moved_le (N.motion.map 1) hH (N.motion.map 1).injective
        z hnewv hnewint (N.moved_stars z hzK).1 N.coordinates hnewzero
        P hP hPi hPs hcount hpos hneg hsigns O hO (hfix.symm ▸ hzO)
    exact ⟨T, hfix ▸ hzT, hTs, hfix ▸ hTz, hTPL, hflat, hbranch⟩
  · obtain ⟨edge, he, he2, hezero, hze⟩ := he
    have heK : edge ∈ N.branchComplex.faces := N.fixed_le he
    have hzfixed : z ∈ N.fixed.space := N.fixed_carrier.subset
      (N.fixedComplex.convexHull_subset_space he (intrinsicInterior_subset hze))
    obtain ⟨hpos, hneg⟩ := N.protected_signed_approach hW hzfixed hzJ hz0
    have hefix (x : V3) (hx : x ∈ edge) : N.motion.map 1 x = x :=
      N.motion.fixed_protected 1 x (N.fixed_carrier.subset
        (N.fixedComplex.subset_space he hx))
    have himage : edge.image (N.motion.map 1) = edge := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        rw [hefix y hy]
        exact hy
      · intro hx
        exact Finset.mem_image.mpr ⟨x, hx, hefix x hx⟩
    let B' := hH.embeddedImage (N.motion.map 1).injective.injOn
    have hB's : B'.space = N.movedBranch.space := by
      rw [hH.embeddedImage_space, N.moved_space, N.branch_space]
    obtain ⟨T, hzT, hTs, hTz, hTPL, hbranch, hheight⟩ :=
      exists_moved_zero_edge_crossing N.branchComplex B' hK
        (N.motion.map 1) hH (N.motion.map 1).injective rfl
        N.parameter N.parameter_affine hi edge heK he2 ell hezero
        (fun x hx ↦ by rw [hefix x hx]; exact hezero x hx) z hze
        (hint z (N.branchComplex.convexHull_subset_space heK
          (intrinsicInterior_subset hze)) hzJ) hpos hneg hsigns z
        (by rw [himage]; exact hze) O hO hzO
    obtain ⟨T', hsource, hcenter, hPL, hflat, hcarrier⟩ := exists_swapped_carrier_chart
      B'.space ell T hTPL hbranch hheight
    refine ⟨T', hsource.symm ▸ hzT, hsource.subset.trans hTs, hcenter z hTz,
      hPL, hflat, ?_⟩
    intro x hx
    rw [← hB's]
    exact hcarrier x hx
  · obtain ⟨T, hzT, hTs, hTz, hTPL, _, hbranch, hheight⟩ := hfree O hO hzO
    obtain ⟨T', hsource, hcenter, hPL, hflat, hcarrier⟩ := exists_swapped_carrier_chart
      B.space ell T hTPL hbranch (fun x hx ↦ (hheight x hx).symm)
    refine ⟨T', hsource.symm ▸ hzT, hsource.subset.trans hTs, hcenter z hTz,
      hPL, hflat, ?_⟩
    intro x hx
    rw [← hBmoved]
    exact hcarrier x hx

end Geometry.OriginalPLTower.PlanarSurfaceBranchMotion
