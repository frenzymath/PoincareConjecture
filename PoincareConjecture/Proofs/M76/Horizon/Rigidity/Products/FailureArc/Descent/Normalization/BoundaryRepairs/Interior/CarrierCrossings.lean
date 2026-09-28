import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.Vertices
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.Edges
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BoundaryContactFaces
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.LocalBranchCharts

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "P2" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ P2} {j : P2 → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}
  {a b : PLAnnularStrip.squareAnnulus 8 1} {W : Set s.Carrier} {ε : ℝ}
  (N : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
  (hAnn : D.K.space = PLAnnularStrip.squareAnnulus 8 1)

include hAnn

set_option maxHeartbeats 800000 in
theorem exists_positive_carrier_crossing
    (hW : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    (B : SimplicialComplex ℝ V3)
    (hfaces : B.faces = (fun face ↦ face.image (N.motion.map 1)) '' N.branchComplex.faces)
    (p : V3) (hpB : p ∈ B.space) (hpJ : p ∈ interior N.support.space)
    (hpR : 0 < (N.coordinates p).1.1) (hpzero : (N.coordinates p).2 = 0)
    (O : Set V3) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, (N.coordinates x).2 = 0 ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, x ∈ B.space ↔ (T x).2 = 0 := by
  classical
  let K := N.branchComplex
  have hK : K.faces.Finite := N.ambient_finite.subset N.branch_le
  have hHK : K.AffineOnFaces (N.motion.map 1) :=
    fun face hface => N.endpoint_affine face (N.branch_le hface)
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp N.coordinates.toContinuousLinearMap
  let region : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp N.coordinates.toContinuousLinearMap)
  let coord := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let param := coord ∘ N.parameter
  have hparam : K.AffineOnFaces param :=
    N.parameter_affine.postcomp coord.toContinuousLinearMap.toContinuousAffineMap
  have hparami : InjOn param K.space :=
    coord.injective.comp_injOn (N.parameter_injective.mono N.branch_space.subset)
  have hparamInt (x : V3) (hx : x ∈ K.space) (hxJ : x ∈ interior N.support.space)
      (hxR : 0 < region x) : param x ∈ interior (param '' K.space) := by
    have h := coord.toHomeomorph.image_interior (N.parameter '' K.space)
    change coord '' interior (N.parameter '' K.space) =
      interior (coord '' (N.parameter '' K.space)) at h
    have hm := mem_image_of_mem coord (N.positive_parameter_interior hx hxJ hxR)
    change coord (N.parameter x) ∈ coord '' interior (N.parameter '' K.space) at hm
    rw [h] at hm
    simpa only [param, image_image, Function.comp_def] using hm
  have happroach (x : V3) (hx : x ∈ K.space) (hxJ : x ∈ interior N.support.space)
      (hxR : 0 < region x) (hx0 : ell x = 0) :
      x ∈ closure (K.space ∩ {y | 0 < ell y}) :=
    (N.positive_signed_approach hAnn hW (N.branch_space.subset hx) hxJ hxR hx0).1
  have hcases := boundary_motion_interior_contact_cases N.support K B hK param
    hparam hparami ell region hparamInt N.motion hHK
    (N.height 1) N.branch_zero_faces hfaces happroach
    p hpB hpJ hpR hpzero
  rcases hcases with ⟨v, hvK, _hv0, rfl⟩ | ⟨edge, heK, he2, hezero, henew, hp⟩ | hfree
  · have hvB : N.motion.map 1 v ∈ B.vertices := by
      have hBi : B = hHK.embeddedImage (N.motion.map 1).injective.injOn := by
        ext1
        exact hfaces.trans (hHK.embeddedImage_faces _).symm
      rw [hBi, hHK.embeddedImage_vertices]
      exact mem_image_of_mem (N.motion.map 1) hvK
    exact N.moved_positive_vertex_crossing hAnn hW B hfaces
      (N.motion.map 1 v) hvB hpJ hpR hpzero O hO hpO
  · obtain ⟨T, hpT, hTs, hTzero, hTPL, hTK, hheight⟩ :=
      N.moved_positive_edge_crossing hAnn hW B hfaces
        edge heK he2 hezero henew p hp hpJ hpR O hO hpO
    obtain ⟨T', hT's, hT'zero, hT'PL, hT'height, hT'K⟩ :=
      exists_swapped_carrier_chart B.space (fun x => (N.coordinates x).2) T hTPL hTK hheight
    exact ⟨T', hT's.symm ▸ hpT, hT's.subset.trans hTs, hT'zero p hTzero,
      hT'PL, hT'height, hT'K⟩
  · obtain ⟨T, hpT, hTs, hTzero, hTPL, _hTinv, hTK, hheight⟩ := hfree O hO hpO
    obtain ⟨T', hT's, hT'zero, hT'PL, hT'height, hT'K⟩ :=
      exists_swapped_carrier_chart B.space ell T hTPL hTK (fun x hx => (hheight x hx).symm)
    exact ⟨T', hT's.symm ▸ hpT, hT's.subset.trans hTs, hT'zero p hTzero,
      hT'PL, hT'height, hT'K⟩

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
