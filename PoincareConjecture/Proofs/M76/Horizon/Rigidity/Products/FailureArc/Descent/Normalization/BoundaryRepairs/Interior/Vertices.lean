import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.Links
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.Parameter
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.PlanarParameterLink

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
theorem moved_positive_vertex_crossing
    (hW : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    (B : SimplicialComplex ℝ V3)
    (hfaces : B.faces = (fun face ↦ face.image (N.motion.map 1)) '' N.branchComplex.faces)
    (p : V3) (hpB : p ∈ B.vertices) (hpJ : p ∈ interior N.support.space)
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
  have hBimage : B = hHK.embeddedImage (N.motion.map 1).injective.injOn := by
    ext1
    exact hfaces.trans (hHK.embeddedImage_faces _).symm
  have hBvertices : B.vertices = N.motion.map 1 '' K.vertices := by
    rw [hBimage]
    exact hHK.embeddedImage_vertices _
  obtain ⟨v, hvK, rfl⟩ := hBvertices.subset hpB
  have hvJ : v ∈ interior N.support.space := by
    have hi := ((N.motion.map 1).image_interior N.support.space).trans (congrArg interior (N.motion.carrier 1))
    obtain ⟨x, hx, hxeq⟩ := hi.symm.subset hpJ
    exact (N.motion.map 1).injective hxeq ▸ hx
  have hvR : 0 < (N.coordinates v).1.1 := (N.height 1 v) ▸ hpR
  have hvzero : (N.coordinates v).2 = 0 := by
    have hs : ({v} : Finset V3) ∈ K.faces := hvK
    exact N.branch_zero_faces {v} hs (by simpa using hpzero) v (by simp)
  have hvspace : v ∈ K.space := K.vertices_subset_space hvK
  have hparamInt := N.positive_parameter_interior hvspace hvJ hvR
  obtain ⟨n, P, hPi, hP, hPs⟩ := exists_link_polygon_of_pair_parameter K hK
    N.parameter_affine (N.parameter_injective.mono N.branch_space.subset) hvK hparamInt
  obtain ⟨hzeros, hpos, hneg⟩ := N.positive_link_sections hAnn hW hvK hvJ hvR hvzero
  let A := N.endpoint_affine.embeddedImage (N.motion.map 1).injective.injOn
  have hA : A.faces.Finite := N.endpoint_affine.embeddedImage_finite
    (N.motion.map 1).injective.injOn N.ambient_finite
  have hAs : A.space = N.support.space := by
    rw [N.endpoint_affine.embeddedImage_space, N.subdivision.space_eq]
    exact N.motion.carrier 1
  have hBA : B ≤ A := by
    intro face hface
    obtain ⟨g, hg, rfl⟩ := hfaces.subset hface
    exact (N.endpoint_affine.embeddedImage_faces _).symm.subset
      ⟨g, N.branch_le hg, rfl⟩
  have hlink : (B.link (N.motion.map 1 v)).space = N.motion.map 1 '' (K.link v).space := by
    rw [hBimage]
    exact hHK.embeddedImage_link_space (N.motion.map 1).injective.injOn hvK
  exact exists_moved_zero_vertex_crossing K B A hK hA hBA (N.motion.map 1) hHK
    (N.motion.map 1).injective v hpB (hAs.symm ▸ hpJ) hlink N.coordinates hpzero P hP hPi hPs
    hzeros hpos hneg
    (fun x hx hn => N.signs x (N.branch_le hx) hn 1)
    O hO hpO

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
