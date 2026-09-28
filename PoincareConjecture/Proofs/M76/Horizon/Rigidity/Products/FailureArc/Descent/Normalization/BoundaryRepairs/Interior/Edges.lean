import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.Links
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.Parameter
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.MovedEdgeCrossing

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
theorem moved_positive_edge_crossing
    (hW : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    (B : SimplicialComplex ℝ V3)
    (hfaces : B.faces = (fun face ↦ face.image (N.motion.map 1)) '' N.branchComplex.faces)
    (edge : Finset V3) (heK : edge ∈ N.branchComplex.faces) (he2 : edge.card = 2)
    (hezero : ∀ x ∈ edge, (N.coordinates x).2 = 0)
    (henew : ∀ x ∈ edge, (N.coordinates (N.motion.map 1 x)).2 = 0)
    (p : V3)
    (hp : p ∈ N.motion.map 1 '' intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)))
    (hpJ : p ∈ interior N.support.space) (hpR : 0 < (N.coordinates p).1.1)
    (O : Set V3) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, x ∈ B.space ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, (T x).2 = (N.coordinates x).2 := by
  classical
  let K := N.branchComplex
  have hK : K.faces.Finite := N.ambient_finite.subset N.branch_le
  have hHK : K.AffineOnFaces (N.motion.map 1) :=
    fun face hface ↦ N.endpoint_affine face (N.branch_le hface)
  have hBimage : B = hHK.embeddedImage (N.motion.map 1).injective.injOn := by
    ext1
    exact hfaces.trans (hHK.embeddedImage_faces _).symm
  have hB : B.faces.Finite := by
    rw [hBimage]
    exact hHK.embeddedImage_finite (N.motion.map 1).injective.injOn hK
  obtain ⟨z, hzedge, rfl⟩ := hp
  have hzJ : z ∈ interior N.support.space := by
    have hi := ((N.motion.map 1).image_interior N.support.space).trans (congrArg interior (N.motion.carrier 1))
    obtain ⟨x, hx, hxeq⟩ := hi.symm.subset hpJ
    exact (N.motion.map 1).injective hxeq ▸ hx
  have hzR : 0 < (N.coordinates z).1.1 := (N.height 1 z) ▸ hpR
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp N.coordinates.toContinuousLinearMap
  have hzeroHull : convexHull ℝ (edge : Set V3) ⊆ {x | ell x = 0} :=
    convexHull_min hezero ((convex_singleton (0 : ℝ)).linear_preimage ell.toLinearMap)
  have hzzero : (N.coordinates z).2 = 0 := hzeroHull (intrinsicInterior_subset hzedge)
  have hzspace : z ∈ K.space := K.convexHull_subset_space heK (intrinsicInterior_subset hzedge)
  have hparamInterior := N.positive_parameter_interior hzspace hzJ hzR
  obtain ⟨hpositive, hnegative⟩ :=
    N.positive_signed_approach hAnn hW (N.branch_space.subset hzspace) hzJ hzR hzzero
  have heB : edge.image (N.motion.map 1) ∈ B.faces := by
    rw [hBimage]
    exact (hHK.image_mem_embeddedImage_iff (N.motion.map 1).injective.injOn
      (K.subset_space heK)).mpr heK
  have hpHull : N.motion.map 1 z ∈ convexHull ℝ (edge.image (N.motion.map 1) : Set V3) := by
    rw [Finset.coe_image, ← hHK.image_convexHull heK]
    exact mem_image_of_mem (N.motion.map 1) (intrinsicInterior_subset hzedge)
  have hpInterior : N.motion.map 1 z ∈
      intrinsicInterior ℝ (convexHull ℝ (edge.image (N.motion.map 1) : Set V3)) := by
    obtain ⟨face, hface, hpface⟩ := B.exists_face_intrinsicInterior_of_finite hB
      (B.convexHull_subset_space heB hpHull)
    have hsub := B.subset_of_mem_intrinsicInterior_face hface heB hpface hpHull
    obtain ⟨oldFace, holdFace, rfl⟩ := hfaces.subset hface
    have hzold : z ∈ convexHull ℝ (oldFace : Set V3) := by
      have hm := intrinsicInterior_subset hpface
      rw [Finset.coe_image, ← hHK.image_convexHull holdFace] at hm
      exact (N.motion.map 1).injective.mem_set_image.mp hm
    have holdsub := K.subset_of_mem_intrinsicInterior_face heK holdFace hzedge hzold
    have heq := Finset.Subset.antisymm hsub (Finset.image_subset_image holdsub)
    exact heq ▸ hpface
  exact exists_moved_zero_edge_crossing K B hK (N.motion.map 1) hHK (N.motion.map 1).injective
    hBimage N.parameter N.parameter_affine
    (N.parameter_injective.mono N.branch_space.subset) edge heK he2 ell hezero henew z hzedge hparamInterior
    hpositive hnegative
    (fun x hx hn ↦ N.signs x (N.branch_le hx) hn 1)
    (N.motion.map 1 z) hpInterior O hO hpO

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
