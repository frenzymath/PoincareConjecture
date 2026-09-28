import PoincareConjecture.Proofs.M76.Mathlib.FullEuclideanGrid
import PoincareConjecture.Proofs.M76.Mathlib.HullImageLocalFiniteness
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.OpenPartialHomeomorph.Basic










set_option autoImplicit false

open Set Topology

namespace Geometry.SimplicialComplex

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_full_locallyFinite_complex :
    ∃ K : SimplicialComplex ℝ E, K.space = univ ∧
      LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E)) := by
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨J, _, hJspace, hJ⟩ :=
    exists_fullEuclideanGrid (N := Module.finrank ℝ E) 1 (by norm_num)
  have hf : J.AffineOnFaces e :=
    J.affineOnFaces_affine e.toContinuousLinearMap.toContinuousAffineMap
  let p := e.toHomeomorph.toOpenPartialHomeomorph
  have hsource : J.space ⊆ p.source := subset_univ _
  have hind (s : Finset (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (hs : s ∈ J.faces) : AffineIndependent ℝ ((↑) : ↥(p '' (s : Set _)) → E) :=
    hf.affineIndependent_image_face e.injective.injOn hs
  have hhull (s : Finset (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (hs : s ∈ J.faces) :
      p '' convexHull ℝ (s : Set _) = convexHull ℝ (p '' (s : Set _)) := hf.image_convexHull hs
  let D := J.hullImage p (p.injOn.mono hsource) hind hhull
  have hDspace : D.space = univ := by
    change (J.hullImage p (p.injOn.mono hsource) hind hhull).space = univ
    rw [hullImage_space, hJspace]
    rw [image_univ]
    exact e.surjective.range_eq
  refine ⟨D, hDspace, fun y => ?_⟩
  exact J.local_faces_hullImage p hsource hind hhull (fun x _ => hJ x)
    y (hDspace.symm ▸ mem_univ y)

end Geometry.SimplicialComplex
