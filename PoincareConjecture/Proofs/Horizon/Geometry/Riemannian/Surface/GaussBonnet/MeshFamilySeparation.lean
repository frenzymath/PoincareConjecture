import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilyIncidence
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Interior








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


theorem coordinate_mesh_family_support_eq_iUnion {I : Type*}
    (M : I → TriangleMesh) (F : I → OpenPartialHomeomorph Plane S)
    (face : ((i : I) × (M i).Triangle) → SmoothFace S)
    (hcarrier : ∀ a, (face a).carrier =
      F a.1 '' convexHull ℝ (range (meshTriangleBasis (M a.1) a.2))) (i : I) :
    F i '' (M i).toPlaneComplex.support = ⋃ t : (M i).Triangle, (face ⟨i, t⟩).carrier := by
  simp only [hcarrier, ← image_iUnion, meshTriangleBasis_sources_cover]

variable [T2Space S]



theorem coordinate_mesh_family_not_mem_of_interior_subfamily {I J : Type*}
    (M : I → TriangleMesh) (F : I → OpenPartialHomeomorph Plane S)
    (face : ((i : I) × (M i).Triangle) → SmoothFace S)
    (hsource : ∀ i, (M i).toPlaneComplex.support ⊆ (F i).source)
    (hcarrier : ∀ a, (face a).carrier =
      F a.1 '' convexHull ℝ (range (meshTriangleBasis (M a.1) a.2)))
    (hfront : ∀ a b, a ≠ b → (face a).carrier ∩ (face b).carrier ⊆ frontier (face a).carrier)
    (ι : J → I) (i : I) (hi : ∀ j, i ≠ ι j) {q : S}
    (hq : q ∈ interior (⋃ j, F (ι j) '' (M (ι j)).toPlaneComplex.support)) :
    q ∉ F i '' (M i).toPlaneComplex.support := by
  rw [coordinate_mesh_family_support_eq_iUnion M F face hcarrier]
  intro hmem
  obtain ⟨t, ht⟩ := mem_iUnion.mp hmem
  have hregular : closure (interior (face ⟨i, t⟩).carrier) = (face ⟨i, t⟩).carrier := by
    rw [hcarrier]
    exact coordinate_triangle_closure_interior (F i) (meshTriangleBasis (M i) t)
      ((meshTriangleBasis_subset_support (M i) t).trans (hsource i))
  have hdisj : Disjoint (interior (⋃ j, F (ι j) '' (M (ι j)).toPlaneComplex.support))
      (interior (face ⟨i, t⟩).carrier) := by
    apply disjoint_left.mpr
    intro z hz hzt
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (interior_subset hz)
    rw [coordinate_mesh_family_support_eq_iUnion M F face hcarrier] at hzj
    obtain ⟨u, hzu⟩ := mem_iUnion.mp hzj
    have hne : (⟨i, t⟩ : (i : I) × (M i).Triangle) ≠ ⟨ι j, u⟩ :=
      fun h => hi j (congrArg Sigma.fst h)
    exact (hfront ⟨i, t⟩ ⟨ι j, u⟩ hne ⟨interior_subset hzt, hzu⟩).2 hzt
  have h := hdisj.closure_right isOpen_interior
  rw [hregular] at h
  exact disjoint_left.mp h hq ht

end PoincareConjecture.Topology.Surface
