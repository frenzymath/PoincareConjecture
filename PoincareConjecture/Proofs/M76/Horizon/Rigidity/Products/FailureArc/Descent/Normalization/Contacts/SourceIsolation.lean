import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Contacts.SourceIsolation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Contacts.FaceCharts

set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.SimplicialComplex

theorem exists_surface_projected_branch_face_neighborhood
    {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → X} (hji : IsEmbedding (fun x : K.space ↦ j x))
    {p : X → Y} (branch : OpenPartialHomeomorph X Y)
    (hbranch : (branch : X → Y) = p)
    {a : Finset V} (ha : a ∈ K.faces)
    (hmax : ∀ b ∈ K.faces, a ⊆ b → b = a)
    {v : V} (hv : v ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V)))
    (hvbranch : j v ∈ branch.source) :
    ∃ W : Set Y, IsOpen W ∧ p (j v) ∈ W ∧ W ⊆ branch.target ∧
      ∀ z ∈ W, ∀ q ∈ K.space, j q ∈ branch.source → p (j q) = z →
        q ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V)) := by
  exact K.exists_projected_branch_face_neighborhood hK hji branch hbranch ha hmax hv hvbranch

end Geometry.SimplicialComplex
