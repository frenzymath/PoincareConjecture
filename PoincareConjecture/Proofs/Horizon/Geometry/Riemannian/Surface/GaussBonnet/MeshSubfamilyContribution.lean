import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilySeparation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.IndependentFans




set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem mesh_family_contribution_eq_two_subfamily_sums {I A B : Type*}
    [Fintype I] [Fintype A] [Fintype B]
    (g : RiemannianMetric 2 S) (M : I → TriangleMesh)
    (F : I → OpenPartialHomeomorph Plane S)
    (face : ((i : I) × (M i).Triangle) → SmoothFace S)
    (hsource : ∀ i, (M i).toPlaneComplex.support ⊆ (F i).source)
    (hcarrier : ∀ a, (face a).carrier =
      F a.1 '' convexHull ℝ (range (meshTriangleBasis (M a.1) a.2)))
    (hfront : ∀ a b, a ≠ b → (face a).carrier ∩ (face b).carrier ⊆ frontier (face a).carrier)
    (left : A → I) (right : B → I) (hl : Function.Injective left)
    (hr : Function.Injective right) (hne : ∀ a b, left a ≠ right b) {q : S}
    (hq : q ∈ interior ((⋃ a, F (left a) '' (M (left a)).toPlaneComplex.support) ∪
      ⋃ b, F (right b) '' (M (right b)).toPlaneComplex.support)) :
    (∑ i, meshVertexAngleContribution g (F i) (M i) q) =
      (∑ a, meshVertexAngleContribution g (F (left a)) (M (left a)) q) +
      ∑ b, meshVertexAngleContribution g (F (right b)) (M (right b)) q := by
  classical
  let ι : A ⊕ B → I := Sum.elim left right
  have hinj : Function.Injective ι := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (hl h)
      | inr b => exact False.elim (hne a b h)
    | inr a =>
      cases b with
      | inl b => exact False.elim (hne b a h.symm)
      | inr b => exact congrArg Sum.inr (hr h)
  have hint : q ∈ interior (⋃ s, F (ι s) '' (M (ι s)).toPlaneComplex.support) := by
    simpa only [iUnion_sum, ι, Sum.elim_inl, Sum.elim_inr] using hq
  have heq : (∑ s, meshVertexAngleContribution g (F (ι s)) (M (ι s)) q) =
      ∑ i, meshVertexAngleContribution g (F i) (M i) q := by
    apply Fintype.sum_of_injective ι hinj
    · intro i hi
      apply meshVertexAngleContribution_eq_zero_of_not_mem_support
      exact coordinate_mesh_family_not_mem_of_interior_subfamily M F face hsource hcarrier hfront
        ι i (fun s h => hi ⟨s, h.symm⟩) hint
    · intro s
      rfl
  rw [← heq, Fintype.sum_sum_type]
  rfl

end PoincareConjecture.Topology.Surface
