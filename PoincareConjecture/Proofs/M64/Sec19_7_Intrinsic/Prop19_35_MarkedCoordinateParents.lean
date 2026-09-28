import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandChainCompatibility
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Subdivision.Vertices

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

theorem m64Intrinsic_exists_marked_coordinate_parents
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j))
    (marks : Finset AnnulusCoordinates)
    (hmarks : (marks : Set AnnulusCoordinates) ⊆ ⋃ i, F i '' convexHull ℝ (range (b i))) :
    ∃ (m : ℕ) (G : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
      (d : Fin m → AffineBasis (Fin 3) ℝ Plane),
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (G p) (G p).source) ∧
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (G p).symm (G p).target) ∧
      (∀ p, convexHull ℝ (range (d p)) ⊆ (G p).source) ∧
      (∀ p q, p ≠ q → CoordinateTriangleBoundaryIntersection (G p) (G q) (d p) (d q)) ∧
      (⋃ p, G p '' convexHull ℝ (range (d p))) = ⋃ i, F i '' convexHull ℝ (range (b i)) ∧
      ∀ q ∈ marks, ∃ p k, G p (d p k) = q := by
  classical
  let M (i : I) := (TriangleMesh.single (b i) (b i).ind).refineAtVertices
    (marks.image (F i).symm)
  have hsupport (i : I) : (M i).toPlaneComplex.support = convexHull ℝ (range (b i)) := by
    rw [TriangleMesh.refineAtVertices_support, TriangleMesh.single_support]
  have hchild (i : I) (t : (M i).Triangle) :
      convexHull ℝ (range (meshTriangleBasis (M i) t)) ⊆ convexHull ℝ (range (b i)) := by
    rw [← hsupport i]
    exact meshTriangleBasis_subset_support (M i) t
  obtain ⟨hcompat, hcover⟩ := m64Intrinsic_coordinate_mesh_family_canonical
    F b hsource hparents M hsupport
  let Child := (i : I) × (M i).Triangle
  let _ := Fintype.ofFinite Child
  let index := Fintype.equivFin Child
  let G : Fin (Fintype.card Child) → OpenPartialHomeomorph Plane AnnulusCoordinates :=
    fun p => F (index.symm p).1
  let d : Fin (Fintype.card Child) → AffineBasis (Fin 3) ℝ Plane :=
    fun p => meshTriangleBasis (M (index.symm p).1) (index.symm p).2
  refine ⟨Fintype.card Child, G, d, fun p => hF _, fun p => hFi _,
    fun p => (hchild _ _).trans (hsource _), ?_, ?_, ?_⟩
  · intro p q hpq
    exact hcompat (index.symm p) (index.symm q) (fun h => hpq (index.symm.injective h))
  · rw [← hcover]
    ext q
    constructor
    · intro hq
      obtain ⟨p, hp⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨index.symm p, hp⟩
    · intro hq
      obtain ⟨p, hp⟩ := mem_iUnion.mp hq
      apply mem_iUnion.mpr
      refine ⟨index p, ?_⟩
      change q ∈ F (index.symm (index p)).1 ''
        convexHull ℝ (range (meshTriangleBasis (M (index.symm (index p)).1)
          (index.symm (index p)).2))
      rw [index.symm_apply_apply]
      exact hp
  · intro q hq
    obtain ⟨i, z, hz, hzq⟩ := mem_iUnion.mp (hmarks hq)
    have hinverse : (F i).symm q = z := by
      rw [← hzq]
      exact (F i).left_inv (hsource i hz)
    have hzmark : z ∈ marks.image (F i).symm :=
      Finset.mem_image.mpr ⟨q, hq, hinverse⟩
    have hzsupport : z ∈ (TriangleMesh.single (b i) (b i).ind).toPlaneComplex.support := by
      rw [TriangleMesh.single_support]
      exact hz
    obtain ⟨t, ht, v, hv, hpos⟩ :=
      (TriangleMesh.single (b i) (b i).ind).refineAtVertices_exists_incident_triangle
        (marks.image (F i).symm) hzmark hzsupport
    let triangle : (M i).Triangle := ⟨t, ht⟩
    have hvRange : v ∈ range ((M i).orderedVertex triangle) := by
      rw [(M i).range_orderedVertex]
      exact hv
    obtain ⟨k, hk⟩ := hvRange
    refine ⟨index ⟨i, triangle⟩, k, ?_⟩
    change F (index.symm (index ⟨i, triangle⟩)).1
      (meshTriangleBasis (M (index.symm (index ⟨i, triangle⟩)).1)
        (index.symm (index ⟨i, triangle⟩)).2 k) = q
    rw [index.symm_apply_apply]
    change F i ((M i).position ((M i).orderedVertex triangle k)) = q
    change (M i).position v = z at hpos
    rw [hk, hpos]
    exact hzq

end PoincareConjecture
