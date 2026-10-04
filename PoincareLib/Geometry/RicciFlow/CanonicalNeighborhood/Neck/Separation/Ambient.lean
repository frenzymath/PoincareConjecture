import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import PoincareLib.Topology.Manifold.Separation.Components
import PoincareLib.Topology.Manifold.Separation.Bounded
import Mathlib.Analysis.Convex.Contractible

/-!
# Ambient separation by an actual neck

An actual epsilon-neck in a manifold homeomorphic to Euclidean three-space has
two ambient complementary components on opposite sides of its central sphere.
Exactly one component has bounded image under the Euclidean homeomorphism.

Reference: Morgan--Tian, Lemma 2.20, pp. 31--32, and Lemmas A.9--A.10,
pp. 501--502; see `references/topology/hatcher/neck-ambient-separation.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.EpsilonNeck

section CoordinateIdentities

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- The central slice of the neck homeomorphism is its specified central sphere. -/
theorem coordinate_central_range :
    range (fun y : UnitTwoSphere => (N.coordinate
      (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩) : M)) = N.central_sphere := by
  rw [N.central_sphere_eq]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y, 0), ⟨mem_univ _, rfl⟩,
      (N.coordinate_map_eq (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩)).symm⟩
  · rintro ⟨⟨y, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨y, N.coordinate_map_eq _⟩

private theorem mem_coordinate_image_iff (P : ℝ → Prop) (x : M) :
    x ∈ (fun z : NeckDomain N.epsilon => (N.coordinate z : M)) ''
      {z | P (z.2 : ℝ)} ↔ x ∈ N.carrier ∧ P (N.coordinate_inverse x).2 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(N.coordinate z).property, ?_⟩
    simpa only [N.coordinate_inverse_left, mem_ofPred_eq] using hz
  · rintro ⟨hx, hP⟩
    refine ⟨((N.coordinate_inverse x).1,
      ⟨(N.coordinate_inverse x).2, (N.coordinate_inverse_mem x hx).2⟩), hP, ?_⟩
    exact congrArg Subtype.val (N.coordinate_inverse_right x hx)

/-- The negative half of the collar is the actual negative coordinate region. -/
theorem coordinate_negative_image :
    (fun z : NeckDomain N.epsilon => (N.coordinate z : M)) ''
      {z | (z.2 : ℝ) < 0} = N.region (-N.epsilon⁻¹) 0 := by
  ext x
  rw [mem_coordinate_image_iff N (fun t => t < 0) x]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨hx, (N.coordinate_inverse_mem x hx).2.1, hn⟩
  · intro hx
    exact ⟨hx.1, hx.2.2⟩

/-- The positive half of the collar is the actual positive coordinate region. -/
theorem coordinate_positive_image :
    (fun z : NeckDomain N.epsilon => (N.coordinate z : M)) ''
      {z | 0 < (z.2 : ℝ)} = N.region 0 N.epsilon⁻¹ := by
  ext x
  rw [mem_coordinate_image_iff N (fun t => 0 < t) x]
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨hx, hp, (N.coordinate_inverse_mem x hx).2.2⟩
  · intro hx
    exact ⟨hx.1, hx.2.1⟩

end CoordinateIdentities

/-- An actual neck in a manifold homeomorphic to Euclidean three-space has two
ambient complementary sides, with exactly one bounded Euclidean image. -/
theorem exists_ambient_complementary_regions
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (h : M ≃ₜ EuclideanSpace ℝ (Fin 3)) :
    ∃ A B : Set M,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = N.central_sphereᶜ ∧
      frontier A = N.central_sphere ∧ frontier B = N.central_sphere ∧
      N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B ∧
      ((Bornology.IsBounded (h '' A) ∧ ¬Bornology.IsBounded (h '' B)) ∨
        (Bornology.IsBounded (h '' B) ∧ ¬Bornology.IsBounded (h '' A))) := by
  let : SimplyConnectedSpace M := h.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have hsep := Poincare.Topology.exists_collar_complementary_regions
    (inv_pos.mpr N.epsilon_pos) N.carrier_open N.coordinate
  dsimp only at hsep
  rw [N.coordinate_central_range, N.coordinate_negative_image,
    N.coordinate_positive_image] at hsep
  obtain ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hneg, hpos⟩ := hsep
  refine ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hneg, hpos, ?_⟩
  apply Poincare.Topology.bounded_side_of_compact_complement_partition_euclidean_three
    (N.isCompact_central_sphere.image h.continuous) (h.isOpenMap _ hA) (h.isOpenMap _ hB)
    (Set.disjoint_image_of_injective h.injective hdisj)
  rw [← image_union, hcover, h.image_compl]

/-- A side with bounded Euclidean image has compact closure in the manifold. -/
theorem compact_closure_of_bounded_image
    {M : Type*} [TopologicalSpace M] (h : M ≃ₜ EuclideanSpace ℝ (Fin 3))
    {A : Set M} (hA : Bornology.IsBounded (h '' A)) : IsCompact (closure A) := by
  have hc := hA.isCompact_closure.image h.symm.continuous
  rwa [← h.image_closure, h.image_symm, h.preimage_image] at hc

end PoincareMT.EpsilonNeck
