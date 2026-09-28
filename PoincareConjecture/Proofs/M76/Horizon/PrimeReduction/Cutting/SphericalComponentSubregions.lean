import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedComponentDomains
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereSubregionFinitePL

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

theorem PLDomain.component_frontier_of_connected_marks
    {X ι ν : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X}
    (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (S : ν → Set X) (hS : ∀ i, IsConnected (S i))
    (hfront : frontier Q = ⋃ i, S i) {x : X} (hx : x ∈ Q) :
    IsCompact (_root_.connectedComponentIn Q x) ∧
      PLDomain e (_root_.connectedComponentIn Q x) ∧
      IsConnected (_root_.connectedComponentIn Q x) ∧
      (∀ i, S i ⊆ _root_.connectedComponentIn Q x ∨
        Disjoint (S i) (_root_.connectedComponentIn Q x)) ∧
      frontier (_root_.connectedComponentIn Q x) =
        ⋃ i : {i : ν // S i ⊆ _root_.connectedComponentIn Q x}, S i := by
  classical
  obtain ⟨_, D, owner, hD, hdis, _, howner, haway, hactual⟩ :=
    exists_marked_pl_component_domains hQ hPL S hS
      (fun i => hfront.symm ▸ subset_iUnion S i)
  let c := ConnectedComponents.mk (⟨x, hx⟩ : Q)
  have hDc : D c = _root_.connectedComponentIn Q x := hactual ⟨x, hx⟩
  have hwhole (i : ν) : S i ⊆ D c ∨ Disjoint (S i) (D c) := by
    by_cases hi : owner i = c
    · exact Or.inl ((howner i c).mpr hi)
    · exact Or.inr (haway i c hi)
  have hboundary : frontier (D c) = ⋃ i : {i : ν // S i ⊆ D c}, S i := by
    rw [(hD c).2.2.2.2, hfront]
    apply Subset.antisymm
    · rintro y ⟨hyD, hyS⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hyS
      rcases hwhole i with hsub | hsep
      · exact mem_iUnion.mpr ⟨⟨i, hsub⟩, hi⟩
      · exact False.elim (disjoint_left.mp hsep hi hyD)
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact ⟨i.property hi, mem_iUnion.mpr ⟨i, hi⟩⟩
  rw [hDc] at hwhole hboundary
  exact ⟨hDc ▸ (hD c).1, hDc ▸ (hD c).2.1,
    hDc ▸ (hD c).2.2.1, hwhole, hboundary⟩

theorem PLDomain.component_frontier_of_spheres
    {X ι ν : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X}
    (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hfront : frontier Q = ⋃ i, S i) {x : X} (hx : x ∈ Q) :
    IsCompact (_root_.connectedComponentIn Q x) ∧
      PLDomain e (_root_.connectedComponentIn Q x) ∧
      IsConnected (_root_.connectedComponentIn Q x) ∧
      (∀ i, S i ⊆ _root_.connectedComponentIn Q x ∨
        Disjoint (S i) (_root_.connectedComponentIn Q x)) ∧
      frontier (_root_.connectedComponentIn Q x) =
        ⋃ i : {i : ν // S i ⊆ _root_.connectedComponentIn Q x}, S i := by
  apply hPL.component_frontier_of_connected_marks hQ S _ hfront hx
  intro i
  exact isConnected_iff_connectedSpace.mpr
    ((sS i).parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by simp) (0 : V3) zero_le_one)))

theorem PLDomain.exists_finitePL_punctured_component_model
    {X E ι κ ν : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite κ] [Finite ν]
    {e : ι → OpenPartialHomeomorph X V3} {R Q : Set X} {M : Set E}
    (hQ : IsCompact Q) (hPL : PLDomain e Q) (hQR : Q ⊆ R)
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ Sphere)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hAo : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A i \ r i)))
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (G : R ≃ₜ M) (hG : ∀ x : R, (G x : E) = f x)
    (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)) (hC : C.IsFinitePL)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r i)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Q = ⋃ i, S i) {x : X} (hx : x ∈ Q) :
    let D := _root_.connectedComponentIn Q x
    let J := {i : ν // S i ⊆ D}
    let T := fun i : J => (fun x : R => (C (G x) : V4)) ''
      ((Subtype.val : R → X) ⁻¹' S i)
    ∃ B : J → Set V4,
      (∀ i, IsFinitePLBallPair V3 (B i) (T i) ∧ B i ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B i \ T i))) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      ∃ (u : D ≃ₜ (f '' D)) (H : (f '' D) ≃ₜ (Sphere \ ⋃ i, B i \ T i : Set V4)),
        H.IsFinitePL ∧ (∀ x : D, (u x : E) = f x) ∧
        (∀ x : D, (H (u x) : V4) = C (G ⟨x, hQR
          (connectedComponentIn_subset Q _ x.property)⟩)) ∧
        (∀ (i : J) (x : D), (x : X) ∈ S i ↔ (H (u x) : V4) ∈ T i) ∧
        ∀ x : D, (x : X) ∈ frontier D ↔ (H (u x) : V4) ∈ ⋃ i, T i := by
  classical
  obtain ⟨_, hDPL, hDc, _, hDf⟩ := hPL.component_frontier_of_spheres hQ S sS hfront hx
  exact hDPL.exists_finitePL_punctured_subregion_model hDc
    ((connectedComponentIn_subset Q x).trans hQR)
    A r hA hAS hAdis hAo f hf G hG C hC hmark
    (fun i : {i : ν // S i ⊆ _root_.connectedComponentIn Q x} => S i)
    (fun i => sS i) (fun i j hij => hSdis (Subtype.val_injective.ne hij)) hDf

end PoincareConjecture.M76
