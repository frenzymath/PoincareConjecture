import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskComponentProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalComponentSubregions

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

theorem exists_punctured_cap_component_models
    {X E ι κ ν : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite κ] [Finite ν]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X} {M : Set E}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier)
    (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ Sphere)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hAo : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A i \ r i)))
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (G : connectedComponentIn R (a false) ≃ₜ M)
    (hG : ∀ x : connectedComponentIn R (a false), (G x : E) = f x)
    (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)) (hC : C.IsFinitePL)
    (hmark : ∀ x : connectedComponentIn R (a false),
      (x : X) ∈ frontier (connectedComponentIn R (a false)) ↔
        (C (G x) : V4) ∈ ⋃ i, r i)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier P.cutCarrier = ⋃ i, S i) :
    let D := fun b => connectedComponentIn P.cutCarrier (a b)
    Disjoint (D false) (D true) ∧
      connectedComponentIn R (a false) = (D false ∪ D true) ∪ P.closedStrip ∧
      ∀ b : Bool,
        let J := {i : ν // S i ⊆ D b}
        let T := fun i : J => (fun x : connectedComponentIn R (a false) =>
          (C (G x) : V4)) '' ((Subtype.val : connectedComponentIn R (a false) → X) ⁻¹' S i)
        ∃ B : J → Set V4,
          (∀ i, IsFinitePLBallPair V3 (B i) (T i) ∧ B i ⊆ Sphere ∧
            IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B i \ T i))) ∧
          Pairwise (fun i j => Disjoint (B i) (B j)) ∧
          ∃ (u : D b ≃ₜ (f '' D b))
            (H : (f '' D b) ≃ₜ (Sphere \ ⋃ i, B i \ T i : Set V4)),
            H.IsFinitePL ∧ (∀ x : D b, (u x : E) = f x) ∧
            (∀ (i : J) (x : D b), (x : X) ∈ S i ↔ (H (u x) : V4) ∈ T i) ∧
            ∀ x : D b, (x : X) ∈ frontier (D b) ↔ (H (u x) : V4) ∈ ⋃ i, T i := by
  classical
  let D := fun b => connectedComponentIn P.cutCarrier (a b)
  obtain ⟨hQ, _, _, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hacut (b : Bool) : a b ∈ P.cutCarrier := by
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl (ha false)
    · exact Or.inr (ha true)
  have hneq : D false ≠ D true := by
    intro heq
    have hsame : a true ∈ connectedComponentIn P.cutCarrier (a false) := by
      change a true ∈ D false
      rw [heq]
      exact mem_connectedComponentIn (hacut true)
    exact P.not_homeomorph_punctured_sphere_of_cap_component_self_attachment
      hR hopen hPL (ha false) (ha true) hsame A r hA hAS hAdis hAo ⟨G.trans C⟩
  have hdis : Disjoint (D false) (D true) := by
    apply disjoint_left.mpr
    intro x hxf hxt
    exact hneq ((connectedComponentIn_eq hxf).trans (connectedComponentIn_eq hxt).symm)
  have hrec := (P.component_reconstruction hR hopen hPL (ha false) (ha true)).1
  refine ⟨hdis, hrec, ?_⟩
  intro b
  obtain ⟨_, hDPL, hDc, _, hDf⟩ :=
    hPL.component_frontier_of_spheres hQ S sS hfront (hacut b)
  have hDR : D b ⊆ connectedComponentIn R (a false) := by
    rw [hrec]
    cases b
    · exact subset_union_of_subset_left subset_union_left _
    · exact subset_union_of_subset_left subset_union_right _
  obtain ⟨B, hB, hBdis, u, H, hH, hu, _, hrim, hboundary⟩ :=
    hDPL.exists_finitePL_punctured_subregion_model hDc hDR
      A r hA hAS hAdis hAo f hf G hG C hC hmark
      (fun i : {i : ν // S i ⊆ D b} => S i) (fun i => sS i)
      (fun i j hij => hSdis (Subtype.val_injective.ne hij)) hDf
  exact ⟨B, hB, hBdis, u, H, hH, hu, hrim, hboundary⟩

end PoincareConjecture.M76.OriginalDiskProduct
