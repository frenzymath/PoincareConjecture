import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.RegionMapExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.EmbeddedMapTransport

set_option autoImplicit false
open Set Geometry Metric Topology

namespace PoincareConjecture.M76

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

open Dehn.ProtectedAnnulus

theorem exists_original_moved_annulus_pair
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S₀ : Set X}
    (M : R ≃ₜ R) (hM : ChartwisePLMap e e (⟨M, M.continuous⟩ : C(R, R)))
    (hfront : ∀ x : R, (M x : X) ∈ frontier R ↔ (x : X) ∈ frontier R)
    (hfix : ∀ x : R, (x : X) ∈ S₀ → M x = x)
    (f : Bool → V1 × V2 → X)
    (hf : ∀ b, PolyhedralPLInCharts e (f b) source)
    (hi : ∀ b, InjOn (f b) source)
    (hR : ∀ b, MapsTo (f b) source R)
    (hproper : ∀ b x, x ∈ source →
      (f b x ∈ frontier R ↔ x.1 ∈ sphere (0 : V1) 1))
    (hlower : ∀ b (u : Q2), f b (endpoint false, u) ∈ S₀) :
    ∃ j : Bool → V1 × V2 → X,
      j false = f false ∧
      j true = extendRegionMap M ∘ f true ∧
      (∀ b, PolyhedralPLInCharts e (j b) source) ∧
      (∀ b, InjOn (j b) source) ∧
      (∀ b, MapsTo (j b) source R) ∧
      (∀ b x, x ∈ source →
        (j b x ∈ frontier R ↔ x.1 ∈ sphere (0 : V1) 1)) ∧
      (∀ b (u : Q2), j b (endpoint false, u) = f b (endpoint false, u)) ∧
      (∀ u : Q2, j false (endpoint true, u) = f false (endpoint true, u)) ∧
      (∀ u : Q2, j true (endpoint true, u) =
        (M ⟨f true (endpoint true, u), hR true
          ⟨sphere_subset_closedBall (endpoint_mem_sphere true), u.property⟩⟩ : X)) := by
  classical
  let j : Bool → V1 × V2 → X := fun b =>
    if b then extendRegionMap M ∘ f true else f false
  have hval (x : V1 × V2) (hx : x ∈ source) :
      j true x = (M ⟨f true x, hR true hx⟩ : X) := by
    exact extendRegionMap_apply M ⟨f true x, hR true hx⟩
  have hjPL : PolyhedralPLInCharts e (j true) source := by
    obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
    let u : Q2 := ⟨fun _ => 1, by simp⟩
    let x₀ : R := ⟨f true (endpoint false, u), hR true
      ⟨sphere_subset_closedBall (endpoint_mem_sphere false), u.property⟩⟩
    have hh := hM.polyhedralPLInCharts_extendRegionMap K hK x₀ (f true)
      (hKs.symm ▸ hf true) (hKs.symm ▸ hR true)
    exact hKs ▸ hh
  refine ⟨j, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    cases b
    · exact hf false
    · exact hjPL
  · intro b
    cases b
    · exact hi false
    · exact (extendRegionMap_injective M.injective).injOn.comp (hi true)
        (mapsTo_univ _ _)
  · intro b x hx
    cases b
    · exact hR false hx
    · rw [hval x hx]
      exact (M ⟨f true x, hR true hx⟩).property
  · intro b x hx
    cases b
    · exact hproper false x hx
    · rw [hval x hx, hfront]
      exact hproper true x hx
  · intro b u
    cases b
    · rfl
    · rw [hval _ ⟨sphere_subset_closedBall (endpoint_mem_sphere false), u.property⟩,
        hfix _ (hlower true u)]
  · intro u
    rfl
  · intro u
    exact hval _ ⟨sphere_subset_closedBall (endpoint_mem_sphere true), u.property⟩

end PoincareConjecture.M76
