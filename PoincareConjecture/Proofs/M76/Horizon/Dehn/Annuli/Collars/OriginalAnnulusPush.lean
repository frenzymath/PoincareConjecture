import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Collars.SourceComplex
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Collars.FiniteBoundaryPush









set_option autoImplicit false
open Set Geometry Metric Topology

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1



theorem exists_original_annulus_push
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : (V1 × V2) → X}
    (hN : IsCompact N) (he : PLDomain e N)
    (hj : PolyhedralPLInCharts e j source)
    (hjemb : Topology.IsEmbedding (fun x : source ↦ j x))
    (hjB : MapsTo j source (frontier N)) :
    ∃ k : (V1 × V2) → X, PolyhedralPLInCharts e k source ∧
      Topology.IsEmbedding (fun x : source ↦ k x) ∧ MapsTo k source N ∧
      EqOn k j (sphere (0 : V1) 1 ×ˢ Q2) ∧
      (∀ x : source, k x ∈ frontier N ↔ (x : V1 × V2) ∈ sphere (0 : V1) 1 ×ˢ Q2) ∧
      ∀ (b : Bool) (u : Q2), k (endpoint b, u) = j (endpoint b, u) := by
  obtain ⟨K, A, hK, hA, hKs, hAs, hAK, hne⟩ := exists_source_rim_complexes
  obtain ⟨k, hkPL, hkemb, hkN, hkfix, hkfront⟩ :=
    exists_original_finite_boundary_push K A hK hA hAK hne hN he
      (hKs.symm ▸ hj) (hKs.symm ▸ hjemb) (hKs.symm ▸ hjB)
  have hfix : EqOn k j (sphere (0 : V1) 1 ×ˢ Q2) := hAs ▸ hkfix
  refine ⟨k, hKs ▸ hkPL, hKs ▸ hkemb, hKs ▸ hkN, hfix, ?_, ?_⟩
  · intro x
    exact (hkfront ⟨x, hKs.symm ▸ x.property⟩).trans (by rw [hAs])
  · intro b u
    exact hfix ⟨endpoint_mem_sphere b, u.property⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
