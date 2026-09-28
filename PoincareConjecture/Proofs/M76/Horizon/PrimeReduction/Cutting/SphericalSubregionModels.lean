import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalComponentSubregions

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HasPuncturedSphereModel

theorem component_of_spherical_subregion
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R Q : Set X} {f : X → E}
    (hm : HasPuncturedSphereModel e f R)
    (hQ : IsCompact Q) (hPL : PLDomain e Q) (hQR : Q ⊆ R)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Q = ⋃ i, S i) {x : X} (hx : x ∈ Q) :
    HasPuncturedSphereModel e f (connectedComponentIn Q x) := by
  obtain ⟨hf,n,A,r,M,G,C,hA,hAdis,hG,hC,hmark⟩ := hm
  obtain ⟨A',hA',hA'dis,u,H,hH,hu,_,_,hboundary⟩ :=
    hPL.exists_finitePL_punctured_component_model hQ hQR
      A r (fun i => (hA i).1) (fun i => (hA i).2.1) hAdis (fun i => (hA i).2.2)
      f hf G hG C hC hmark S sS hSdis hfront hx
  exact of_marked_model A' _
    (fun i => (hA' i).1) (fun i => (hA' i).2.1) hA'dis (fun i => (hA' i).2.2)
    hf u hu H hH hboundary

theorem of_connected_spherical_subregion
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R Q : Set X} {f : X → E}
    (hm : HasPuncturedSphereModel e f R)
    (hQ : IsCompact Q) (hPL : PLDomain e Q) (hQc : IsConnected Q) (hQR : Q ⊆ R)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Q = ⋃ i, S i) : HasPuncturedSphereModel e f Q := by
  obtain ⟨x,hx⟩ := hQc.nonempty
  have hh := hm.component_of_spherical_subregion hQ hPL hQR S sS hSdis hfront hx
  rwa [hQc.isPreconnected.connectedComponentIn hx] at hh

end PoincareConjecture.M76.HasPuncturedSphereModel
