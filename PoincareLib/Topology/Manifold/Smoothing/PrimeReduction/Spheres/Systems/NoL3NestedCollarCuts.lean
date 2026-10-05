import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.RawSphereCutComponents
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.SphericalSubregionModels

/-!
# Marked no-L3 preservation under nested original collar cuts

The two normal retractions identify their actual components in the same
raw sphere complement. A modeled component of the larger closed cut
would therefore contain a whole old cut component. Its constructed
spherical subregion model contradicts the old marked invariant.
-/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76

theorem HasNoPuncturedSphereComponents.mono_original_collar_cut
    {X E ι κ ν : Type*} [TopologicalSpace X] [T2Space X] [Finite κ] [Finite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : X → E}
    {A : Bool → κ → Type*} [∀ b i, TopologicalSpace (A b i)]
    (R : Set X) (Q : Bool → Set X) (O : Bool → κ → Set X) (S : κ → Set X)
    (W : ∀ b i, (A b i × unitInterval) ≃ₜ closure (O b i))
    (hQ : ∀ b, Q b = R \ ⋃ i, O b i) (hcQ : ∀ b, IsClosed (Q b))
    (hCR : ∀ b i, closure (O b i) ⊆ R)
    (hdis : ∀ b, Pairwise fun i j => Disjoint (closure (O b i)) (closure (O b j)))
    (hO : ∀ b i z, (W b i z : X) ∈ O b i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀ b i z, (W b i z : X) ∈ S i ↔ (z.2 : ℝ) = 1 / 2)
    (hSC : ∀ b i, S i ⊆ closure (O b i))
    (hnest : Q false ⊆ Q true)
    (hcompact : IsCompact (Q false)) (hPL : PLDomain e (Q false))
    (B : ν → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hfront : frontier (Q false) = ⋃ i, B i)
    (hno : HasNoPuncturedSphereComponents e f (Q false)) :
    HasNoPuncturedSphereComponents e f (Q true) := by
  obtain ⟨r,_,hrQ,_,hrcc,_⟩ := exists_raw_sphere_cut_component_map
    R (Q false) (O false) S (W false) (hQ false) (hcQ false)
    (hCR false) (hdis false) (hO false) (hS false) (hSC false)
  obtain ⟨_,_,_,_,_,hcomp,_⟩ := exists_raw_sphere_cut_component_map
    R (Q true) (O true) S (W true) (hQ true) (hcQ true)
    (hCR true) (hdis true) (hO true) (hS true) (hSC true)
  intro x hx hm
  have hxraw : x ∈ R \ ⋃ i, S i := by
    have h := mem_connectedComponentIn hx
    rw [hcomp x hx] at h
    exact connectedComponentIn_subset _ _ h.1
  have hy := hrQ hxraw
  have hynew : r x ∈ connectedComponentIn (Q true) x := by
    rw [hcomp x hx]
    exact ⟨hrcc x hxraw,hnest hy⟩
  have hsub : connectedComponentIn (Q false) (r x) ⊆ connectedComponentIn (Q true) x := by
    have hh := connectedComponentIn_mono (r x) hnest
    rwa [←connectedComponentIn_eq hynew] at hh
  obtain ⟨hD,hDPL,hDc,_,hDf⟩ := hPL.component_frontier_of_spheres hcompact B sB hfront hy
  exact hno (r x) hy (hm.of_connected_spherical_subregion hD hDPL hDc hsub
    (fun i : {i : ν // B i ⊆ connectedComponentIn (Q false) (r x)} => B i)
    (fun i => sB i) (fun i j hij => hBdis (Subtype.val_injective.ne hij)) hDf)

end PoincareMT.M76
