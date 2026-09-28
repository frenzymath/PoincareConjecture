import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Collars.OriginalAnnulusPush
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.AnnulusProjection









set_option autoImplicit false
open Set Metric Geometry PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem Stage.exists_pushed_marked_annulus
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3}
    {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → M}
    {r : M → ℝ} {C : Set M} (st : Stage e S f r C)
    (hS : S.space = ProtectedAnnulus.source)
    {R : Set M} {N : Set st.Carrier} (hN : IsCompact N)
    (heN : PoincareConjecture.M76.PLDomain st.charts N) (hNR : N ⊆ st.projection ⁻¹' R)
    {j : (V1 × V2) → st.Carrier}
    (hj : PolyhedralPLInCharts st.charts j ProtectedAnnulus.source)
    (hjemb : Topology.IsEmbedding (fun x : ProtectedAnnulus.source ↦ j x))
    (hjB : MapsTo j ProtectedAnnulus.source (frontier N))
    (hrims : ∀ (b : Bool) (u : Q2),
      j (ProtectedAnnulus.endpoint b, u) = st.annulusRim hS b u)
    (hfront : ∀ (b : Bool) (u : Q2),
      f (ProtectedAnnulus.endpoint b, u) ∈ frontier R) :
    ∃ k : (V1 × V2) → st.Carrier,
      PolyhedralPLInCharts st.charts k ProtectedAnnulus.source ∧
      Topology.IsEmbedding (fun x : ProtectedAnnulus.source ↦ k x) ∧
      MapsTo k ProtectedAnnulus.source (st.projection ⁻¹' R) ∧
      (∀ (b : Bool) (u : Q2), k (ProtectedAnnulus.endpoint b, u) = st.annulusRim hS b u) ∧
      ∀ x : ProtectedAnnulus.source,
        k x ∈ frontier (st.projection ⁻¹' R) ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  obtain ⟨k, hk, hki, hkN, _, hproper, hfix⟩ :=
    ProtectedAnnulus.exists_original_annulus_push hN heN hj hjemb hjB
  have hkrim (b : Bool) (u : Q2) :
      k (ProtectedAnnulus.endpoint b, u) = st.annulusRim hS b u :=
    (hfix b u).trans (hrims b u)
  refine ⟨k, hk, hki, fun x hx ↦ hNR (hkN hx), hkrim, ?_⟩
  intro x
  constructor
  · intro hf
    by_contra hx
    have hxN : k x ∈ interior N :=
      (mem_interior_iff_notMem_frontier (hkN x.property)).mpr
        (fun h ↦ hx ((hproper x).mp h).1)
    exact hf.2 (interior_mono hNR hxN)
  · intro hx
    obtain ⟨b, hb⟩ := (ProtectedAnnulus.mem_sphere_iff_exists_endpoint _).mp hx
    have hpair : (x : V1 × V2) = (ProtectedAnnulus.endpoint b, (x : V1 × V2).2) :=
      Prod.ext hb rfl
    rw [st.frontier_region R]
    change st.projection (k x) ∈ frontier R
    rw [hpair, hkrim b ⟨(x : V1 × V2).2, x.property.2⟩, st.annulusRim_projection]
    exact hfront b ⟨(x : V1 × V2).2, x.property.2⟩

end Geometry.OriginalPLTower
