import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalBallPuncturedModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalComponentSubregions










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.component_model_of_spherical_subregion
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {B bd Q : Set X}
    (ball : ChartwisePLBall e B bd) (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (hQB : Q ⊆ B) (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Q = ⋃ i, S i)
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f B) {x : X} (hx : x ∈ Q) :
    HasPuncturedSphereModel e f (connectedComponentIn Q x) := by
  obtain ⟨_, n, A, r, M, G, C, hA, hAdis, hG, hC, hmark⟩ :=
    ball.hasPuncturedSphereModel f hf hfi
  obtain ⟨B', hB', hBdis, u, H, hH, hu, _, _, hboundary⟩ :=
    hPL.exists_finitePL_punctured_component_model hQ hQB A r
      (fun i => (hA i).1) (fun i => (hA i).2.1) hAdis (fun i => (hA i).2.2)
      f hf G hG C hC hmark S sS hSdis hfront hx
  exact HasPuncturedSphereModel.of_marked_model B' _
    (fun i => (hB' i).1) (fun i => (hB' i).2.1) hBdis (fun i => (hB' i).2.2)
    hf u hu H hH hboundary

theorem ChartwisePLBall.model_of_connected_spherical_subregion
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {B bd Q : Set X}
    (ball : ChartwisePLBall e B bd) (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (hQc : IsConnected Q) (hQB : Q ⊆ B)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Q = ⋃ i, S i)
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f B) : HasPuncturedSphereModel e f Q := by
  obtain ⟨x, hx⟩ := hQc.nonempty
  have hm := ball.component_model_of_spherical_subregion hQ hPL hQB S sS hSdis hfront f hf hfi hx
  rwa [hQc.isPreconnected.connectedComponentIn hx] at hm

theorem HasNoPuncturedSphereComponents.not_spherical_component_subset_ball
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {B bd Q : Set X} {f : X → E}
    (hno : HasNoPuncturedSphereComponents e f Q)
    (ball : ChartwisePLBall e B bd) {x : X} (hx : x ∈ Q)
    (hD : IsCompact (connectedComponentIn Q x))
    (hDPL : PLDomain e (connectedComponentIn Q x))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier (connectedComponentIn Q x) = ⋃ i, S i)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f B) : ¬ connectedComponentIn Q x ⊆ B := by
  intro hDB
  exact hno x hx (ball.model_of_connected_spherical_subregion hD hDPL
    ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
    hDB S sS hSdis hfront f hf hfi)

theorem HasNoPuncturedSphereComponents.not_component_subset_ball
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {B bd Q : Set X} {f : X → E}
    (hno : HasNoPuncturedSphereComponents e f Q)
    (ball : ChartwisePLBall e B bd) (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Q = ⋃ i, S i)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f B) {x : X} (hx : x ∈ Q) :
    ¬ connectedComponentIn Q x ⊆ B := by
  obtain ⟨hD, hDPL, _, _, hDf⟩ := hPL.component_frontier_of_spheres hQ S sS hfront hx
  exact hno.not_spherical_component_subset_ball ball hx hD hDPL
    (fun i : {i : κ // S i ⊆ connectedComponentIn Q x} => S i)
    (fun i => sS i) (fun i j hij => hSdis (Subtype.val_injective.ne hij)) hDf hf hfi

end PoincareConjecture.M76
