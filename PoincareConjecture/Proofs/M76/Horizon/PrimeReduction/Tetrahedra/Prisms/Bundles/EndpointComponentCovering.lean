import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointComponentLocalHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Dependencies.Topology.Covering.Universal.Proper

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem exists_endpoint_component_projection_homeomorph
    {X Y A : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    {D : Set X} {B M S O K : Set Y}
    [SimplyConnectedSpace S] [LocallyPathConnectedSpace S]
    (f : X → Y) (hf : Continuous f) (hS : IsClosed S)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (W : (A × unitInterval) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOM : O ⊆ M) (hSO : S ⊆ O)
    (hcenter : ∀ z, (W z : Y) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (y₀ : Y) (hcover : connectedComponentIn (M \ S) y₀ ⊆ B)
    (hfinite : ∀ a, (f ⁻¹' {(W (a,⟨1/2,by norm_num,by norm_num⟩) : Y)}).Finite)
    (x₀ : X) (hx₀ : f x₀ ∈ S)
    (Γ : C(connectedComponentIn (f ⁻¹' S) x₀ × unitInterval,X))
    (hΓzero : ∀ p, Γ (p,0) = p)
    (hinto : ∀ p (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      Γ (p,t) ∈ D ∧ f (Γ (p,t)) ∈ connectedComponentIn (M \ S) y₀) :
    ∃ P : connectedComponentIn (f ⁻¹' S) x₀ ≃ₜ S, ∀ p, (P p : Y) = f p := by
  let : CompactSpace (f ⁻¹' S) := isCompact_iff_compactSpace.mp (hS.preimage hf).isCompact
  have hcompact : IsCompact (connectedComponentIn (f ⁻¹' S) x₀) := by
    rw [connectedComponentIn_eq_image (show x₀ ∈ f ⁻¹' S from hx₀)]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  let : CompactSpace (connectedComponentIn (f ⁻¹' S) x₀) :=
    isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace (connectedComponentIn (f ⁻¹' S) x₀) :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr
      (show x₀ ∈ f ⁻¹' S from hx₀))
  obtain ⟨π,hπ,hlocal⟩ := exists_endpoint_component_localHomeomorph f hf H hH W
    hO hOK hOM hSO hcenter y₀ hcover hfinite x₀ Γ hΓzero hinto
  have hbij := Poincare.Topology.bijective_proper_localHomeomorph hlocal π.continuous.isProperMap
  exact ⟨hlocal.toHomeomorphOfBijective hbij,hπ⟩

end PoincareConjecture.M76.PrismBelt
