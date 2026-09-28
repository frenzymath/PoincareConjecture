import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointComponentCovering
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointSphereCovering
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finitePL_endpoint_sphere_of_core
    {E X A ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [LocallyPathConnectedSpace A]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set E} {B M S O K : Set X}
    (hU : IsCompact U) (s : ChartwisePLSphere e S)
    (f : U → X) (hf : Continuous f) {D : Set U}
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (W : (A × unitInterval) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOM : O ⊆ M) (hSO : S ⊆ O)
    (hcenter : ∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (y₀ : X) (hcover : connectedComponentIn (M \ S) y₀ ⊆ B)
    (hfinite : ∀ a, (f ⁻¹' {(W (a,⟨1/2,by norm_num,by norm_num⟩) : X)}).Finite)
    (x₀ : U) (hx₀ : f x₀ ∈ S)
    (Γ : C(connectedComponentIn (f ⁻¹' S) x₀ × unitInterval,U))
    (hΓzero : ∀ q, Γ (q,0) = q)
    (hinto : ∀ q (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      Γ (q,t) ∈ D ∧ f (Γ (q,t)) ∈ connectedComponentIn (M \ S) y₀)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S)
    (p : E → E)
    (hp : FinitePiecewiseAffineOn p
      ((Subtype.val : U → E) '' connectedComponentIn (f ⁻¹' S) x₀))
    (hpval : ∀ q : connectedComponentIn (f ⁻¹' S) x₀, p (q : U) = F (f q)) :
    ∃ Q : sphere (0 : V3) 1 ≃ₜ
        ((Subtype.val : U → E) '' connectedComponentIn (f ⁻¹' S) x₀),
      Q.IsFinitePL ∧ Q.symm.IsFinitePL ∧ ∀ z, p (Q z) = F (s.parametrization z) := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let : SimplyConnectedSpace S := s.lifting_connectedness.1
  let : LocallyPathConnectedSpace S := s.lifting_connectedness.2
  obtain ⟨P,hP⟩ := exists_endpoint_component_projection_homeomorph f hf s.isCompact.isClosed
    H hH W hO hOK hOM hSO hcenter y₀ hcover hfinite x₀ hx₀ Γ hΓzero hinto
  let T := (Subtype.val : U → E) '' connectedComponentIn (f ⁻¹' S) x₀
  let flat : connectedComponentIn (f ⁻¹' S) x₀ ≃ₜ T :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage _
  have hflat (q : connectedComponentIn (f ⁻¹' S) x₀) : (flat q : E) = (q : U) := rfl
  have hflatback (q : T) : ((flat.symm q : U) : E) = q :=
    (hflat (flat.symm q)).symm.trans (congrArg Subtype.val (flat.apply_symm_apply q))
  let J : T ≃ₜ S := flat.symm.trans P
  let : ConnectedSpace T := J.symm.surjective.connectedSpace J.symm.continuous
  have hT : IsConnected T := isConnected_iff_connectedSpace.mpr inferInstance
  have hJ (q : T) : (J q : X) = f (flat.symm q) := hP _
  have hpJ (q : T) : p q = F (J q) := by
    rw [hJ,← hpval, hflatback]
  obtain ⟨_,_,Q,hQ,hQinv,hQvalue⟩ := exists_finitePL_sphere_of_original_localHomeomorph
    s F hF hFi hT J J.isLocalHomeomorph p hp hpJ
  refine ⟨Q,hQ,hQinv,?_⟩
  intro z
  rw [hpJ,hQvalue]

end PoincareConjecture.M76.PrismBelt
