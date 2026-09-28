import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointSphereFromCore
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ComponentMembership







set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finitePL_endpoint_sphere_of_finite_system
    {E X A ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [LocallyPathConnectedSpace A] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set E} {B M : Set X}
    (hU : IsCompact U) (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (f : U → X) (hf : Continuous f) {D : Set U}
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (O K : κ → Set X) (W : ∀ i, (A × unitInterval) ≃ₜ K i)
    (hO : ∀ i, IsOpen (O i)) (hOK : ∀ i, O i ⊆ K i)
    (hOM : ∀ i, O i ⊆ M) (hSO : ∀ i, S i ⊆ O i)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (y₀ : X) (hcover : connectedComponentIn (M \ ⋃ i, S i) y₀ ⊆ B)
    (hfinite : ∀ y, (f ⁻¹' {y}).Finite)
    (x₀ : U) (hx₀ : f x₀ ∈ ⋃ i, S i)
    (Γ : C(connectedComponentIn (f ⁻¹' ⋃ i, S i) x₀ × unitInterval,U))
    (hΓzero : ∀ q, Γ (q,0) = q)
    (hinto : ∀ q (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      Γ (q,t) ∈ D ∧ f (Γ (q,t)) ∈ connectedComponentIn (M \ ⋃ i, S i) y₀)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F (⋃ i, S i))
    (p : E → E)
    (hp : FinitePiecewiseAffineOn p
      ((Subtype.val : U → E) '' connectedComponentIn (f ⁻¹' ⋃ i, S i) x₀))
    (hpval : ∀ q : connectedComponentIn (f ⁻¹' ⋃ i, S i) x₀, p (q : U) = F (f q)) :
    ∃ i, f x₀ ∈ S i ∧
      ∃ Q : sphere (0 : V3) 1 ≃ₜ
        ((Subtype.val : U → E) '' connectedComponentIn (f ⁻¹' ⋃ j, S j) x₀),
        Q.IsFinitePL ∧ Q.symm.IsFinitePL ∧ ∀ z, p (Q z) = F ((sS i).parametrization z) := by
  obtain ⟨i,⟨hxi,heq⟩,_⟩ := exists_unique_preimage_component_member S
    (fun i => (sS i).isCompact.isClosed) hdis f hf x₀ hx₀
  refine ⟨i,hxi,?_⟩
  revert Γ
  rw [heq] at hp hpval ⊢
  intro Γ hΓzero hinto
  let R : Set X := ⋃ j : {j : κ // j ≠ i}, S j.val
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => (sS j.val).isCompact.isClosed)
  have hSR : Disjoint (S i) R := by
    apply disjoint_left.mpr
    rintro x hx ⟨_,⟨j,rfl⟩,hj⟩
    exact disjoint_left.mp (hdis (Ne.symm j.property)) hx hj
  have hdiff : ((M \ R) \ S i : Set X) = M \ ⋃ j, S j := by
    ext x
    constructor
    · rintro ⟨⟨hxM,hxR⟩,hxi⟩
      refine ⟨hxM,?_⟩
      intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · exact hxi (hji ▸ hj)
      · exact hxR (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
    · rintro ⟨hxM,hx⟩
      refine ⟨⟨hxM,?_⟩,fun hi => hx (mem_iUnion.mpr ⟨i,hi⟩)⟩
      intro hr
      obtain ⟨j,hj⟩ := mem_iUnion.mp hr
      exact hx (mem_iUnion.mpr ⟨j.val,hj⟩)
  apply exists_finitePL_endpoint_sphere_of_core (M := M \ R) (O := O i \ R)
    hU (sS i) f hf H hH (W i)
    ((hO i).sdiff hR) (fun _ hx => hOK i hx.1)
    (fun _ hx => ⟨hOM i hx.1,hx.2⟩)
    (fun _ hx => ⟨hSO i hx,fun hr => disjoint_left.mp hSR hx hr⟩)
    (hcenter i) y₀ (by simpa only [hdiff] using hcover)
    (fun _ => hfinite _) x₀ hxi Γ hΓzero
    (by simpa only [hdiff] using hinto) F hF (hFi.mono (subset_iUnion S i)) p hp hpval

end PoincareConjecture.M76.PrismBelt
