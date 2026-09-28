import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointSphereFiniteSystem
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCapProjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.RawPrismRescalingInjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.FiniteCarrierComponents
import PoincareConjecture.Proofs.M76.Horizon.Dependencies.Topology.Connected.Subtype








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finitePL_prism_endpoint_sphere_of_core
    {E X A ι κ η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [LocallyPathConnectedSpace A] [Finite κ] [Finite η]
    {e : ι → OpenPartialHomeomorph X V3} {B M : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {Ac Bc Tc : η → Set E}
    (Hc : ∀ j, (Ac j ×ˢ I : Set (E × ℝ)) ≃ₜ Bc j)
    (C : ∀ j, (Ac j ×ˢ I : Set (E × ℝ)) ≃ₜ Tc j)
    (hC : ∀ j, (C j).IsFinitePL)
    (r : E → E) (hr : FinitePiecewiseAffineOn r (⋃ j,Tc j))
    (hrv : ∀ j x, r (C j x) = Hc j x)
    (f : (⋃ j,Tc j : Set E) → X) (hf : Continuous f)
    (hcap : ∀ j x, f ⟨C j x,mem_iUnion.mpr ⟨j,(C j x).property⟩⟩ ∈ ⋃ i,S i ↔
      (x : E × ℝ).2 = 0 ∨ (x : E × ℝ).2 = 1)
    {D : Set (⋃ j,Tc j : Set E)}
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (O K : κ → Set X) (W : ∀ i, (A × unitInterval) ≃ₜ K i)
    (hO : ∀ i, IsOpen (O i)) (hOK : ∀ i, O i ⊆ K i)
    (hOM : ∀ i, O i ⊆ M) (hSO : ∀ i, S i ⊆ O i)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (y₀ : X) (hcover : connectedComponentIn (M \ ⋃ i,S i) y₀ ⊆ B)
    (p : (⋃ j,prismEnds (C j) : Set E))
    (Γ : C(connectedComponentIn (⋃ j,prismEnds (C j)) (p : E) × I,(⋃ j,Tc j)))
    (hΓzero : ∀ q, (Γ (q,0) : E) = q)
    (hinto : ∀ q (t : I), 0 < (t : ℝ) → (t : ℝ) < 1 →
      Γ (q,t) ∈ D ∧ f (Γ (q,t)) ∈ connectedComponentIn (M \ ⋃ i,S i) y₀)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F (⋃ i,S i))
    (hrF : ∀ x : (⋃ j,Tc j : Set E), r x = F (f x)) :
    ∃ i, ∃ Q : sphere (0 : V3) 1 ≃ₜ connectedComponentIn (⋃ j,prismEnds (C j)) (p : E),
      Q.IsFinitePL ∧ Q.symm.IsFinitePL ∧ ∀ z, r (Q z) = F ((sS i).parametrization z) := by
  let U := (⋃ j,Tc j : Set E)
  let Ends := (⋃ j,prismEnds (C j) : Set E)
  have hEU : Ends ⊆ U := iUnion_mono (fun j => prismEnds_subset (C j))
  have hpre : f ⁻¹' (⋃ i,S i) = (Subtype.val : U → E) ⁻¹' Ends := by
    ext x
    obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
    let z := (C j).symm ⟨x,hj⟩
    have hzx : (C j z : E) = x := congrArg Subtype.val ((C j).apply_symm_apply ⟨x,hj⟩)
    have hpoint : (⟨C j z,mem_iUnion.mpr ⟨j,(C j z).property⟩⟩ : U) = x := Subtype.ext hzx
    constructor
    · intro hx
      have hz := (hcap j z).mp (hpoint.symm ▸ hx)
      exact mem_iUnion.mpr ⟨j,hzx ▸ (prism_mem_ends_iff (C j) z).mpr hz⟩
    · intro hx
      obtain ⟨k,⟨⟨a,b⟩,hk⟩⟩ := mem_iUnion.mp hx
      have hpoint' : (⟨prismEndMap (C k) a b,
          mem_iUnion.mpr ⟨k,(prismEndMap (C k) a b).property⟩⟩ : U) = x := Subtype.ext hk
      rw [← hpoint']
      apply (hcap k _).mpr
      cases b <;> simp
  let p₀ : U := ⟨p,hEU p.property⟩
  have hp₀ : f p₀ ∈ ⋃ i,S i := by
    change p₀ ∈ f ⁻¹' (⋃ i,S i)
    rw [hpre]
    exact p.property
  have hcomponent : (Subtype.val : U → E) '' connectedComponentIn (f ⁻¹' ⋃ i,S i) p₀ =
      connectedComponentIn Ends (p : E) := by
    rw [hpre]
    exact Poincare.Topology.subtype_image_connectedComponentIn hEU p₀ p.property
  let J : connectedComponentIn (f ⁻¹' ⋃ i,S i) p₀ ≃ₜ connectedComponentIn Ends (p : E) :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage _).trans (Homeomorph.setCongr hcomponent)
  have hJ (q : connectedComponentIn (f ⁻¹' ⋃ i,S i) p₀) : (J q : E) = (q : U) := rfl
  let Γ' : C(connectedComponentIn (f ⁻¹' ⋃ i,S i) p₀ × I,U) :=
    ⟨fun z => Γ (J z.1,z.2),Γ.continuous.comp
      ((J.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hΓ'zero (q) : Γ' (q,0) = q := Subtype.ext ((hΓzero (J q)).trans (hJ q))
  have hfinite (y : X) : (f ⁻¹' {y}).Finite := by
    refine (finite_fiber_of_prism_cell_maps Hc C r hrv (F y)).1.of_injOn ?_
      Subtype.val_injective.injOn
    intro x hx
    exact ⟨x.property,(hrF x).trans (congrArg F hx)⟩
  obtain ⟨Kc,hKc,hKcs⟩ := exists_finite_prism_endpoint_triangulation C hC
  obtain ⟨N,hN,hNs⟩ := exists_finite_triangulation_connectedComponentIn Kc hKc (p : E)
  have hNs' : N.space = connectedComponentIn Ends (p : E) := by simpa only [hKcs] using hNs
  have hrcomponent : FinitePiecewiseAffineOn r (connectedComponentIn Ends (p : E)) :=
    hNs' ▸ hr.restrict N hN
      (hNs'.subset.trans ((connectedComponentIn_subset Ends (p : E)).trans hEU))
  obtain ⟨i,_,Q,hQ,_,hQval⟩ := exists_finitePL_endpoint_sphere_of_finite_system hr.isCompact
    S sS hdis f hf H hH O K W hO hOK hOM hSO hcenter y₀ hcover hfinite p₀ hp₀
    Γ' hΓ'zero (fun q t ht ht1 => hinto (J q) t ht ht1) F hF hFi r
    (hcomponent.symm ▸ hrcomponent) (fun q => hrF q)
  have hQ' := hQ.setCongr rfl hcomponent
  exact ⟨i,Q.trans (Homeomorph.setCongr hcomponent),hQ',hQ'.symm,hQval⟩

end PoincareConjecture.M76.PrismBelt
