import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiberMap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarUniformSide

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_endpoint_inward_family
    {E ι : Type*} [TopologicalSpace E] [T2Space E] [Finite ι]
    {A B T : ι → Set E} {S : Set E}
    (H : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (C : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ T j)
    (hA : ∀ j, IsCompact (A j))
    (hagree : ∀ j k (x : E) (hj : x ∈ T j) (hk : x ∈ T k) (t : I),
      (prismFiberInterpolation (C j) ⟨x,hj⟩ t : E) = prismFiberInterpolation (C k) ⟨x,hk⟩ t)
    (hcap : ∀ j x, (H j x : E) ∈ S ↔ (x : E × ℝ).2 = 0 ∨ (x : E × ℝ).2 = 1)
    (r : E → E) (hr : ContinuousOn r (⋃ j,T j))
    (hrv : ∀ j x, r (C j x) = H j x) :
    ∃ Γ : C((⋃ j,prismEnds (C j)) × I,E),
      (∀ j a b t, Γ (prismEndpointLift C j a b,t) =
        H j ⟨(a,fiberFlip b t),a.property,(fiberFlip b t).property⟩) ∧
      (∀ p, Γ (p,0) = r p) ∧ (∀ p, Γ (p,0) ∈ S) ∧
      ∀ p (t : I), 0 < (t : ℝ) → (t : ℝ) < 1 → Γ (p,t) ∉ S := by
  obtain ⟨L,hL⟩ := exists_continuous_prism_interpolation C hA hagree
  let Γ : C((⋃ j,prismEnds (C j)) × I,E) :=
    ⟨fun z => r (prismEndpointFiberMap C L z),
      hr.domRestrict.comp (prismEndpointFiberMap C L).continuous⟩
  have hΓ (j) (a : A j) (b : Bool) (t : I) :
      Γ (prismEndpointLift C j a b,t) =
        H j ⟨(a,fiberFlip b t),a.property,(fiberFlip b t).property⟩ := by
    change r (prismEndpointFiberMap C L _) = _
    rw [prismEndpointFiberMap_apply C L hL,hrv]
  have hrepresent (p : (⋃ j,prismEnds (C j))) :
      ∃ (j : ι) (a : A j) (b : Bool), p = prismEndpointLift C j a b := by
    obtain ⟨j,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
    exact ⟨j,a,b,Subtype.ext hp.symm⟩
  refine ⟨Γ,hΓ,?_,?_,?_⟩
  · intro p
    obtain ⟨j,a,b,rfl⟩ := hrepresent p
    rw [hΓ]
    change (H j _ : E) = r (C j _)
    rw [hrv]
    congr 2
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact fiberFlip_zero b
  · intro p
    obtain ⟨j,a,b,rfl⟩ := hrepresent p
    rw [hΓ,hcap]
    cases b <;> simp
  · intro p t ht ht1
    obtain ⟨j,a,b,rfl⟩ := hrepresent p
    rw [hΓ,hcap]
    cases b
    · exact not_or.mpr ⟨ne_of_gt ht,ne_of_lt ht1⟩
    · change ¬ (1 - (t : ℝ) = 0 ∨ 1 - (t : ℝ) = 1)
      exact not_or.mpr ⟨by linarith,by linarith⟩

end PoincareConjecture.M76.PrismBelt
