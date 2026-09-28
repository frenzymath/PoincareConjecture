import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiberMap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.RawPrismRescalingInjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointInwardComponent

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_endpoint_component_inward_family
    {E ι : Type*} [TopologicalSpace E] [T2Space E] [Finite ι]
    {A B T : ι → Set E} {S : Set E}
    (H : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (C : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ T j)
    (hA : ∀ j, IsCompact (A j))
    (hagree : ∀ j k (x : E) (hj : x ∈ T j) (hk : x ∈ T k) (t : I),
      (prismFiberInterpolation (C j) ⟨x,hj⟩ t : E) = prismFiberInterpolation (C k) ⟨x,hk⟩ t)
    (hcap : ∀ j x, (H j x : E) ∈ S ↔ (x : E × ℝ).2 = 0 ∨ (x : E × ℝ).2 = 1)
    (r : E → E) (hr : ContinuousOn r (⋃ j,T j))
    (hrv : ∀ j x, r (C j x) = H j x)
    (p : (⋃ j,prismEnds (C j) : Set E)) :
    ∃ y₀ ∈ (⋃ j,B j) \ S,
      ∃ Θ : C(connectedComponentIn (⋃ j,prismEnds (C j)) (p : E) × I,(⋃ j,T j)),
        (∀ q, (Θ (q,0) : E) = q) ∧
        (∀ j (a : A j) (b : Bool), p = prismEndpointLift C j a b →
          y₀ = H j ⟨(a,(1/2 : ℝ)),a.property,by norm_num⟩) ∧
        ∀ q (t : I), 0 < (t : ℝ) → (t : ℝ) < 1 →
          (Θ (q,t) : E) ∉ ⋃ j,prismEnds (C j) ∧
          r (Θ (q,t)) ∈ connectedComponentIn ((⋃ j,B j) \ S) y₀ := by
  obtain ⟨L,hL⟩ := exists_continuous_prism_interpolation C hA hagree
  let P := connectedComponentIn (⋃ j,prismEnds (C j)) (p : E)
  let inc : C(P,(⋃ j,prismEnds (C j))) :=
    ⟨fun q => ⟨q,connectedComponentIn_subset _ _ q.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let Θ : C(P × I,(⋃ j,T j)) :=
    ⟨fun z => prismEndpointFiberMap C L (inc z.1,z.2),
      (prismEndpointFiberMap C L).continuous.comp
        ((inc.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hrepresent (q : P) : ∃ (j : ι) (a : A j) (b : Bool), inc q = prismEndpointLift C j a b := by
    obtain ⟨j,⟨⟨a,b⟩,hq⟩⟩ := mem_iUnion.mp (inc q).property
    exact ⟨j,a,b,Subtype.ext hq.symm⟩
  have hΘ (q : P) (j) (a : A j) (b : Bool)
      (hq : inc q = prismEndpointLift C j a b) (t : I) :
      (Θ (q,t) : E) = C j ⟨(a,fiberFlip b t),a.property,(fiberFlip b t).property⟩ := by
    change (prismEndpointFiberMap C L (inc q,t) : E) = _
    rw [hq,prismEndpointFiberMap_apply C L hL]
  have hzero (q : P) : (Θ (q,0) : E) = q := by
    obtain ⟨j,a,b,hq⟩ := hrepresent q
    rw [hΘ q j a b hq]
    have hv := congrArg Subtype.val hq
    change (q : E) = prismEndMap (C j) a b at hv
    rw [hv]
    congr 2
    apply Subtype.ext
    exact Prod.ext rfl (fiberFlip_zero b)
  have hinto (q : P) (t : I) (ht : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
      r (Θ (q,t)) ∈ (⋃ j,B j) \ S := by
    obtain ⟨j,a,b,hq⟩ := hrepresent q
    rw [hΘ q j a b hq,hrv]
    refine ⟨mem_iUnion.mpr ⟨j,(H j _).property⟩,?_⟩
    rw [hcap]
    cases b
    · exact not_or.mpr ⟨ne_of_gt ht,ne_of_lt ht1⟩
    · change ¬ (1 - (t : ℝ) = 0 ∨ 1 - (t : ℝ) = 1)
      exact not_or.mpr ⟨by linarith,by linarith⟩
  let : ConnectedSpace P := isConnected_iff_connectedSpace.mp
    (isConnected_connectedComponentIn_iff.mpr p.property)
  let Γ : C(P × I,E) := ⟨fun z => r (Θ z),hr.domRestrict.comp Θ.continuous⟩
  let p₀ : P := ⟨p,mem_connectedComponentIn p.property⟩
  let t₀ : I := ⟨1/2,by norm_num,by norm_num⟩
  have hmid (j) (a : A j) (b : Bool) (hp : p = prismEndpointLift C j a b) :
      Γ (p₀,t₀) = H j ⟨(a,(1/2 : ℝ)),a.property,by norm_num⟩ := by
    change r (Θ (p₀,t₀)) = _
    rw [hΘ p₀ j a b hp,hrv]
    congr 2
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · cases b <;> norm_num [t₀,fiberFlip,unitInterval.symm]
  refine ⟨Γ (p₀,t₀),hinto p₀ t₀ (by norm_num [t₀]) (by norm_num [t₀]),Θ,hzero,hmid,?_⟩
  intro q t ht ht1
  refine ⟨?_,inward_family_mem_connectedComponentIn Γ hinto p₀ q t ht ht1⟩
  intro hends
  exact (hinto q t ht ht1).2
    ((raw_prism_rescaling_mem_caps_iff A B T S H C hcap r hrv (Θ (q,t)).property).mpr hends)

end PoincareConjecture.M76.PrismBelt
