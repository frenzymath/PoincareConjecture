import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointOrbitCover









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def prismEndpointLift {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (i : ι) (x : A i) (b : Bool) : (⋃ i, prismEnds (H i) : Set E) :=
  ⟨prismEndMap (H i) x b,mem_iUnion.mpr ⟨i,⟨(x,b),rfl⟩⟩⟩

theorem continuous_prismEndpointLift {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (i : ι) (b : Bool) : Continuous (fun x => prismEndpointLift H i x b) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (H i).continuous).comp
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)

theorem exists_prism_endpoint_quotient_cap_charts
    {E ι : Type*} [TopologicalSpace E] [T2Space E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (hA : ∀ i, IsCompact (A i))
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτ : Function.Involutive τ)
    (hends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b)) :
    let q := FreeInvolutionQuotient.projection τ hτ
    let m := fun i (x : A i) => q (prismEndpointLift H i x false)
    (∀ i, ∃ G : A i ≃ₜ range (m i), ∀ x, (G x : FreeInvolutionQuotient.Model τ hτ) = m i x) ∧
    (∀ i (x : A i), q (prismEndpointLift H i x true) = m i x) ∧
    (⋃ i, range (m i)) = univ := by
  classical
  let q := FreeInvolutionQuotient.projection τ hτ
  let m := fun i (x : A i) => q (prismEndpointLift H i x false)
  have htop (i : ι) (x : A i) : q (prismEndpointLift H i x true) = m i x := by
    have hτend : τ (prismEndpointLift H i x false) = prismEndpointLift H i x true :=
      Subtype.ext (hends i x false)
    rw [←hτend]
    exact FreeInvolutionQuotient.projection_involution τ hτ _
  refine ⟨?_,htop,?_⟩
  · intro i
    have hmc : Continuous (m i) :=
      (FreeInvolutionQuotient.continuous_projection τ hτ).comp (continuous_prismEndpointLift H i false)
    have hmi : Function.Injective (m i) := by
      intro x y hxy
      rcases (FreeInvolutionQuotient.projection_eq τ hτ _ _).mp hxy with h | h
      · have hh := congrArg (fun z : (⋃ i, prismEnds (H i) : Set E) => (z : E)) h
        have hv := (H i).injective (Subtype.ext hh)
        exact Subtype.ext (congrArg (fun z : (A i ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).1) hv)
      · have hh := congrArg (fun z : (⋃ i, prismEnds (H i) : Set E) => (z : E)) h
        rw [hends] at hh
        have hv := (H i).injective (Subtype.ext hh)
        have ht := congrArg (fun z : (A i ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).2) hv
        norm_num [prismEndpointLift,prismEndMap] at ht
    let : CompactSpace (A i) := isCompact_iff_compactSpace.mp (hA i)
    exact ⟨(hmc.isClosedEmbedding hmi).isEmbedding.toHomeomorph,fun _ => rfl⟩
  · apply Subset.antisymm (subset_univ _)
    intro z _
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
    obtain ⟨i,⟨⟨y,b⟩,hy⟩⟩ := mem_iUnion.mp x.property
    have hx : x = prismEndpointLift H i y b := Subtype.ext hy.symm
    change q x ∈ ⋃ i, range (m i)
    rw [hx]
    cases b
    · exact mem_iUnion.mpr ⟨i,⟨y,rfl⟩⟩
    · exact mem_iUnion.mpr ⟨i,⟨y,(htop i y).symm⟩⟩

end PoincareConjecture.M76.PrismBelt
