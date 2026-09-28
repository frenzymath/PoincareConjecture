import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointOrbitCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberMidpoint

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def prismEndpointInclusion {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (x : (⋃ i, prismEnds (H i) : Set E)) : (⋃ i, B i : Set E) :=
  ⟨x,by
    obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i,prismEnds_subset (H i) hi⟩⟩

theorem continuous_prismEndpointInclusion {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) :
    Continuous (prismEndpointInclusion H) := continuous_subtype_val.subtype_mk _

theorem isCompact_prismEnds {E : Type*} [TopologicalSpace E]
    {A B : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hA : IsCompact A) :
    IsCompact (prismEnds H) := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hc (b : Bool) : IsCompact (range (fun x : A => (prismEndMap H x b : E))) :=
    isCompact_range ((continuous_subtype_val.comp H.continuous).comp
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _))
  have he : prismEnds H = range (fun x : A => (prismEndMap H x false : E)) ∪
      range (fun x : A => (prismEndMap H x true : E)) := by
    ext x
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      cases b
      · exact Or.inl ⟨a,rfl⟩
      · exact Or.inr ⟨a,rfl⟩
    · rintro (⟨a,rfl⟩ | ⟨a,rfl⟩)
      · exact ⟨(a,false),rfl⟩
      · exact ⟨(a,true),rfl⟩
  exact he ▸ (hc false).union (hc true)

theorem prismFiberMidpoint_end {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) (b : Bool) :
    prismFiberMidpoint H (prismEndMap H ⟨(H.symm x : E × ℝ).1,(H.symm x).property.1⟩ b) =
      prismFiberMidpoint H x := by
  simp only [prismFiberMidpoint,prismEndMap,H.symm_apply_apply]

theorem exists_endpoint_with_same_midpoint
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (m : C((⋃ i, B i), (⋃ i, B i)))
    (hm : ∀ i (x : B i), (m ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : E) =
      prismFiberMidpoint (H i) x)
    (x : (⋃ i, B i : Set E)) :
    ∃ p : (⋃ i, prismEnds (H i) : Set E), m (prismEndpointInclusion H p) = m x := by
  obtain ⟨i,hxi⟩ := mem_iUnion.mp x.property
  let xi : B i := ⟨x,hxi⟩
  let a : A i := ⟨((H i).symm xi : E × ℝ).1,((H i).symm xi).property.1⟩
  refine ⟨prismEndpointLift H i a false,?_⟩
  apply Subtype.ext
  change (m ⟨prismEndMap (H i) a false,_⟩ : E) = m x
  rw [hm]
  exact (congrArg Subtype.val (prismFiberMidpoint_end (H i) xi false)).trans (hm i xi).symm

theorem range_midpoint_eq_fixed_locus
    {U : Type*} [TopologicalSpace U] (J : U ≃ₜ U) (m : U → U)
    (hfixed : ∀ x, J (m x) = m x) (hfixes : ∀ x, J x = x → m x = x) :
    range m = {x | J x = x} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact hfixed y
  · intro hx
    exact ⟨x,hfixes x hx⟩

theorem exists_prism_endpoint_midpoint_map
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (J : (⋃ i, B i) ≃ₜ (⋃ i, B i)) (m : C((⋃ i, B i), (⋃ i, B i)))
    (hm : ∀ i (x : B i), (m ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : E) =
      prismFiberMidpoint (H i) x)
    (hfixed : ∀ x, J (m x) = m x) (hfixes : ∀ x, J x = x → m x = x) :
    ∃ μ : C((⋃ i, prismEnds (H i)), {x : (⋃ i, B i : Set E) | J x = x}),
      (∀ p, (μ p).1 = m (prismEndpointInclusion H p)) ∧ Function.Surjective μ := by
  let μ : C((⋃ i, prismEnds (H i)), {x : (⋃ i, B i : Set E) | J x = x}) :=
    ⟨fun p => ⟨m (prismEndpointInclusion H p),hfixed _⟩,
      (m.continuous.comp (continuous_prismEndpointInclusion H)).subtype_mk _⟩
  refine ⟨μ,fun _ => rfl,?_⟩
  intro x
  obtain ⟨p,hp⟩ := exists_endpoint_with_same_midpoint H m hm x.1
  exact ⟨p,Subtype.ext (hp.trans (hfixes x.1 x.2))⟩

end PoincareConjecture.M76.PrismBelt
