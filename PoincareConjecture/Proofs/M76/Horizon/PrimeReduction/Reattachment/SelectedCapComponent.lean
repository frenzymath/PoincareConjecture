import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FiniteCapComponentCarriers
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.CarrierComponentTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FiniteRetainedBallReplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.SelectedComponentBoundaries



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem irreducible_ambient_component_preimage
    {E α : Type*} [TopologicalSpace E] [T2Space E]
    {W D T : Set E} (hDW : D ⊆ W)
    (atlas : α → OpenPartialHomeomorph W V3)
    (hI : IsPLIrreducible atlas ((Subtype.val : W → E) ⁻¹' D))
    (hD : IsCompact ((Subtype.val : W → E) ⁻¹' D))
    {x : E} (hx : x ∈ D) (hT : connectedComponentIn D x = T) :
    IsPLIrreducible atlas ((Subtype.val : W → E) ⁻¹' T) := by
  let xW : W := ⟨x,hDW hx⟩
  have hcc : connectedComponentIn ((Subtype.val : W → E) ⁻¹' D) xW =
      (Subtype.val : W → E) ⁻¹' connectedComponentIn D x := by
    apply Subset.antisymm
    · intro y hy
      have h := continuous_subtype_val.continuousOn.image_connectedComponentIn_subset
        (show xW ∈ (Subtype.val : W → E) ⁻¹' D from hx)
      have him : (Subtype.val : W → E) '' ((Subtype.val : W → E) ⁻¹' D) = D :=
        image_preimage_eq_of_subset (by simpa only [Subtype.range_val] using hDW)
      rw [him] at h
      exact h (mem_image_of_mem Subtype.val hy)
    · have hpre : IsPreconnected ((Subtype.val : W → E) ⁻¹' connectedComponentIn D x) := by
        apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        rw [image_preimage_eq_of_subset (by
          simpa only [Subtype.range_val] using (connectedComponentIn_subset D x).trans hDW)]
        exact isPreconnected_connectedComponentIn
      exact hpre.subset_connectedComponentIn (mem_connectedComponentIn hx)
        (preimage_mono (connectedComponentIn_subset D x))
  have h := hI.connectedComponentIn hD (show xW ∈ (Subtype.val : W → E) ⁻¹' D from hx)
  rwa [hcc,hT] at h

theorem componentIn_selected_caps
    {X E κ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite κ]
    {P A : Set X} (hP : IsCompact P) (hAP : A ⊆ P)
    {x : X} (hx : x ∈ A) (hcomponent : connectedComponentIn P x = A)
    (S : κ → Set X) (hSP : ∀ i, S i ⊆ P)
    (t : Finset κ) (hselected : ∀ i, (S i ∩ A).Nonempty ↔ i ∈ t)
    (f : X → E) (hf : Continuous f) (hfi : InjOn f P)
    (C : κ → Set E) (hC : ∀ i, IsFinitePLBallPair V3 (C i) (f '' S i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (hcontact : ∀ i, (f '' P) ∩ C i = f '' S i) :
    connectedComponentIn (f '' P ∪ ⋃ i, C i) (f x) = f '' A ∪ ⋃ i : t, C i := by
  classical
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let H : P ≃ₜ f '' P := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f P hfi) (hf.comp continuous_subtype_val |>.subtype_mk _)
  have hcc : connectedComponentIn (f '' P) (f x) = f '' A := by
    rw [←H.image_connectedComponentIn_of_values (fun _ => rfl) subset_rfl (hAP hx),hcomponent]
  rw [componentIn_finite_cap_attachment C (fun i => f '' S i)
    (hP.image hf).isClosed hC hdis hcontact (mem_image_of_mem f (hAP hx)),hcc]
  have hmeet (i : κ) : ((f '' S i) ∩ (f '' A)).Nonempty ↔ i ∈ t := by
    rw [←hselected]
    constructor
    · rintro ⟨z,⟨a,ha,haz⟩,⟨b,hb,hbz⟩⟩
      have hab := hfi (hSP i ha) (hAP hb) (haz.trans hbz.symm)
      exact ⟨a,ha,hab.symm ▸ hb⟩
    · rintro ⟨z,hzS,hzA⟩
      exact ⟨f z,mem_image_of_mem f hzS,mem_image_of_mem f hzA⟩
  congr 1
  ext z
  constructor
  · rintro hz
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion.mpr ⟨⟨i,(hmeet i).mp hi⟩,hzi⟩
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion₂.mpr ⟨i,(hmeet i).mpr i.property,hi⟩

theorem exists_replacement_with_prescribed_caps
    {X E κ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite κ]
    {R P A : Set X} (hA : IsCompact A) (hAP : A ⊆ P)
    (Q S : κ → Set X) (hQ : ∀ i, IsUnitBallPair V3 (Q i) (S i))
    (hdisQ : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hcontactQ : ∀ i, A ∩ Q i = S i) (hcover : A ∪ ⋃ i, Q i = R)
    (f : X → E) (hf : Continuous f) (hfi : InjOn f P)
    (C : κ → Set E) (hC : ∀ i, IsFinitePLBallPair V3 (C i) (f '' S i))
    (hdisC : Pairwise fun i j => Disjoint (C i) (C j))
    (hcontactC : ∀ i, (f '' P) ∩ C i = f '' S i) :
    ∃ G : R ≃ₜ (f '' A ∪ ⋃ i, C i : Set E),
      (∀ (x : X) (hx : x ∈ A),
        (G ⟨x,hcover.subset (Or.inl hx)⟩ : E) = f x) ∧
      (∀ (x : X) (hx : x ∈ A),
        (G.symm ⟨f x,Or.inl (mem_image_of_mem f hx)⟩ : X) = x) ∧
      ∀ i (x : R), (x : X) ∈ Q i ↔ (G x : E) ∈ C i := by
  classical
  have hSA (i : κ) : S i ⊆ A := (hcontactQ i).symm.subset.trans inter_subset_left
  have hcontact (i : κ) : (f '' A) ∩ C i = f '' S i := by
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ (image_mono hAP)).trans (hcontactC i).subset
    · exact subset_inter (image_mono (hSA i)) ((hcontactC i).symm.subset.trans inter_subset_right)
  have hcapTop (i : κ) : IsUnitBallPair V3 (C i) (f '' S i) := by
    obtain ⟨HB,_,hHB⟩ := (hC i).exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
    exact ⟨(hC i).1,HB,by simpa only [frontier_closedBall _ one_ne_zero] using hHB⟩
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let H : A ≃ₜ f '' A := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f A (hfi.mono hAP))
    (hf.comp continuous_subtype_val |>.subtype_mk _)
  have hmark (i : κ) (x : A) : (x : X) ∈ S i ↔ (H x : E) ∈ f '' S i := by
    change (x : X) ∈ S i ↔ f x ∈ f '' S i
    constructor
    · exact mem_image_of_mem f
    · rintro ⟨y,hy,heq⟩
      exact hfi (hAP (hSA i hy)) (hAP x.property) heq ▸ hy
  obtain ⟨G₀,hG₀,_,hGQ⟩ := exists_finite_retained_ball_replacement Q S C
    (fun i => f '' S i) hA.isClosed (hA.image hf).isClosed
    hQ hcapTop hdisQ hdisC hcontactQ hcontact H hmark
  let G : R ≃ₜ (f '' A ∪ ⋃ i, C i : Set E) := (Homeomorph.setCongr hcover.symm).trans G₀
  have hG (x : X) (hx : x ∈ A) : (G ⟨x,hcover.subset (Or.inl hx)⟩ : E) = f x :=
    hG₀ ⟨x,hx⟩
  refine ⟨G,hG,?_,fun i x => hGQ i ((Homeomorph.setCongr hcover.symm) x)⟩
  intro x hx
  have heq : G ⟨x,hcover.subset (Or.inl hx)⟩ =
      ⟨f x,Or.inl (mem_image_of_mem f hx)⟩ := Subtype.ext (hG x hx)
  exact congrArg Subtype.val (G.injective ((G.apply_symm_apply _).trans heq.symm))

end PoincareConjecture.M76
