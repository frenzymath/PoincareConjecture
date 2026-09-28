import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.OuterRetainedDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.ClopenCapSelection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.InteriorReplacement









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.exists_open_retained_model
    {X E α κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3} {R P : Set X}
    (c : MarkedSphereCut e R κ) (hP : IsCompact P) (heP : PLDomain e P)
    (hRP : R ⊆ interior P)
    (heB : PLDomain e (P \ ⋃ i,c.collar i))
    (hBfront : frontier (P \ ⋃ i,c.collar i) = frontier P ∪ ⋃ i,c.ports i)
    (Q : κ × Bool → Set X) (t : Finset (κ × Bool))
    (hQ : ∀ i : t, IsCompact (Q i))
    (hfrontQ : ∀ i : t, frontier (Q i) = c.ports i)
    (hball : ∀ i : t, IsUnitBallPair V3 (Q i) (c.ports i))
    (hinside : ∀ i : t, Q i ⊆ interior R)
    (hdisQ : Pairwise fun i j : t => Disjoint (Q i) (Q j))
    (hinner : (R \ ⋃ i : t, interior (Q i)) ⊆ c.carrier)
    (hselected : ∀ i, (c.ports i ∩ (R \ ⋃ j : t,interior (Q j))).Nonempty ↔ i ∈ t)
    (f : X → E) (hf : Continuous f) (hfi : InjOn f (P \ ⋃ i,c.collar i))
    (C : κ × Bool → Set E) (hC : ∀ i, IsFinitePLBallPair V3 (C i) (f '' c.ports i))
    (hdisC : Pairwise fun i j => Disjoint (C i) (C j))
    (hcontactC : ∀ i, (f '' (P \ ⋃ j,c.collar j)) ∩ C i = f '' c.ports i) :
    let A := P \ ⋃ i : t, interior (Q i)
    let W := (f '' (P \ ⋃ i,c.collar i) ∪ ⋃ i,C i) \ f '' frontier P
    let V := (f '' A ∪ ⋃ i : t,C i) \ f '' frontier P
    V ⊆ W ∧ IsOpen ((Subtype.val : W → E) ⁻¹' V) ∧
      ∃ H : interior P ≃ₜ V,
        (∀ x : interior P, (x : X) ∈ A → (H x : E) = f x) ∧
        ∀ x : interior P, (x : X) ∈ R ↔
          (H x : E) ∈ f '' (R \ ⋃ i : t,interior (Q i)) ∪ ⋃ i : t,C i := by
  classical
  let A := P \ ⋃ i : t, interior (Q i)
  let B := P \ ⋃ i,c.collar i
  let Y := f '' A ∪ ⋃ i : t,C i
  let Z := f '' B ∪ ⋃ i,C i
  let W := Z \ f '' frontier P
  let V := Y \ f '' frontier P
  obtain ⟨hAc,heA,hAf,hfront,hAB,hclopen,hrest,hAR⟩ :=
    c.outer_retained_domain hP heP hRP heB hBfront Q t hQ hfrontQ hball hinside hdisQ hinner
  have hcontactQ (i : t) : A ∩ Q i = c.ports i := by
    rw [←hfrontQ i,(hQ i).isClosed.frontier_eq]
    apply Subset.antisymm
    · rintro x ⟨hxA,hxQ⟩
      exact ⟨hxQ,fun hx => hxA.2 (mem_iUnion.mpr ⟨i,hx⟩)⟩
    · rintro x ⟨hxQ,hxint⟩
      refine ⟨⟨interior_subset (hRP (interior_subset (hinside i hxQ))),?_⟩,hxQ⟩
      intro hx
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact hxint (hij.symm ▸ hxj)
      · exact disjoint_left.mp (hdisQ hij) hxQ (interior_subset hxj)
  have hcover : A ∪ ⋃ i : t,Q i = P := by
    apply Subset.antisymm
    · exact union_subset sdiff_subset
        (iUnion_subset fun i => (hinside i).trans (interior_subset.trans (hRP.trans interior_subset)))
    · intro x hx
      by_cases hh : x ∈ ⋃ i : t,Q i
      · exact Or.inr hh
      · exact Or.inl ⟨hx,fun hi => hh (iUnion_mono (fun _ => interior_subset) hi)⟩
  have hSP (i : κ × Bool) : c.ports i ⊆ B := by
    intro x hx
    have hc := c.port_subset_carrier i hx
    exact ⟨interior_subset (hRP hc.1),hc.2⟩
  have hsel (i : κ × Bool) (hi : i ∈ t) : c.ports i ⊆ A :=
    (hcontactQ ⟨i,hi⟩).symm.subset.trans inter_subset_left
  have homit (i : κ × Bool) (hi : i ∉ t) : Disjoint (c.ports i) A := by
    apply disjoint_left.mpr
    intro x hxS hxA
    exact hi ((hselected i).mp ⟨x,hxS,⟨(c.port_subset_carrier i hxS).1,hxA.2⟩⟩)
  have hclosedRest : IsClosed (f '' B \ f '' A) := by
    have heq := hfi.image_sdiff_subset hAB
    exact heq ▸ (hrest.image hf).isClosed
  have hYclopen : IsClopen ((Subtype.val : Z → E) ⁻¹' Y) :=
    isClopen_finite_cap_selection (hAc.image hf).isClosed hclosedRest (image_mono hAB)
      C (fun i => f '' c.ports i) hC hdisC hcontactC t
      (fun i hi => image_mono (hsel i hi)) (by
        intro i hi
        apply disjoint_left.mpr
        rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
        have hxy := hfi (hSP i hx) (hAB hy) (hxz.trans hyz.symm)
        exact disjoint_left.mp (homit i hi) hx (hxy.symm ▸ hy))
  have hYW : Y ⊆ Z := union_subset_union (image_mono hAB)
    (iUnion_subset fun i => subset_iUnion C (i : κ × Bool))
  have hVW : V ⊆ W := sdiff_subset_sdiff_left hYW
  have hVopen : IsOpen ((Subtype.val : W → E) ⁻¹' V) := by
    have h := hYclopen.isOpen.preimage (continuous_inclusion (show W ⊆ Z from sdiff_subset))
    convert h using 1
    ext x
    exact and_iff_left x.property.2
  obtain ⟨G,hG,_,hGQ⟩ := exists_replacement_with_prescribed_caps hAc hAB
    (fun i : t => Q i) (fun i : t => c.ports i) hball hdisQ hcontactQ hcover f hf hfi
    (fun i : t => C i) (fun i => hC i)
    (fun i j hij => hdisC (Subtype.val_injective.ne hij)) (fun i => hcontactC i)
  obtain ⟨_,H,_,hH,hHR⟩ := exists_interior_retained_replacement
    (show A ⊆ P from sdiff_subset) hfront (fun i : t => Q i) (fun i : t => C i)
    hcover (fun i => (hinside i).trans interior_subset) f G hG hGQ
  refine ⟨hVW,hVopen,H,hH,?_⟩
  change A ∩ R = R \ ⋃ i : t,interior (Q i) at hAR
  simpa only [hAR] using hHR

end PoincareConjecture.M76
