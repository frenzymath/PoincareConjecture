import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiberMap



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem prismEndpointFiberMap_same_or_flip
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x,hi⟩ = prismFiberEndPair (H j) ⟨x,hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (p q : (⋃ i, prismEnds (H i) : Set E)) (t s : I)
    (heq : prismEndpointFiberMap H L (p,t) = prismEndpointFiberMap H L (q,s)) : p = q ∨ p = τ q := by
  obtain ⟨i,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
  obtain ⟨j,⟨⟨c,d⟩,hq⟩⟩ := mem_iUnion.mp q.property
  have hp' : p = prismEndpointLift H i a b := Subtype.ext hp.symm
  have hq' : q = prismEndpointLift H j c d := Subtype.ext hq.symm
  rw [hp',hq'] at heq ⊢
  have hpoint : (prismFiberInterpolation (H i) (prismEndMap (H i) a b) t : E) =
      prismFiberInterpolation (H j) (prismEndMap (H j) c d) s :=
    (hL i (prismEndMap (H i) a b) t).symm.trans
      ((congrArg Subtype.val heq).trans (hL j (prismEndMap (H j) c d) s))
  have hmem : (prismFiberInterpolation (H i) (prismEndMap (H i) a b) t : E) ∈ B j :=
    hpoint ▸ (prismFiberInterpolation (H j) (prismEndMap (H j) c d) s).property
  have hsame : (⟨prismFiberInterpolation (H i) (prismEndMap (H i) a b) t,hmem⟩ : B j) =
      prismFiberInterpolation (H j) (prismEndMap (H j) c d) s := Subtype.ext hpoint
  have he := hpair i j (prismFiberInterpolation (H i) (prismEndMap (H i) a b) t)
    (prismFiberInterpolation (H i) (prismEndMap (H i) a b) t).property hmem
  rw [hsame,prismFiberEndPair_interpolation,prismFiberEndPair_interpolation,
    prismFiberEndPair_endpoint,prismFiberEndPair_endpoint] at he
  have hh : (prismEndMap (H i) a b : E) ∈
      {(prismEndMap (H j) c d : E),(prismEndMap (H j) c (!d) : E)} := he.subset (mem_insert _ _)
  rcases mem_insert_iff.mp hh with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext ((mem_singleton_iff.mp h).trans (hτends j c d).symm))

theorem prismEndpointFiberMap_eq_iff
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x,hi⟩ = prismFiberEndPair (H j) ⟨x,hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (z w : (⋃ i, prismEnds (H i) : Set E) × I) :
    prismEndpointFiberMap H L z = prismEndpointFiberMap H L w ↔
      z = w ∨ z = TwistedInvolutionInterval.deck τ w := by
  rcases z with ⟨p,t⟩
  rcases w with ⟨q,s⟩
  constructor
  · intro h
    rcases prismEndpointFiberMap_same_or_flip H L hL hpair τ hτends p q t s h with hp | hp
    · subst p
      exact Or.inl (Prod.ext rfl (prismEndpointFiberMap_fiber_injective H L hL q h))
    · subst p
      have ht : unitInterval.symm t = s := prismEndpointFiberMap_fiber_injective H L hL q
        ((prismEndpointFiberMap_flip H L hL τ hτends q t).symm.trans h)
      have ht' : t = unitInterval.symm s := by
        simpa only [unitInterval.symm_symm] using congrArg unitInterval.symm ht
      exact Or.inr (Prod.ext rfl ht')
  · rintro (h | h)
    · exact congrArg (prismEndpointFiberMap H L) h
    · rw [h]
      change prismEndpointFiberMap H L (τ q,unitInterval.symm s) = _
      rw [prismEndpointFiberMap_flip H L hL τ hτends,unitInterval.symm_symm]

theorem exists_twisted_interval_homeomorph_of_prism_interpolation
    {E ι : Type*} [TopologicalSpace E] [T2Space E] [Finite ι]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (hA : ∀ i, IsCompact (A i))
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x,hi⟩ = prismFiberEndPair (H j) ⟨x,hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i))) (hτ : Function.Involutive τ)
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b)) :
    ∃ W : TwistedInvolutionInterval.Model τ hτ ≃ₜ (⋃ i, B i : Set E),
      (∀ z, W (TwistedInvolutionInterval.projection τ hτ z) = prismEndpointFiberMap H L z) ∧
      (∀ p, W (TwistedInvolutionInterval.boundaryMap τ hτ p) = prismEndpointInclusion H p) := by
  classical
  let Ends := (⋃ i, prismEnds (H i) : Set E)
  let : CompactSpace Ends := isCompact_iff_compactSpace.mp
    (isCompact_iUnion (fun i => isCompact_prismEnds (H i) (hA i)))
  let f := prismEndpointFiberMap H L
  have hrespect : ∀ z w : Ends × I,
      (FreeInvolutionQuotient.orbitSetoid (TwistedInvolutionInterval.deck τ)
        (TwistedInvolutionInterval.deck_involutive τ hτ)).r z w → f z = f w := by
    intro z w h
    exact (prismEndpointFiberMap_eq_iff H L hL hpair τ hτends z w).mpr h
  let φ : TwistedInvolutionInterval.Model τ hτ → (⋃ i, B i : Set E) := Quotient.lift f hrespect
  have hφ : Continuous φ := f.continuous.quotient_lift hrespect
  have hinj : Function.Injective φ := by
    intro z w hzw
    obtain ⟨z,rfl⟩ := Quotient.mk_surjective z
    obtain ⟨w,rfl⟩ := Quotient.mk_surjective w
    exact Quotient.sound ((prismEndpointFiberMap_eq_iff H L hL hpair τ hτends z w).mp hzw)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨z,hz⟩ := prismEndpointFiberMap_surjective H L hL x
    exact ⟨TwistedInvolutionInterval.projection τ hτ z,hz⟩
  let W := (Equiv.ofBijective φ ⟨hinj,hsurj⟩).toHomeomorphOfContinuousClosed hφ hφ.isClosedMap
  refine ⟨W,fun _ => rfl,?_⟩
  intro p
  obtain ⟨i,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
  have hp' : p = prismEndpointLift H i a b := Subtype.ext hp.symm
  rw [hp']
  apply Subtype.ext
  exact (hL i (prismEndMap (H i) a b) 0).trans
    (congrArg Subtype.val (prismFiberInterpolation_zero (H i) (prismEndMap (H i) a b)))

end PoincareConjecture.M76.PrismBelt
