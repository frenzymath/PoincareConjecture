import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointMidpointGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberEndpointPairs



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem prismFiberEndPair_midpoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberEndPair H (prismFiberMidpoint H x) = prismFiberEndPair H x := by
  simp only [prismFiberEndPair,prismFiberPoint_midpoint]

theorem prismFiberEndPair_endpoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : A) (b : Bool) :
    prismFiberEndPair H (prismEndMap H x b) =
      {(prismEndMap H x b : E),(prismEndMap H x (!b) : E)} := by
  simp only [prismFiberEndPair,prismFiberPoint,prismEndMap,H.symm_apply_apply]
  cases b
  · rfl
  · exact pair_comm _ _

theorem prism_endpoint_midpoint_eq_iff
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (J : (⋃ i, B i) ≃ₜ (⋃ i, B i)) (m : C((⋃ i, B i), (⋃ i, B i)))
    (hm : ∀ i (x : B i), (m ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : E) =
      prismFiberMidpoint (H i) x)
    (hmJ : ∀ x, m (J x) = m x)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x,hi⟩ = prismFiberEndPair (H j) ⟨x,hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτval : ∀ x, (τ x : E) = J (prismEndpointInclusion H x))
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (p q : (⋃ i, prismEnds (H i) : Set E)) :
    m (prismEndpointInclusion H p) = m (prismEndpointInclusion H q) ↔ p = q ∨ p = τ q := by
  constructor
  · intro hpq
    obtain ⟨i,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
    obtain ⟨j,⟨⟨c,d⟩,hq⟩⟩ := mem_iUnion.mp q.property
    have hp' : p = prismEndpointLift H i a b := Subtype.ext hp.symm
    have hq' : q = prismEndpointLift H j c d := Subtype.ext hq.symm
    rw [hp',hq'] at hpq ⊢
    have hmid : (prismFiberMidpoint (H i) (prismEndMap (H i) a b) : E) =
        prismFiberMidpoint (H j) (prismEndMap (H j) c d) :=
      (hm i (prismEndMap (H i) a b)).symm.trans
        ((congrArg Subtype.val hpq).trans (hm j (prismEndMap (H j) c d)))
    have hmem : (prismFiberMidpoint (H i) (prismEndMap (H i) a b) : E) ∈ B j :=
      hmid ▸ (prismFiberMidpoint (H j) (prismEndMap (H j) c d)).property
    have hsame : (⟨prismFiberMidpoint (H i) (prismEndMap (H i) a b),hmem⟩ : B j) =
        prismFiberMidpoint (H j) (prismEndMap (H j) c d) := Subtype.ext hmid
    have he := hpair i j (prismFiberMidpoint (H i) (prismEndMap (H i) a b))
      (prismFiberMidpoint (H i) (prismEndMap (H i) a b)).property hmem
    rw [hsame,prismFiberEndPair_midpoint,prismFiberEndPair_midpoint,
      prismFiberEndPair_endpoint,prismFiberEndPair_endpoint] at he
    have hh : (prismEndMap (H i) a b : E) ∈
        {(prismEndMap (H j) c d : E),(prismEndMap (H j) c (!d) : E)} :=
      he.subset (mem_insert _ _)
    rcases mem_insert_iff.mp hh with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext ((mem_singleton_iff.mp h).trans (hτends j c d).symm))
  · rintro (rfl | rfl)
    · rfl
    · have he : prismEndpointInclusion H (τ q) = J (prismEndpointInclusion H q) :=
        Subtype.ext (hτval q)
      rw [he,hmJ]

end PoincareConjecture.M76.PrismBelt
