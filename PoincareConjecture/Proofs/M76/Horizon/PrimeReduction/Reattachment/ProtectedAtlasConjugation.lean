import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.PulledBackAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainComposition

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

variable {X ι κ : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3}
  {a : κ → OpenPartialHomeomorph X V3} {R N D : Set X}

theorem ChartwisePLOn.identity_pullback_homeomorph
    (h : ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' N))
    (F : X ≃ₜ X) (hFR : F '' R = R) (hN : IsOpen N) :
    ChartwisePLOn (fun i => F.transOpenPartialHomeomorph (e i))
      (fun j => F.transOpenPartialHomeomorph (a j))
      (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' (F ⁻¹' N)) := by
  have hpre : F ⁻¹' R = R := by
    rw [← hFR, F.injective.preimage_image]
    exact hFR.symm
  let q : R ≃ₜ R := F.subtype (fun x => by
    change x ∈ R ↔ x ∈ F ⁻¹' R
    rw [hpre])
  refine ⟨?_, ?_, (hN.preimage F.continuous).preimage continuous_subtype_val, ?_⟩
  · simpa only [hpre] using h.source_domain.preimage_homeomorph F
  · simpa only [hpre] using h.target_domain.preimage_homeomorph F
  intro x hx
  obtain ⟨i,j,K,V,G,hK,hV,hxV,hVU,hVe,hVK,hKt,hKU,hG,hcoords⟩ :=
    h.coordinates (q x) hx
  refine ⟨i,j,K,q ⁻¹' V,G,hK,hV.preimage q.continuous,hxV,?_,?_,?_,hKt,?_,hG,?_⟩
  · intro y hy
    exact hVU hy
  · intro y hy
    exact hVe hy
  · rintro z ⟨y,hy,rfl⟩
    exact hVK ⟨q y,hy,rfl⟩
  · intro z hz
    obtain ⟨y,hyN,hy⟩ := hKU hz
    refine ⟨q.symm y,?_,?_⟩
    · change F (F.symm (y : X)) ∈ N
      rw [F.apply_symm_apply]
      exact hyN
    · change F.symm (y : X) = F.symm ((e i).symm z)
      rw [hy]
  · intro y hy hyK
    exact hcoords (q y) hy hyK

theorem protected_atlas_conjugation
    (he : PLDomain e R) (hI : IsPLIrreducible a R)
    (hN : IsOpen N) (hfront : frontier R ⊆ N)
    (hforward : ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' N))
    (hreverse : ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' N))
    (F : X ≃ₜ X) (hFR : F '' R = R)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hFD : F '' D ⊆ N) :
    let b := fun j => F.transOpenPartialHomeomorph (a j)
    IsOpen (F ⁻¹' N) ∧ D ∪ frontier R ⊆ F ⁻¹' N ∧ IsPLIrreducible b R ∧
      ChartwisePLOn e b (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' (F ⁻¹' N)) ∧
      ChartwisePLOn b e (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' (F ⁻¹' N)) := by
  have hpre : F ⁻¹' R = R := by
    rw [← hFR, F.injective.preimage_image]
    exact hFR.symm
  let ep := fun i => F.transOpenPartialHomeomorph (e i)
  have hep : PLDomain ep R := by
    simpa only [hpre] using he.preimage_homeomorph F
  have hrestr (i : ι) : (e i).restrOpen univ isOpen_univ = e i := by
    apply OpenPartialHomeomorph.ext
    · intro x; rfl
    · intro x; rfl
    · exact inter_univ _
  have ht : ∀ i j, ((e i).restrOpen univ isOpen_univ).symm.trans (ep j) ∈
      piecewiseAffineGroupoid V3 := by
    intro i j
    rw [hrestr]
    simpa only [ep, Homeomorph.transOpenPartialHomeomorph_eq_trans] using hF i j
  obtain ⟨hff,hfr⟩ := chartwisePLOn_identity_domain_both_of_restricted_transitions
    e ep he hep isOpen_univ ht
  have hp := hforward.identity_pullback_homeomorph F hFR hN
  have hq := hreverse.identity_pullback_homeomorph F hFR hN
  refine ⟨hN.preimage F.continuous,?_,?_,?_,?_⟩
  · rintro x (hx | hx)
    · exact hFD (mem_image_of_mem F hx)
    · apply hfront
      have := mem_image_of_mem F hx
      rwa [F.image_frontier, hFR] at this
  · simpa only [hpre] using hI.preimage_homeomorph F
  · simpa only [ContinuousMap.id_comp, ContinuousMap.coe_id, preimage_id,
      preimage_univ, univ_inter] using hp.comp hff
  · simpa only [ContinuousMap.id_comp, ContinuousMap.coe_id, preimage_id,
      preimage_univ, inter_univ] using hfr.comp hq

end PoincareConjecture.M76
