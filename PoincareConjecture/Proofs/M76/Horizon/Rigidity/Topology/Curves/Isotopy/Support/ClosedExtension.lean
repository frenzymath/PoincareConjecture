import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension
import Mathlib.Topology.Homeomorph.Lemmas



set_option autoImplicit false
open Set Topology

namespace Homeomorph

variable {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
  {S : Set X}

theorem continuous_closedExtension_family
    (F : T → S ≃ₜ S) (hS : IsClosed S)
    (hF : Continuous (fun z : T × S => F z.1 z.2))
    (hfix : ∀ t (x : S), (x : X) ∈ frontier S → F t x = x) :
    Continuous (fun z : T × X => (F z.1).closedExtension hS (hfix z.1) z.2) := by
  let G := fun z : T × X => (F z.1).closedExtension hS (hfix z.1) z.2
  have hinside : ContinuousOn G (Prod.snd ⁻¹' S) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let a : (Prod.snd ⁻¹' S : Set (T × X)) → T × S :=
      fun z => (z.1.1, ⟨z.1.2, z.property⟩)
    have ha : Continuous a := by fun_prop
    convert continuous_subtype_val.comp (hF.comp ha) using 1
    ext z
    exact (F z.1.1).closedExtension_apply_mem hS (hfix z.1.1) z.property
  have houtside : EqOn G Prod.snd (Prod.snd ⁻¹' closure Sᶜ) := by
    intro z hz
    by_cases hx : z.2 ∈ S
    · exact (F z.1).closedExtension_apply_frontier hS (hfix z.1)
        (by rw [frontier_eq_closure_inter_closure]; exact ⟨subset_closure hx, hz⟩)
    · exact (F z.1).closedExtension_apply_notMem hS (hfix z.1) hx
  have hcover : (Prod.snd ⁻¹' S : Set (T × X)) ∪
      Prod.snd ⁻¹' closure Sᶜ = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z.2 ∈ S
    · exact Or.inl hz
    · exact Or.inr (subset_closure hz)
  have h := hinside.union_of_isClosed
    (continuous_snd.continuousOn.congr houtside)
    (hS.preimage continuous_snd) (isClosed_closure.preimage continuous_snd)
  rw [hcover] at h
  exact continuousOn_univ.mp h

theorem continuous_closedExtension_family_symm
    (F : T → S ≃ₜ S) (hS : IsClosed S)
    (hF : Continuous (fun z : T × S => (F z.1).symm z.2))
    (hfix : ∀ t (x : S), (x : X) ∈ frontier S → F t x = x) :
    Continuous (fun z : T × X => ((F z.1).closedExtension hS (hfix z.1)).symm z.2) := by
  have hfixInv (t : T) (x : S) (hx : (x : X) ∈ frontier S) : (F t).symm x = x := by
    apply (F t).injective
    rw [(F t).apply_symm_apply, hfix t x hx]
  exact continuous_closedExtension_family (fun t => (F t).symm) hS hF hfixInv

end Homeomorph
