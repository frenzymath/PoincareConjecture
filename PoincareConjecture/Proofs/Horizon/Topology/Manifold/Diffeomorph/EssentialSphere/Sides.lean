import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Connected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sets.Opens

set_option autoImplicit false

open Set TopologicalSpace

namespace Poincare.Topology

theorem cylinder_sides_of_negative_witness
    {S M : Type*} [TopologicalSpace S] [ConnectedSpace S] [TopologicalSpace M]
    (U : Opens M) (F : (S × ℝ) ≃ₜ U) {A B : Set M}
    (hA : IsOpen A) (hB : IsOpen B) (hcA : IsPreconnected A)
    (hdis : Disjoint A B)
    (hcover : A ∪ B = (U : Set M) \ range (fun q : S => (F (q, 0) : M)))
    {p₀ : S × ℝ} (hp₀ : p₀.2 < 0) (hseed : (F p₀ : M) ∈ A) :
    (∀ p : S × ℝ, (F p : M) ∈ A ↔ p.2 < 0) ∧
      ∀ p : S × ℝ, (F p : M) ∈ B ↔ 0 < p.2 := by
  let f : S × ℝ → M := fun p => F p
  have hf : Continuous f := continuous_subtype_val.comp F.continuous
  have hfinj : Function.Injective f := Subtype.val_injective.comp F.injective
  have hfopen : IsOpenMap f := U.isOpen.isOpenMap_subtype_val.comp F.isOpenMap
  have hAU : A ⊆ range f := by
    intro x hx
    have hxU : x ∈ U := (hcover.le (Or.inl hx)).1
    obtain ⟨p, hp⟩ := F.surjective ⟨x, hxU⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  have hzero (p : S × ℝ) : f p ∈ range (fun q : S => (F (q, 0) : M)) ↔ p.2 = 0 := by
    constructor
    · rintro ⟨q, hq⟩
      exact (congrArg Prod.snd (hfinj hq)).symm
    · intro hp
      exact ⟨p.1, congrArg f (Prod.ext rfl hp.symm)⟩
  have hmem (p : S × ℝ) : (f p ∈ A ∨ f p ∈ B) ↔ p.2 ≠ 0 := by
    change f p ∈ A ∪ B ↔ _
    rw [hcover, mem_sdiff, hzero]
    exact and_iff_right (F p).property
  let L : Set (S × ℝ) := {p | p.2 < 0}
  let R : Set (S × ℝ) := {p | 0 < p.2}
  have hL : IsOpen L := isOpen_lt continuous_snd continuous_const
  have hR : IsOpen R := isOpen_lt continuous_const continuous_snd
  have hLR : Disjoint L R := disjoint_left.mpr fun p hl hr =>
    lt_asymm (show p.2 < 0 from hl) (show 0 < p.2 from hr)
  have hcL : IsPreconnected L := by
    have heq : L = (univ : Set S) ×ˢ Iio (0 : ℝ) := by ext p; simp [L]
    rw [heq]
    exact isPreconnected_univ.prod isPreconnected_Iio
  have hsubA : f ⁻¹' A ⊆ L ∪ R := by
    intro p hp
    exact lt_or_gt_of_ne ((hmem p).mp (Or.inl hp))
  have hsubL : L ⊆ f ⁻¹' A ∪ f ⁻¹' B := by
    intro p hp
    exact (hmem p).mpr (ne_of_lt hp)
  have hAL : f ⁻¹' A ⊆ L := by
    rcases (hcA.preimage_of_isOpenMap hfinj hfopen hAU).subset_or_subset
        hL hR hLR hsubA with h | h
    · exact h
    · exact (lt_asymm hp₀ (h hseed)).elim
  have hLA : L ⊆ f ⁻¹' A := by
    rcases hcL.subset_or_subset (hA.preimage hf) (hB.preimage hf)
        (hdis.preimage f) hsubL with h | h
    · exact h
    · exact (disjoint_left.mp hdis hseed (h hp₀)).elim
  have hleft (p : S × ℝ) : f p ∈ A ↔ p.2 < 0 := ⟨fun hp => hAL hp, fun hp => hLA hp⟩
  refine ⟨hleft, fun p => ?_⟩
  constructor
  · intro hp
    have hn := (hmem p).mp (Or.inr hp)
    rcases lt_or_gt_of_ne hn with h | h
    · exact (disjoint_left.mp hdis ((hleft p).mpr h) hp).elim
    · exact h
  · intro hp
    exact ((hmem p).mpr hp.ne').resolve_left fun ha => lt_asymm ((hleft p).mp ha) hp

end Poincare.Topology
