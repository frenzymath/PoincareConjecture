import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff





set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture






theorem m64_isCompact_distinct_lift_fibers
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space Z]
    {S : Set X} {T : Set Y} (hS : IsCompact S) (hT : IsCompact T)
    {f : Y → Z} {c : X → Z} {g : X → Y}
    (hf : ContinuousOn f T) (hc : ContinuousOn c S) (hg : ContinuousOn g S)
    (hlift : ∀ x ∈ S, f (g x) = c x)
    (hlocal : ∀ x ∈ S, ∃ W ∈ 𝓝 (g x), InjOn f W) :
    IsCompact {p : X × Y | p.1 ∈ S ∧ p.2 ∈ T ∧ f p.2 = c p.1 ∧ p.2 ≠ g p.1} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let C : Set (S × T) := {p | f p.2 = c p.1 ∧ (p.2 : Y) ≠ g p.1}
  have hfc : Continuous (fun p : S × T => f p.2) :=
    hf.domRestrict.comp continuous_snd
  have hcc : Continuous (fun p : S × T => c p.1) :=
    hc.domRestrict.comp continuous_fst
  have hgc : Continuous (fun p : S × T => g p.1) :=
    hg.domRestrict.comp continuous_fst
  have hclosed : IsClosed C := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p hp
    change ¬ (f p.2 = c p.1 ∧ (p.2 : Y) ≠ g p.1) at hp
    by_cases he : f p.2 = c p.1
    · have heq : (p.2 : Y) = g p.1 := by tauto
      obtain ⟨W, hW, hi⟩ := hlocal p.1 p.1.property
      have hgW : ∀ᶠ q : S × T in 𝓝 p, g q.1 ∈ W := hgc.continuousAt hW
      have hyW : ∀ᶠ q : S × T in 𝓝 p, (q.2 : Y) ∈ W :=
        (continuous_subtype_val.comp continuous_snd).continuousAt (by
          change W ∈ 𝓝 (p.2 : Y)
          rwa [heq])
      filter_upwards [hgW, hyW] with q hqg hqy
      change ¬ (f q.2 = c q.1 ∧ (q.2 : Y) ≠ g q.1)
      rintro ⟨hqe, hqn⟩
      exact hqn (hi hqy hqg (hqe.trans (hlift q.1 q.1.property).symm))
    · filter_upwards [(isOpen_ne_fun hfc hcc).mem_nhds he] with q hq
      exact fun h => hq h.1
  have himage : (fun p : S × T => ((p.1 : X), (p.2 : Y))) '' C =
      {p : X × Y | p.1 ∈ S ∧ p.2 ∈ T ∧ f p.2 = c p.1 ∧ p.2 ≠ g p.1} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.property, q.2.property, hq⟩
    · rintro ⟨hpS, hpT, hp⟩
      exact ⟨(⟨p.1, hpS⟩, ⟨p.2, hpT⟩), hp, rfl⟩
  rw [← himage]
  exact hclosed.isCompact.image
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

end PoincareConjecture
