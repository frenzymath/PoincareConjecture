import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.OldWordNormalSubgroup

/-!
# Selection in one finite double-arc surgery

The local chart construction supplies two normalized resolution candidates
for one proper double arc.  This file keeps their concrete source/rim,
properness, mark, homotopy, and finite-decrease fields together and proves
the exact normal-subgroup selection used by the tower descent.  It does not
construct a crossing decomposition or a disk surgery supplier.  See Dehn
derivations 034 and 036.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set

namespace PoincareMT.M76.Dehn

universe u v w

/-- The common finite data retained by the two local resolution candidates.
The `normality` field is the actual normal-subgroup hypothesis for the
marked stage, while the sets and counts expose the whole-source and finite
decrease obligations read by the later descent. -/
structure DoubleArcContext (X : Type u) (Y : Type v) (G : Type w)
    [Group G] where
  normal : Subgroup G
  normality : normal.Normal
  source : Set X
  boundary : Set X
  region : Set Y
  frontier : Set Y
  mark : Set Y
  oldArcCount : Nat
  oldCircleCount : Nat
  oldWord : G
  alpha : G
  beta : G
  gamma : G
  delta : G
  old_outside : oldWord ∉ normal
  old_word : oldWord = alpha * beta * gamma * delta

/-- One normalized local resolution produced by the cut-and-glue chart
construction.  The map and rim are concrete functions; all relative
properness, marking, endpoint-trace, and finite-decrease facts are retained
as fields instead of being hidden in a named Dehn predicate. -/
structure DoubleArcCandidate {X : Type u} {Y : Type v} {G : Type w}
    [Group G] (C : DoubleArcContext X Y G) where
  map : X → Y
  rim : X → Y
  word : G
  image_mem : ∀ x, x ∈ C.source → map x ∈ C.region
  proper : ∀ x, x ∈ C.source → (map x ∈ C.frontier ↔ x ∈ C.boundary)
  rim_eq : ∀ x, x ∈ C.boundary → map x = rim x
  rim_mark : ∀ x, x ∈ C.boundary → rim x ∈ C.mark
  endpoint_homotopy : Prop
  marked_path_update : Prop
  arcCount : Nat
  circleCount : Nat
  arcs_decrease : arcCount < C.oldArcCount
  circles_no_increase : circleCount ≤ C.oldCircleCount
  no_new_triples : Prop
  unchanged_off_tube : Prop

/-- The first section-11 pairing family, including the exact two converted
rim words from one endpoint preimage. -/
structure CaseAResolutionFamily {X : Type u} {Y : Type v} {G : Type w}
    [Group G] (C : DoubleArcContext X Y G) where
  first : DoubleArcCandidate C
  second : DoubleArcCandidate C
  first_word : first.word = C.alpha * C.gamma
  second_word : second.word = C.alpha * C.beta⁻¹ * C.gamma * C.delta⁻¹

/-- The second section-11 pairing family, including the exact two converted
rim words from one endpoint preimage. -/
structure CaseBResolutionFamily {X : Type u} {Y : Type v} {G : Type w}
    [Group G] (C : DoubleArcContext X Y G) where
  first : DoubleArcCandidate C
  second : DoubleArcCandidate C
  first_word : first.word = C.alpha * C.gamma⁻¹
  second_word : second.word = C.alpha * C.delta * C.gamma * C.beta

/-- Select the case-(a) resolution whose marked rim stays outside the stage
normal subgroup.  The selected value is literally one of the two supplied
candidate records, so all source/rim, properness, homotopy, and decrease
fields are preserved by projection. -/
theorem exists_selected_case_a_resolution
    {X : Type u} {Y : Type v} {G : Type w} [Group G]
    (C : DoubleArcContext X Y G) (F : CaseAResolutionFamily C) :
    ∃ c : DoubleArcCandidate C,
      (c = F.first ∨ c = F.second) ∧ c.word ∉ C.normal := by
  letI : C.normal.Normal := C.normality
  have hold : C.alpha * C.beta * C.gamma * C.delta ∉ C.normal := by
    intro h
    apply C.old_outside
    rw [C.old_word]
    exact h
  by_cases hfirst : F.first.word ∈ C.normal
  · have hsecond : F.second.word ∉ C.normal := by
      intro hsecond
      apply hold
      apply old_word_mem_of_case_a C.normal
      · exact F.first_word ▸ hfirst
      · exact F.second_word ▸ hsecond
    exact ⟨F.second, Or.inr rfl, hsecond⟩
  · exact ⟨F.first, Or.inl rfl, hfirst⟩

/-- Select the case-(b) resolution whose marked rim stays outside the stage
normal subgroup.  As in case (a), the output is one of the supplied concrete
candidate records and carries every local geometric field unchanged. -/
theorem exists_selected_case_b_resolution
    {X : Type u} {Y : Type v} {G : Type w} [Group G]
    (C : DoubleArcContext X Y G) (F : CaseBResolutionFamily C) :
    ∃ c : DoubleArcCandidate C,
      (c = F.first ∨ c = F.second) ∧ c.word ∉ C.normal := by
  letI : C.normal.Normal := C.normality
  have hold : C.alpha * C.beta * C.gamma * C.delta ∉ C.normal := by
    intro h
    apply C.old_outside
    rw [C.old_word]
    exact h
  by_cases hfirst : F.first.word ∈ C.normal
  · have hsecond : F.second.word ∉ C.normal := by
      intro hsecond
      apply hold
      apply old_word_mem_of_case_b C.normal
      · exact F.first_word ▸ hfirst
      · exact F.second_word ▸ hsecond
    exact ⟨F.second, Or.inr rfl, hsecond⟩
  · exact ⟨F.first, Or.inl rfl, hfirst⟩

end PoincareMT.M76.Dehn
