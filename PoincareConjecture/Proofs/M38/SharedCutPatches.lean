import PoincareConjecture.Proofs.M38.SuccessiveCutDomains









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S R : Set (Fin (F.event T hT).cap_count)) (hSR : S ⊆ R)


abbrev SharedCutIndex := eventCutOpen F T hT P R ⊕ (S × Bool)


def sharedCutIndex : SharedCutIndex F T hT P S R → PartialCappingIndex F T hT P R
  | .inl y => .inl y
  | .inr a => .inr (successiveCapIndex F T hT S R hSR a)


noncomputable def sharedCutDomain (j : SharedCutIndex F T hT P S R) :
    TopologicalSpace.Opens StandardCapSpace :=
  partialCappingDomain F T hT P R (sharedCutIndex F T hT P S R hSR j)


noncomputable def sharedCutInclude (j : SharedCutIndex F T hT P S R) :
    sharedCutDomain F T hT P S R hSR j → PartialCappedSpace F T hT P R :=
  partialCappingInclude F T hT P R (sharedCutIndex F T hT P S R hSR j)


noncomputable def sharedCutPatch (j : SharedCutIndex F T hT P S R) :
    sharedCutDomain F T hT P S R hSR j → PartialCappedSpace F T hT P S :=
  match j with
  | .inl y => partialOldInclusion F T hT P S ∘ successiveOldInclusion F T hT P S R hSR ∘
      partialCappingMap F T hT P R (.inl y)
  | .inr a => partialCappingInclude F T hT P S (.inr a)


theorem sharedCutInclude_openEmbedding (j : SharedCutIndex F T hT P S R) :
    IsOpenEmbedding (sharedCutInclude F T hT P S R hSR j) :=
  partialCappingInclude_openEmbedding F T hT P R (sharedCutIndex F T hT P S R hSR j)


theorem sharedCutPatch_openEmbedding (j : SharedCutIndex F T hT P S R) :
    IsOpenEmbedding (sharedCutPatch F T hT P S R hSR j) := by
  cases j with
  | inl y =>
      exact (partialOldInclusion_openEmbedding F T hT P S).comp
        ((successiveOldInclusion_openEmbedding F T hT P S R hSR).comp
          (partialCappingMap_old_openEmbedding F T hT P R y))
  | inr a => exact partialCappingInclude_openEmbedding F T hT P S (.inr a)


theorem sharedCut_old_cap_iff (y : eventCutOpen F T hT P R) (a : S × Bool)
    (x : capDoubleBall) :
    partialOldInclusion F T hT P S (successiveOldInclusion F T hT P S R hSR y) =
        partialCappingInclude F T hT P S (.inr a) x ↔
      partialOldInclusion F T hT P R y = partialCappingInclude F T hT P R
        (.inr (successiveCapIndex F T hT S R hSR a)) x := by
  rw [partialOldInclusion_eq_cap_iff, partialOldInclusion_eq_cap_iff]
  apply and_congr_right
  intro hx
  rw [← successive_attachment F T hT P S R hSR a x hx]
  exact (successiveOldInclusion_openEmbedding F T hT P S R hSR).injective.eq_iff


theorem sharedCutPatch_eq_iff (j k : SharedCutIndex F T hT P S R)
    (x : sharedCutDomain F T hT P S R hSR j) (y : sharedCutDomain F T hT P S R hSR k) :
    sharedCutPatch F T hT P S R hSR j x = sharedCutPatch F T hT P S R hSR k y ↔
      sharedCutInclude F T hT P S R hSR j x = sharedCutInclude F T hT P S R hSR k y := by
  cases j with
  | inl a =>
      cases k with
      | inl b =>
          change partialOldInclusion F T hT P S
              (successiveOldInclusion F T hT P S R hSR (partialCappingMap F T hT P R (.inl a) x)) =
            partialOldInclusion F T hT P S
              (successiveOldInclusion F T hT P S R hSR (partialCappingMap F T hT P R (.inl b) y)) ↔
            partialCappingInclude F T hT P R (.inl a) x =
              partialCappingInclude F T hT P R (.inl b) y
          rw [← partialOldInclusion_patch, ← partialOldInclusion_patch]
          exact (partialOldInclusion_openEmbedding F T hT P S).injective.eq_iff.trans
            ((successiveOldInclusion_openEmbedding F T hT P S R hSR).injective.eq_iff.trans
              (partialOldInclusion_openEmbedding F T hT P R).injective.eq_iff.symm)
      | inr b =>
          change partialOldInclusion F T hT P S
              (successiveOldInclusion F T hT P S R hSR (partialCappingMap F T hT P R (.inl a) x)) =
            partialCappingInclude F T hT P S (.inr b) y ↔
            partialCappingInclude F T hT P R (.inl a) x =
              partialCappingInclude F T hT P R (.inr (successiveCapIndex F T hT S R hSR b)) y
          rw [← partialOldInclusion_patch]
          exact sharedCut_old_cap_iff F T hT P S R hSR _ b y
  | inr a =>
      cases k with
      | inl b =>
          change partialCappingInclude F T hT P S (.inr a) x =
            partialOldInclusion F T hT P S
              (successiveOldInclusion F T hT P S R hSR (partialCappingMap F T hT P R (.inl b) y)) ↔
            partialCappingInclude F T hT P R (.inr (successiveCapIndex F T hT S R hSR a)) x =
              partialCappingInclude F T hT P R (.inl b) y
          rw [← partialOldInclusion_patch]
          exact (eq_comm.trans (sharedCut_old_cap_iff F T hT P S R hSR _ a x)).trans eq_comm
      | inr b =>
          by_cases hab : a = b
          · subst b
            exact (sharedCutPatch_openEmbedding F T hT P S R hSR (.inr a)).injective.eq_iff.trans
              (sharedCutInclude_openEmbedding F T hT P S R hSR (.inr a)).injective.eq_iff.symm
          · constructor
            · intro h
              exact (Set.disjoint_left.mp (partialCapPatch_disjoint F T hT P S a b hab)
                (Set.mem_range_self x) ⟨y, h.symm⟩).elim
            · intro h
              exact (Set.disjoint_left.mp (partialCapPatch_disjoint F T hT P R
                (successiveCapIndex F T hT S R hSR a) (successiveCapIndex F T hT S R hSR b)
                (fun he => hab (successiveCapIndex_injective F T hT S R hSR he)))
                  (Set.mem_range_self x) ⟨y, h.symm⟩).elim

end PoincareConjecture.M38
