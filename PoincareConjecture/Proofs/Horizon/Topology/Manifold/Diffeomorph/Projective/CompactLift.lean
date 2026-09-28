import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.Covering









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.StandardPuncturedProjectiveCover

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  {p : RealProjectiveThree} {U : Set M}
  (S : StandardPuncturedProjectiveCover M p U)


theorem compact_lift_topology {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    (hregular : closure (interior K) = K) :
    let L := {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ K}
    IsCompact L ∧ S.cover '' L = K ∧
      interior L = {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ interior K} ∧
      frontier L = {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ frontier K} ∧
      closure (interior L) = L ∧
      ∀ q : UnitThreeSphere, -q ∈ L ↔ q ∈ L := by
  let L := {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ K}
  have hL : IsCompact L := S.isCompact_lift hK hKU
  have himage : S.cover '' L = K := by
    apply Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      exact hq.2
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := S.image_eq.superset (hKU hx)
      exact ⟨q, ⟨hq, hx⟩, rfl⟩
  let v : PuncturedProjectiveSphere p → UnitThreeSphere := Subtype.val
  let f : PuncturedProjectiveSphere p → M := fun q => S.cover q
  have hv : IsLocalHomeomorph v :=
    (isOpen_puncturedProjectiveSphere p).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hf : IsLocalHomeomorph f :=
    S.isOpen_target.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      S.restrictedCover_isLocalHomeomorph
  have hpre : v ⁻¹' L = f ⁻¹' K := by
    ext q
    exact and_iff_right q.property
  have hipre : v ⁻¹' interior L = f ⁻¹' interior K := by
    rw [hv.isOpenMap.preimage_interior_eq_interior_preimage hv.continuous, hpre,
      ← hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous]
  have hi : interior L =
      {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ interior K} := by
    ext q
    constructor
    · intro hq
      have hp : Quotient.mk' q ≠ p := (interior_subset hq).1
      exact ⟨hp, (Set.ext_iff.mp hipre ⟨q, hp⟩).mp hq⟩
    · rintro ⟨hp, hq⟩
      exact (Set.ext_iff.mp hipre ⟨q, hp⟩).mpr hq
  have hfront : frontier L =
      {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ frontier K} := by
    rw [hL.isClosed.frontier_eq, hi, hK.isClosed.frontier_eq]
    ext q
    simp only [L, mem_sdiff, mem_ofPred_eq]
    tauto
  have hclpre : v ⁻¹' closure (interior L) = f ⁻¹' K := by
    rw [hv.isOpenMap.preimage_closure_eq_closure_preimage hv.continuous, hipre,
      ← hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous, hregular]
  have hreg : closure (interior L) = L := by
    apply Subset.antisymm hL.isClosed.closure_interior_subset
    intro q hq
    exact (Set.ext_iff.mp hclpre ⟨q, hq.1⟩).mpr hq.2
  refine ⟨hL, himage, hi, hfront, hreg, ?_⟩
  intro q
  have hp : (Quotient.mk' (-q) : RealProjectiveThree) = Quotient.mk' q :=
    Quotient.sound (Or.inr rfl)
  constructor
  · rintro ⟨hq, hqK⟩
    have hq' : Quotient.mk' q ≠ p := hp ▸ hq
    exact ⟨hq', ((S.fibers (-q) q hq hq').mpr (Or.inr rfl)) ▸ hqK⟩
  · rintro ⟨hq, hqK⟩
    have hq' : Quotient.mk' (-q) ≠ p := hp.symm ▸ hq
    exact ⟨hq', ((S.fibers (-q) q hq' hq).mpr (Or.inr rfl)).symm ▸ hqK⟩

end PoincareConjecture.StandardPuncturedProjectiveCover
