import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.SliceIdentifications
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.ReferenceEmbedding








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Topology
open scoped Manifold ContDiff Bundle

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


abbrev extendedPoint (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :=
  Σ t : ℝ, (H.extendedSliceGeometry P04 t).slice.carrier

theorem oldPoint_time_mem (_H : SingularTimeAssumptions F T M) (p : F.point) :
    p.1 ∈ F.interval :=
  (F.slice_nonempty_iff p.1).mp ⟨p.2⟩

theorem oldPoint_time_ne_terminal (H : SingularTimeAssumptions F T M) (p : F.point) :
    p.1 ≠ T := by
  intro ht
  exact H.terminal_not_in_interval (ht ▸ H.oldPoint_time_mem p)


def oldSpacetimeForward (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (p : F.point) : H.extendedPoint P04 :=
  ⟨p.1, H.oldSliceHomeomorph P04 (H.oldPoint_time_ne_terminal p) p.2⟩

@[simp] theorem oldSpacetimeForward_time (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (p : F.point) :
    (H.oldSpacetimeForward P04 p).1 = p.1 := rfl

theorem oldSpacetimeForward_eq (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ≠ T)
    (x : (F.slice t).carrier) :
    H.oldSpacetimeForward P04 ⟨t, x⟩ = ⟨t, H.oldSliceHomeomorph P04 ht x⟩ := rfl

theorem oldSpacetimeForward_injective (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : Injective (H.oldSpacetimeForward P04) := by
  rintro ⟨t, x⟩ ⟨s, y⟩ hxy
  have hts : t = s := congrArg Sigma.fst hxy
  subst s
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact (H.oldSliceHomeomorph P04 (H.oldPoint_time_ne_terminal ⟨t, x⟩)).injective
      (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2)


theorem oldSpacetimeForward_range (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    range (H.oldSpacetimeForward P04) = {p : H.extendedPoint P04 | p.1 ∈ F.interval} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact H.oldPoint_time_mem q
  · intro hp
    have ht : p.1 ≠ T := fun ht => H.terminal_not_in_interval (ht ▸ hp)
    refine ⟨⟨p.1, (H.oldSliceHomeomorph P04 ht).symm p.2⟩, ?_⟩
    rw [H.oldSpacetimeForward_eq P04 ht]
    exact Sigma.ext rfl (heq_of_eq ((H.oldSliceHomeomorph P04 ht).apply_symm_apply p.2))


theorem mem_range_oldSpacetimeForward_iff (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (p : H.extendedPoint P04) :
    p ∈ range (H.oldSpacetimeForward P04) ↔ p.1 ≠ T := by
  constructor
  · rintro ⟨q, rfl⟩
    exact H.oldPoint_time_ne_terminal q
  · intro ht
    refine ⟨⟨p.1, (H.oldSliceHomeomorph P04 ht).symm p.2⟩, ?_⟩
    rw [H.oldSpacetimeForward_eq P04 ht]
    exact Sigma.ext rfl (heq_of_eq ((H.oldSliceHomeomorph P04 ht).apply_symm_apply p.2))



def regularSpacetimeForward (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u})
    (p : Ioc H.reference.tMinus T × H.regularRegion P04) : H.extendedPoint P04 :=
  if ht : (p.1 : ℝ) = T then
    ⟨T, (H.terminalSliceHomeomorph P04).symm p.2⟩
  else
    H.oldSpacetimeForward P04
      ⟨p.1, H.reference.forward p.1 ⟨p.1.property.1.le, lt_of_le_of_ne p.1.property.2 ht⟩ p.2⟩

@[simp] theorem regularSpacetimeForward_time (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u})
    (p : Ioc H.reference.tMinus T × H.regularRegion P04) :
    (H.regularSpacetimeForward P04 p).1 = (p.1 : ℝ) := by
  unfold regularSpacetimeForward
  split_ifs with ht
  · exact ht.symm
  · rfl


theorem regularSpacetimeForward_old (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T)
    (hlt : t < T) (x : H.regularRegion P04) :
    H.regularSpacetimeForward P04 (⟨t, ht⟩, x) =
      H.oldSpacetimeForward P04 ⟨t, H.reference.forward t ⟨ht.1.le, hlt⟩ x⟩ := by
  simp only [regularSpacetimeForward, dif_neg hlt.ne]


@[simp] theorem regularSpacetimeForward_terminal (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x : H.regularRegion P04) :
    H.regularSpacetimeForward P04 (⟨T, ⟨H.reference.tMinus_lt, le_rfl⟩⟩, x) =
      ⟨T, (H.terminalSliceHomeomorph P04).symm x⟩ := by
  simp [regularSpacetimeForward]

theorem regularSpacetimeForward_injective (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : Injective (H.regularSpacetimeForward P04) := by
  rintro ⟨⟨t, ht⟩, x⟩ ⟨⟨s, hs⟩, y⟩ hxy
  have hts : t = s := by
    have h := congrArg Sigma.fst hxy
    simpa only [regularSpacetimeForward_time] using h
  subst s
  apply Prod.ext
  · rfl
  change x = y
  by_cases hT : t = T
  · subst t
    rw [H.regularSpacetimeForward_terminal P04, H.regularSpacetimeForward_terminal P04] at hxy
    exact (H.terminalSliceHomeomorph P04).symm.injective
      (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2)
  · have hlt : t < T := lt_of_le_of_ne ht.2 hT
    rw [H.regularSpacetimeForward_old P04 t ht hlt,
      H.regularSpacetimeForward_old P04 t hs hlt] at hxy
    have h_old := H.oldSpacetimeForward_injective P04 hxy
    exact Subtype.ext ((H.reference.forward_openEmbedding t ⟨ht.1.le, hlt⟩).injective
      (eq_of_heq (Sigma.mk.inj_iff.mp h_old).2))


theorem old_regular_spacetime_cover (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (p : H.extendedPoint P04) :
    p ∈ range (H.oldSpacetimeForward P04) ∨ p ∈ range (H.regularSpacetimeForward P04) := by
  rcases p with ⟨t, x⟩
  by_cases ht : t = T
  · subst t
    right
    refine ⟨(⟨T, ⟨H.reference.tMinus_lt, le_rfl⟩⟩, H.terminalSliceHomeomorph P04 x), ?_⟩
    rw [H.regularSpacetimeForward_terminal P04]
    exact Sigma.ext rfl (heq_of_eq ((H.terminalSliceHomeomorph P04).symm_apply_apply x))
  · left
    refine ⟨⟨t, (H.oldSliceHomeomorph P04 ht).symm x⟩, ?_⟩
    rw [H.oldSpacetimeForward_eq P04 ht]
    exact Sigma.ext rfl (heq_of_eq ((H.oldSliceHomeomorph P04 ht).apply_symm_apply x))

theorem old_regular_spacetime_range_union (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    range (H.oldSpacetimeForward P04) ∪ range (H.regularSpacetimeForward P04) = univ := by
  exact eq_univ_of_forall (H.old_regular_spacetime_cover P04)

end PoincareConjecture.SingularTimeAssumptions
