import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.GluingTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.TerminalGeometry









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
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})


def terminalGluingMap :
    Ioc H.reference.tMinus T × (H.extendedSliceGeometry P04 T).slice.carrier →
      H.extendedPoint P04 :=
  H.regularSpacetimeForward P04 ∘ Prod.map id (H.terminalSliceHomeomorph P04)

@[simp] theorem terminalGluingMap_time
    (p : Ioc H.reference.tMinus T × (H.extendedSliceGeometry P04 T).slice.carrier) :
    (H.terminalGluingMap P04 p).1 = (p.1 : ℝ) :=
  H.regularSpacetimeForward_time P04 _

theorem terminalGluingMap_old (t : ℝ) (ht : t ∈ Ioc H.reference.tMinus T)
    (hlt : t < T) (x : (H.extendedSliceGeometry P04 T).slice.carrier) :
    H.terminalGluingMap P04 (⟨t, ht⟩, x) = H.oldSpacetimeForward P04
      (⟨t, H.reference.forward t ⟨le_of_lt ht.1, hlt⟩ (H.terminalSource P04 x)⟩ : F.point) :=
  H.regularSpacetimeForward_old P04 t ht hlt (H.terminalSliceHomeomorph P04 x)

@[simp] theorem terminalGluingMap_terminal
    (x : (H.extendedSliceGeometry P04 T).slice.carrier) :
    H.terminalGluingMap P04 (⟨T, ⟨H.reference.tMinus_lt, le_rfl⟩⟩, x) =
      (⟨T, x⟩ : H.extendedPoint P04) := by
  change H.regularSpacetimeForward P04
    (⟨T, ⟨H.reference.tMinus_lt, le_rfl⟩⟩, H.terminalSliceHomeomorph P04 x) = _
  rw [H.regularSpacetimeForward_terminal P04, Homeomorph.symm_apply_apply]

theorem terminalGluingMap_openEmbedding :
    @IsOpenEmbedding
      (Ioc H.reference.tMinus T × (H.extendedSliceGeometry P04 T).slice.carrier)
      (H.extendedPoint P04) _ (H.extendedSpacetimeTopology P04) (H.terminalGluingMap P04) := by
  let _ := H.extendedSpacetimeTopology P04
  exact (H.regularSpacetimeForward_isOpenEmbedding P04).comp
    (IsOpenEmbedding.id.prodMap (H.terminalSliceHomeomorph P04).isOpenEmbedding)

theorem terminalGluingMap_range :
    range (H.terminalGluingMap P04) = range (H.regularSpacetimeForward P04) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(p.1, H.terminalSliceHomeomorph P04 p.2), rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(p.1, (H.terminalSliceHomeomorph P04).symm p.2), ?_⟩
    change H.regularSpacetimeForward P04
      (p.1, H.terminalSliceHomeomorph P04 ((H.terminalSliceHomeomorph P04).symm p.2)) = _
    rw [Homeomorph.apply_symm_apply]


theorem terminalGluingMap_cover :
    range (H.oldSpacetimeForward P04) ∪ range (H.terminalGluingMap P04) = univ := by
  rw [H.terminalGluingMap_range P04]
  exact H.old_regular_spacetime_range_union P04

end PoincareConjecture.SingularTimeAssumptions
