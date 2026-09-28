import PoincareConjecture.Proofs.M65.Assembly
import PoincareConjecture.Proofs.M65.Def18_23_Profile.AreaComparisonProfile
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.NetConclusion
import PoincareConjecture.Proofs.M61.Def18_17_Width.FreeClassInfimum
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.Continuity

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m65RawWidthCore_from_closed_predecessors : M61RawWidthCore.{u} := by
  constructor
  · intro M _ _ _ _ _ g hcompact F hnull
    exact m61FamilyWidth_from_M60 g (m60FillingAreaProperties_of_compact g hcompact) F hnull
  · intro M _ _ _ _ _ g hcompact F hnull
    exact m61FreeClassWidth_from_M60 g (m60FillingAreaProperties_of_compact g hcompact) F hnull

def m65ZeroDurationDeformedFamily
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {a zeta : ℝ}
    (P : M65RawFlowInput M a a) (hzeta : 0 < zeta) : M65DeformedFamily M P zeta where
  family := fun _ => P.family
  family_continuous := P.family.continuous.comp continuous_snd
  null := fun _ => P.family_null
  free_homotopy_to_initial := fun _ => ContinuousMap.Homotopic.refl P.family
  initial_area_close := fun _ => by simpa only [sub_self, abs_zero] using hzeta
  terminal_alternative := fun _ => Or.inr (by
    rw [areaComparisonProfile_initial]
    exact le_add_of_nonneg_right hzeta.le)

theorem m65Construction
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {a b : ℝ} (P : M65RawFlowInput M a b)
    (H : M65Predecessors M P) : Nonempty (M65Conclusion M P H) := by
  classical
  let : T2Space M := P.hausdorff
  let : SecondCountableTopology M := P.second_countable
  refine ⟨{ deformation := ?_ }⟩
  intro zeta hzeta
  rcases lt_or_eq_of_le P.time_ordered with hab | hab
  · obtain ⟨N, _, hN⟩ := H.m64.approximation P.family P.family_null zeta hzeta
    obtain ⟨Q⟩ := hN N le_rfl
    obtain ⟨circumference, h, _, terminal⟩ :=
      m65CommonTerminalAlternative_proved hM61 hM64 P.compact H.m64
        Q.family Q.estimates hab hzeta
    exact ⟨m65DeformedFamilyOfProjectedEstimate (P := P)
      (Q.family.solutions circumference h) terminal⟩
  · subst b
    exact ⟨m65ZeroDurationDeformedFamily P hzeta⟩

end PoincareConjecture
