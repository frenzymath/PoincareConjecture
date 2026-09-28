import PoincareConjecture.Proofs.M65.Mathlib.ClosedIntervalBound
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.UniformSweptArea
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FillingTimeContinuity
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FillingWitnesses
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.ProjectedAreaEstimate

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

theorem m65InteriorFillingDifference (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (Set.univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    {circumference : ℝ} (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) (q : Set.Icc a b) {s t : ℝ}
    (has : a < s) (hst : s ≤ t) (htb : t < b) :
    |fillingArea (F.metric q) ((C.solutions circumference h).projected
        ⟨t, has.le.trans hst, htb.le⟩ z) -
      fillingArea (F.metric q) ((C.solutions circumference h).projected
        ⟨s, has.le, hst.trans htb.le⟩ z)| ≤
      Real.exp ((2 * V.flow.geometry.K2) * (b - a)) *
        m65FamilyTotalCurvatureBound C * (t - s) := by
  let P := V.flow.geometry.product circumference h
  let S := C.solutions circumference h
  let A := m65InteriorSweptAnnulus (P.flow.metric q) (S.shrinking z) has hst htb
  let st : Set.Icc a b := ⟨s, has.le, hst.trans htb.le⟩
  let tt : Set.Icc a b := ⟨t, has.le.trans hst, htb.le⟩
  obtain ⟨data⟩ := m65FamilyFillingData_from_M64 hM64 (F.metric q) (F.connection q)
    compact (S.projected st) (S.projected_null st) z
  obtain ⟨D⟩ := data.nonempty
  have gluing := V.disks circumference h q q.2
    (fun x => S.curve z x s) (fun x => S.curve z x t) A
    (S.projected st z) (S.projected tt z) (S.projected_eq st z) (S.projected_eq tt z)
  obtain ⟨_, _, hdiff⟩ := m65ProjectedDiskComparison
    (V.flow.projection circumference h q q.2) gluing D
  exact hdiff.trans (m65FamilyInteriorSweptAnnulus_area_le C h hlt z has hst htb q.2)

theorem m65ClosedTimeFillingDifference (hM61 : M61RawWidthCore.{u})
    (hM64 : M64ComparisonTheory.{u}) (compact : IsCompact (Set.univ : Set M))
    (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta) (hab : a < b)
    {circumference : ℝ} (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) (q s t : Set.Icc a b) :
    |fillingArea (F.metric q) ((C.solutions circumference h).projected t z) -
      fillingArea (F.metric q) ((C.solutions circumference h).projected s z)| ≤
      Real.exp ((2 * V.flow.geometry.K2) * (b - a)) *
        m65FamilyTotalCurvatureBound C * |(t : ℝ) - s| := by
  let S := C.solutions circumference h
  let c : ContinuousMap (Set.Icc a b) (C1FreeLoopSpace (M := M)) :=
    ⟨fun r => S.projected r z,
      S.projected_continuous.comp (continuous_id.prodMk continuous_const)⟩
  have harea := m65FillingArea_continuous_time hM61 (F.metric q) compact hab c
    (fun r => S.projected_null r z)
  exact M65.closedInterval_difference_bound hab (fun r => fillingArea (F.metric q) (c r))
    harea (fun r v hr hv hrv =>
      m65InteriorFillingDifference hM64 compact V C h hlt z q hr.1 hrv hv.2) s t

end PoincareConjecture
