import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.DiskMetricTransport
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.ClosedTimeFilling








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}



theorem m65FillingArea_flowMetric_le {K0 K1 K2 : ℝ}
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (gamma : C1FreeLoopSpace (M := M))
    (hD : Nonempty (LipschitzSpanningDisk (F.metric s) gamma)) :
    fillingArea (F.metric t) gamma ≤
      Real.exp ((2 * K2) * |t - s|) * fillingArea (F.metric s) gamma := by
  obtain ⟨D0⟩ := hD
  have hdiv : fillingArea (F.metric t) gamma / Real.exp ((2 * K2) * |t - s|) ≤
      fillingArea (F.metric s) gamma := by
    unfold fillingArea
    refine le_csInf ?_ ?_
    · exact ⟨D0.area, D0, rfl⟩
    · rintro _ ⟨D, rfl⟩
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      exact ((m60FillingArea_le_disk (F.metric t) gamma
        (m65TransportSpanningDisk bounds hs ht D)).trans
        (m65TransportSpanningDisk_area_le bounds hs ht D)).trans_eq (mul_comm _ _)
  exact ((div_le_iff₀ (Real.exp_pos _)).mp hdiv).trans_eq (mul_comm _ _)




theorem m65VaryingMetricFillingArea_le [T2Space M] [SecondCountableTopology M]
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta) (hab : a < b)
    {circumference : ℝ} (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) (s t : Icc a b) :
    fillingArea (F.metric t) ((C.solutions circumference h).projected t z) ≤
      Real.exp ((2 * V.flow.geometry.K2) * |(t : ℝ) - s|) *
        fillingArea (F.metric s) ((C.solutions circumference h).projected s z) +
      Real.exp ((2 * V.flow.geometry.K2) * (b - a)) *
        m65FamilyTotalCurvatureBound C * |(t : ℝ) - s| := by
  let S := C.solutions circumference h
  have htime := m65ClosedTimeFillingDifference hM61 hM64 compact V C hab h hlt z t s t
  have hmetric := m65FillingArea_flowMetric_le V.flow.geometry.bounds s.2 t.2
    (S.projected s z)
    (m65ProjectedDisk_nonempty hM64 compact S s z)
  have hle := (le_abs_self
    (fillingArea (F.metric t) (S.projected t z) -
      fillingArea (F.metric t) (S.projected s z))).trans htime
  linarith

end PoincareConjecture
