import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.AreaLoops
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ShortLoops
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.CommonCircumference

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

theorem m65CommonTerminalAlternative (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (Set.univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (E : M64AppliedFamilyEstimates V.flow.geometry C)
    {s eta : ℝ} (heta : 0 < eta) (has : a ≤ s) (hsb : s < b)
    (hgrowth : Real.exp (V.flow.geometry.K2 * (b - s)) < 4 / 3)
    (pointwise : ∀ w : LoopTwoSphere, ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ circumference (h : 0 < circumference), circumference < 1 → circumference < cutoff →
        fillingArea (F.metric b)
            ((C.solutions circumference h).projected ⟨b, has.trans hsb.le, le_rfl⟩ w) ≤
          areaComparisonProfile F (fillingArea (F.metric a) (C.approximation.family w)) b +
            eta / 2 ∨
          ∀ t ∈ Set.Icc s b, m62Length (V.flow.geometry.product circumference h).flow
            ((C.solutions circumference h).curve w) t < eta / 2) :
    ∃ circumference : ℝ, ∃ h : 0 < circumference, circumference < 1 ∧
      ∀ z : LoopTwoSphere,
        freeLoopLength (F.metric b)
            ((C.solutions circumference h).projected ⟨b, has.trans hsb.le, le_rfl⟩ z) < eta ∨
          fillingArea (F.metric b)
              ((C.solutions circumference h).projected ⟨b, has.trans hsb.le, le_rfl⟩ z) ≤
            areaComparisonProfile F (fillingArea (F.metric a) (C.approximation.family z)) b +
              eta := by
  classical
  obtain ⟨muArea, hmuArea, harea⟩ := m65AreaLoopTransfer hM64 compact V C
    (has.trans hsb.le) heta
  obtain ⟨muShort, hmuShort, hshort⟩ := m65ShortLoopTransfer V C E heta has hsb hgrowth
  let mu := min muArea muShort
  have hmu : 0 < mu := lt_min hmuArea hmuShort
  obtain ⟨net⟩ := V.finite_nets C.approximation.family mu hmu
  choose cutoff hpositive hnode using pointwise
  obtain ⟨circumference, h, hlt, hnet, hcutoff⟩ :=
    m65CommonCircumference net cutoff (fun i => hpositive (net.nodes i))
  refine ⟨circumference, h, hlt, ?_⟩
  intro z
  obtain ⟨i, hcover⟩ := net.covers z
  obtain ⟨A, hA⟩ := hcover circumference h hnet
  rcases hnode (net.nodes i) circumference h hlt (hcutoff i) with hbound | hsmall
  · exact Or.inr (harea circumference h z (net.nodes i) A
      (hA.trans_le (min_le_left _ _)) hbound)
  · exact Or.inl (hshort circumference h hlt z (net.nodes i) A
      (hA.trans_le (min_le_right _ _)) hsmall)

end PoincareConjecture
