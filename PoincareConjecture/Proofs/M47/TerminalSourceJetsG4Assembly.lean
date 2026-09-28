import PoincareConjecture.Proofs.M47.TerminalSourceJetsG4Mixed










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)




structure TerminalSourceJetsG4Good
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    {F₀ : SurgeryFlowData.{u}} (O : SurgeryObservation F₀)
    {W : M33RegularHistoryWindow F₀}
    (H : M33RegularHistoryData W)
    {C₀ : GeneralizedSliceCarrier.{u}}
    {base Q τ rNext : ℝ}
    (U : TopologicalSpace.Opens C₀.carrier)
    (e : GeneralizedFlowCylinder H.generalized C₀ base Q
      (Icc (-τ) 0) (U : Set C₀.carrier))
    (F : RicciFlow 3 U (Icc (-τ) 0))
    {R L eta : ℝ} (C : TerminalSourceChart (F.metric 0) R) : Prop where
  hInitial : F₀.standard_initial = S.setup.standard_initial
  hConstants : F₀.local_constants = S.constants
  hC : F₀.parameters.C = S.setup.C
  hBase : base ∈ Ico (surgeryEpochStart p.i) O.H
  hTauNonneg : 0 ≤ τ
  hScale : 64 * (τ + 1) ≤ Q
  hLarge : B.curvature_threshold ≤ Q
  hThreshold : rNext⁻¹ ^ 2 ≤ Q
  hPinched : SurgeryFlowPinched F₀
  hEarlier : SurgeryCanonicalOn F₀
    (surgeryObservationInterval O ∩ Iio base) rNext
  hOverlap : ∀ u ∈ surgeryObservationInterval O ∩
    Ico (surgeryEpochStart (p.i - 1)) O.H,
    F₀.parameters.delta u ≤ B.delta S.setup.standard_initial S.constants
  hne : (U : Set C₀.carrier).Nonempty
  htime : ∀ s ∈ Icc (-τ) 0,
    base + s / Q ∈ H.generalized.interval
  hnorm : ∀ (s : ℝ) (hs : s ∈ Icc (-τ) 0) (x : U),
    (F.connection s).curvatureTensorNorm x =
      (H.generalized.connection (base + s / Q)).curvatureTensorNorm
        (e.forward s hs x.val) / Q
  hL : 1 ≤ L
  hTerminal : ∀ x : C₀.carrier, x ∈ (U : Set C₀.carrier) →
    normalizedCylinderScalar e x 0 ≤ L
  hShort : blowupAnalyticConstant S B * L * τ ≤ 1 / 4
  heta : 0 < eta
  hPinchingScale : blowupPinchingThreshold (4 * L / 3) eta ≤ Q



theorem terminalSourceJetsG4_eventually_raw
    {α : Type v} (l : Filter α)
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    (P : M46Predecessors.{u})
    {τ R L eta : ℝ} (hτ : 0 < τ)
    (F₀ : α → SurgeryFlowData.{u})
    (O : ∀ k, SurgeryObservation (F₀ k))
    (W : ∀ k, M33RegularHistoryWindow (F₀ k))
    (H : ∀ k, M33RegularHistoryData (W k))
    (C₀ : α → GeneralizedSliceCarrier.{u})
    (base Q rNext : α → ℝ)
    (U : ∀ k, TopologicalSpace.Opens (C₀ k).carrier)
    (e : ∀ k, GeneralizedFlowCylinder (H k).generalized (C₀ k)
      (base k) (Q k) (Icc (-τ) 0) (U k : Set (C₀ k).carrier))
    (F : ∀ k, RicciFlow 3 (U k) (Icc (-τ) 0))
    (C : ∀ k, TerminalSourceChart ((F k).metric 0) R)
    (hGood : ∀ᶠ k in l,
      TerminalSourceJetsG4Good S B p (O k) (H k) (U k) (e k) (F k)
        (τ := τ) (base := base k) (Q := Q k) (rNext := rNext k)
        (R := R) (L := L) (eta := eta) (C k)) :
    ∀ᶠ k in l, ∀ s ∈ Icc (-τ) 0, ∀ y ∈
      (C k).chart '' Metric.ball 0 R,
      ((F k).connection s).curvatureTensorNorm y ≤
        13 * max (4 * L / 3) 1 := by
  filter_upwards [hGood] with k hk
  have h := terminalSourceJetsG4_on_chart S B p (O k)
    hk.hInitial hk.hConstants hk.hC hk.hBase hk.hTauNonneg hk.hScale hk.hLarge
    hk.hThreshold hk.hPinched hk.hEarlier hk.hOverlap P (H k) hτ (U k) (e k)
    (F k) hk.htime hk.hnorm hk.hL hk.hTerminal hk.hShort hk.heta
    hk.hPinchingScale (C k)
  exact h.2

end PoincareConjecture.M47
