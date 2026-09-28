import PoincareConjecture.Proofs.M47.TerminalCurvatureSectionalScaling
import PoincareConjecture.Proofs.M47.TerminalSourceJetsG4Assembly










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47



theorem terminalCurvature_source_sectional_of_first_failure
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {F₀ : SurgeryFlowData.{u}} (O : SurgeryObservation F₀)
    {W : M33RegularHistoryWindow F₀} (H : M33RegularHistoryData W)
    {C₀ : GeneralizedSliceCarrier.{u}} {base Q tau rNext R L eta0 : ℝ}
    (U : TopologicalSpace.Opens C₀.carrier)
    (e : GeneralizedFlowCylinder H.generalized C₀ base Q (Icc (-tau) 0) U)
    (F : RicciFlow 3 U (Icc (-tau) 0))
    (C : TerminalSourceChart (F.metric 0) R)
    (hGood : TerminalSourceJetsG4Good S B p O H U e F
      (L := L) (eta := eta0) (rNext := rNext) C)
    (hmetric : ∀ (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : U),
      ∀ v w : TangentSpace (𝓡 3) x,
        (F.metric s).inner x v w = e.pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C₀.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C₀.carrier) x w))
    {eta : ℝ} (heta : 0 < eta)
    (hscale : blowupPinchingThreshold (4 * L / 3) eta ≤ Q) :
    ∀ s ∈ Icc (-tau) 0, ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      -eta ≤ (F.connection s).sectionalCurvature x v w := by
  intro s hs x v w
  let f := fun y : U => e.forward s hs y.val
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := by
    intro y
    exact ((e.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val y)
  have hm : ∀ y ∈ (univ : Set U), ∀ a b : TangentSpace (𝓡 3) y,
      (F.metric s).inner y a b = Q * (H.generalized.metric (base + s / Q)).inner
        (f y) (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b) := by
    intro y _ a b
    have hd := mfderiv_comp y
      (((e.forward_smooth s hs y.val y.property).contMDiffAt
        (U.isOpen.mem_nhds y.property)).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞) y).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) f y = _ at hd
    rw [hmetric s hs y a b, hd]
    rfl
  have hraw := first_failure_cylinder_curvature_bounds S B p O
    hGood.hInitial hGood.hConstants hGood.hC hGood.hBase hGood.hTauNonneg
    hGood.hScale hGood.hLarge hGood.hThreshold hGood.hPinched hGood.hEarlier
    hGood.hOverlap P H e x.property hGood.hL (hGood.hTerminal x.val x.property)
    hGood.hShort heta hscale s hs
  have hnegative : (H.generalized.connection (base + s / Q)).negativeCurvaturePart
      (f x) ≤ eta * Q := by
    simpa only [GeneralizedFlowCylinder.pointMap, f] using hraw.2
  exact terminalCurvature_sectional_lower_of_scaled_negative
    (F.connection s) (H.generalized.connection (base + s / Q)) e.scale_pos
    isOpen_univ hf.contMDiffOn hm (mem_univ x) hnegative v w



theorem terminalCurvature_eventually_source_sectional
    {α : Type v} (l : Filter α)
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {tau R L eta0 : ℝ}
    (F₀ : α → SurgeryFlowData.{u}) (O : ∀ k, SurgeryObservation (F₀ k))
    (W : ∀ k, M33RegularHistoryWindow (F₀ k))
    (H : ∀ k, M33RegularHistoryData (W k))
    (C₀ : α → GeneralizedSliceCarrier.{u}) (base Q rNext : α → ℝ)
    (U : ∀ k, TopologicalSpace.Opens (C₀ k).carrier)
    (e : ∀ k, GeneralizedFlowCylinder (H k).generalized (C₀ k)
      (base k) (Q k) (Icc (-tau) 0) (U k))
    (F : ∀ k, RicciFlow 3 (U k) (Icc (-tau) 0))
    (C : ∀ k, TerminalSourceChart ((F k).metric 0) R)
    (hGood : ∀ᶠ k in l, TerminalSourceJetsG4Good S B p (O k) (H k)
      (U k) (e k) (F k) (L := L) (eta := eta0) (rNext := rNext k) (C k))
    (hmetric : ∀ k (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : U k),
      ∀ v w : TangentSpace (𝓡 3) x,
        ((F k).metric s).inner x v w = (e k).pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U k → (C₀ k).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U k → (C₀ k).carrier) x w))
    (hQ : Tendsto Q l atTop) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ k in l, ∀ s ∈ Icc (-tau) 0,
      ∀ (x : U k) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((F k).connection s).sectionalCurvature x v w := by
  intro eta heta
  filter_upwards [hGood, hQ.eventually
    (eventually_ge_atTop (blowupPinchingThreshold (4 * L / 3) eta))] with k hk hscale
  exact terminalCurvature_source_sectional_of_first_failure S B p P (O k) (H k)
    (U k) (e k) (F k) (C k) hk (hmetric k) heta hscale

end PoincareConjecture.M47
