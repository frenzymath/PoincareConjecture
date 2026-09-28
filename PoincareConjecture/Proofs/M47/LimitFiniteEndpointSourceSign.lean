import PoincareConjecture.Proofs.M47.TerminalCurvatureSectionalScaling
import PoincareConjecture.Proofs.M47.BlowupControlsPinching
import PoincareConjecture.Proofs.M47.LimitFiniteOriginalInterior
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47



theorem limitFinite_source_sectional_of_pinching
    {F : SurgeryFlowData.{u}} (hPinched : SurgeryFlowPinched F)
    {C : GeneralizedSliceCarrier.{u}} {base Q b tau K eta : ℝ}
    (U : TopologicalSpace.Opens C.carrier) (hb : b ≤ -tau) (hK : 0 ≤ K)
    (E : SurgeryFlowCylinder F C base Q (Icc b 0) U)
    (A : RicciFlow 3 U (Icc (-tau) 0))
    (hcurv : ∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
      |(F.connection (base + s / Q)).curvatureTensorNorm (E.forward s hs x)| ≤ K * Q)
    (hmetric : ∀ s (hs : s ∈ Icc (-tau) 0) (x : U),
      ∀ v w : TangentSpace (𝓡 3) x,
        (A.metric s).inner x v w = E.pullbackInner s ⟨hb.trans hs.1, hs.2⟩ x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (heta : 0 < eta) (hscale : blowupPinchingThreshold (3 * K) eta ≤ Q) :
    ∀ s ∈ Icc (-tau) 0, ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      -eta ≤ (A.connection s).sectionalCurvature x v w := by
  intro s hs x v w
  let hsE : s ∈ Icc b 0 := ⟨hb.trans hs.1, hs.2⟩
  let f := fun y : U => E.forward s hsE y.val
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := by
    intro y
    exact ((E.forward_smooth s hsE y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val y)
  have hm : ∀ y ∈ (univ : Set U), ∀ a b : TangentSpace (𝓡 3) y,
      (A.metric s).inner y a b = Q * (F.metric (base + s / Q)).inner
        (f y) (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b) := by
    intro y _ a b
    have hd := mfderiv_comp y
      (((E.forward_smooth s hsE y.val y.property).contMDiffAt
        (U.isOpen.mem_nhds y.property)).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞) y).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) f y = _ at hd
    rw [hmetric s hs y a b, hd]
    rfl
  have hscalar : (F.connection (base + s / Q)).scalarCurvature (f x) ≤ (3 * K) * Q := by
    calc
      _ ≤ 3 * (F.connection (base + s / Q)).curvatureTensorNorm (f x) :=
        (F.connection (base + s / Q)).scalarCurvature_le_curvatureTensorNorm_sharp (f x)
      _ ≤ 3 * (K * Q) := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hcurv s hsE x.val x.property)) (by norm_num)
      _ = _ := by ring
  have hp := hPinched (base + s / Q) (E.time_subset (mem_image_of_mem _ hsE))
  have hnegative : (F.connection (base + s / Q)).negativeCurvaturePart (f x) ≤ eta * Q :=
    negative_part_le_blowup_error (by positivity : 0 ≤ 3 * K) heta hscale hp.1
      hscalar (hp.2.2 (f x) (mem_univ _))
  exact terminalCurvature_sectional_lower_of_scaled_negative
    (A.connection s) (F.connection (base + s / Q)) E.scale_pos
    isOpen_univ hf.contMDiffOn hm (mem_univ x) hnegative v w



theorem limitFinite_eventually_preserved_source_sectional
    (F : ℕ → SurgeryFlowData.{u}) (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (index : ℕ → ℕ) (base Q : ℕ → ℝ)
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier)
    {tau K : ℝ} (hK : 0 ≤ K) (A : ℕ → RicciFlow 3 U (Icc (-tau) 0))
    (hphysical : ∀ᶠ k in atTop, ∃ b, ∃ hb : b ≤ -tau,
      ∃ E : SurgeryFlowCylinder (F (index k)) C
        (base (index k)) (Q (index k)) (Icc b 0) U,
        (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
          |((F (index k)).connection (base (index k) + s / Q (index k))).curvatureTensorNorm
            (E.forward s hs x)| ≤ K * Q (index k)) ∧
        (∀ s (hs : s ∈ Icc (-tau) 0) (x : U), ∀ v w : TangentSpace (𝓡 3) x,
          ((A k).metric s).inner x v w = E.pullbackInner s ⟨hb.trans hs.1, hs.2⟩ x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)))
    (hQ : Tendsto (fun k => Q (index k)) atTop atTop) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop, ∀ s ∈ Icc (-tau) 0,
      ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((A k).connection s).sectionalCurvature x v w := by
  intro eta heta
  filter_upwards [hphysical, hQ.eventually
    (eventually_ge_atTop (blowupPinchingThreshold (3 * K) eta))] with k hk hscale
  obtain ⟨b, hb, E, hcurv, hmetric⟩ := hk
  exact limitFinite_source_sectional_of_pinching (hPinched (index k)) U hb hK E (A k)
    hcurv hmetric heta hscale

end PoincareConjecture.M47
