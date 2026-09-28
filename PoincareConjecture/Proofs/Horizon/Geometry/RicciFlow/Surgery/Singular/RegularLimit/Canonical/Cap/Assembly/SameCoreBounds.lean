import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Assembly.Quantitative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.SameCore.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Volume.Subset



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularRegularLimit



theorem exists_terminal_cap_same_core_quantitative_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
        {A : Set (H.regularRegion P04)}, IsCompact A →
        ∀ x₀ : H.regularRegion P04, 0 < (H.terminalConnection P04).scalarCurvature x₀ →
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t), N.epsilon ≤ ε₀ →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ b : ℝ, -N.epsilon⁻¹ + 40 ≤ b → b < N.epsilon⁻¹ →
          Nonempty (CapQuantitativeData (H.terminalMetric P04) (H.terminalConnection P04)
            (2 * H.constant)
            (H.regularReferencePreimage P04 t ht
              (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b))
            (H.regularReferencePreimage P04 t ht N.core)) := by
  obtain ⟨ε₂, hε₂, hsmall, hdiameter⟩ :=
    exists_truncated_cap_terminal_intrinsicDiameter_threshold.{u}
  let ε₁ := min CapCertificate.coreBallClearanceThreshold.{u}
    CapCertificate.sameCoreBallClearanceThreshold.{u}
  have hε₁ : 0 < ε₁ := lt_min CapCertificate.coreBallClearanceThreshold_pos
    CapCertificate.sameCoreBallClearanceThreshold_pos
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_right _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H P04 A hA x₀ hx₀
  filter_upwards [H.eventually_same_core_calibrated_volume P04 hA x₀ hx₀,
    hdiameter H P04 hA x₀ hx₀,
    H.eventually_captured_cap_terminal_scalar_ratio P04 hA x₀ hx₀,
    H.eventually_captured_cap_terminal_volume_bound_on_subset P04 hA x₀ hx₀,
    H.eventually_captured_cap_terminal_scalarGradient_bound P04 hA x₀ hx₀,
    H.eventually_captured_cap_terminal_scalarEvolution_bound P04 hA x₀ hx₀]
    with t hballs hdiameter hscalar hvolume hgradient hevolution
  intro ht N hε hconstant hconnection hcapture hxcore cut hcut hcutmax
  let U := H.regularReferencePreimage P04 t ht
    (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) cut)
  let K := H.regularReferencePreimage P04 t ht N.core
  have hUsub : U ⊆ H.regularReferencePreimage P04 t ht N.carrier :=
    preimage_mono (union_subset N.closed_core_subset_carrier
      (fun _ hx => N.end_neck_subset hx.1))
  have hxU : x₀ ∈ U := Or.inl (N.core_subset_closed_core hxcore)
  obtain ⟨hpositive, b, hb, hratio⟩ := hscalar ht N hconstant hconnection hcapture hxcore
  obtain ⟨bg, hbg, hgrad⟩ := hgradient ht N hconstant hconnection hcapture hxcore
  obtain ⟨be, hbe, hevol⟩ := hevolution ht N hconstant hconnection hcapture hxcore
  have hcutmem : cut ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨by linarith, hcutmax⟩
  apply CapQuantitativeData.nonempty_of_pointwise_radius
    (H.terminalMetric P04) (H.terminalConnection P04) (2 * H.constant) U K
    (fun x hx => hpositive x (hUsub hx))
    (hdiameter ht N (hε.trans (min_le_right _ _)) hconstant hconnection hcapture hxcore
      cut hcutmem)
    ⟨b, hb, fun x hx y hy => hratio x (hUsub hx) y (hUsub hy)⟩
    (hvolume ht N hconstant hconnection hcapture hxcore U hxU hUsub)
    (b := 3 / (4 * H.constant))
  · rw [inv_eq_one_div]
    apply (div_lt_div_iff₀ (by positivity [H.constant_pos])
      (by positivity [H.constant_pos])).mpr
    nlinarith [H.constant_pos]
  · intro x hx
    exact hballs ht N (hε.trans (min_le_left _ _)) hconstant hconnection hcapture hxcore
      x hx cut hcut
  · exact ⟨bg, hbg, fun x hx => hgrad x (hUsub hx)⟩
  · exact ⟨be, hbe, fun x hx => hevol x (hUsub hx)⟩

end PoincareConjecture.SingularRegularLimit
