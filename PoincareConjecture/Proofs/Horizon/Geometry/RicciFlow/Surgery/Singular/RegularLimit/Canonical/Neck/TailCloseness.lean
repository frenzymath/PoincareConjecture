import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Jets.TailCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TailComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ClockControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TensorRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

private theorem cylinderFamilyClose_of_split {ε a : ℝ} {I : Set ℝ}
    {B : ℝ → RoundCylinderTwoTensor}
    (hleft : RoundCylinderFamilyClose ε (I ∩ Iic a) B)
    (hright : RoundCylinderFamilyClose ε (I ∩ Ici a) B) :
    RoundCylinderFamilyClose ε I B := by
  obtain ⟨hl, L, hL, hleft⟩ := hleft
  obtain ⟨hr, R, hR, hright⟩ := hright
  refine ⟨?_, max L R, max_lt hL hR, ?_⟩
  · intro s hs
    rcases le_total s a with h | h
    · exact hl s ⟨hs, h⟩
    · exact hr s ⟨hs, h⟩
  · intro s hs z hz
    rcases le_total s a with h | h
    · exact (hleft s ⟨hs, h⟩ z hz).trans (le_max_left _ _)
    · exact (hright s ⟨hs, h⟩ z hz).trans (le_max_right _ _)

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_late_neck_terminal_metric_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hΩ : H.reference.regularLimitSet.Nonempty) (hε : H.epsilon ≤ 1 / 200)
    (x₀ : H.regularRegion P04) (hQ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t (ht : t ∈ Ioo H.reference.tMinus T), s < t →
        ∀ N : GeneralizedStrongNeck F t H.epsilon,
          N.center = H.reference.forward t ⟨ht.1.le, ht.2⟩ x₀ →
          H.reference.inverse t ⟨ht.1.le, ht.2⟩ '' N.carrier ⊆ Subtype.val '' A →
          ∀ hR : (F.connection t).scalarCurvature N.center <
            (H.terminalConnection P04).scalarCurvature x₀,
            RoundCylinderFamilyClose (2 * H.epsilon) (Ioc (-1 : ℝ) 0)
              (H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR
                (show H.epsilon ≤ 2 * H.epsilon by linarith [H.epsilon_pos])) := by
  have hweak : H.epsilon ≤ 2 * H.epsilon := by linarith [H.epsilon_pos]
  have hm : ⌊(2 * H.epsilon)⁻¹⌋₊ ≤ ⌊H.epsilon⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (mul_pos (by norm_num) H.epsilon_pos) H.epsilon_pos).2 hweak)
  obtain ⟨η, hη, htolerance⟩ := SingularRegularLimit.exists_short_tail_coefficient_tolerance H.epsilon_pos
  obtain ⟨sJ, B, hsJ, hsJT, hB, hjets⟩ :=
    H.exists_uniform_neck_tail_coefficient_bound P04 hΩ hε x₀ hQ hA ⌊(2 * H.epsilon)⁻¹⌋₊ hm
  obtain ⟨sC, hsC, hsCT, hclock⟩ := H.exists_late_neck_clock_control P04 x₀ hQ
  have hwindow : T - η / (B + 1) < T := by
    have : 0 < η / (B + 1) := by positivity
    linarith
  obtain ⟨s, hs, hsT⟩ := exists_between (max_lt hsJT (max_lt hsCT hwindow))
  have hssJ : sJ < s := (le_max_left _ _).trans_lt hs
  have hssC : sC < s := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  have hssmall : T - η / (B + 1) < s :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  refine ⟨s, hsJ.trans hssJ, hsT, ?_⟩
  intro t ht hst N hcenter hNA hR
  let Q := (H.terminalConnection P04).scalarCurvature x₀
  let q := (F.connection t).scalarCurvature N.center
  let d := Q * (T - t)
  have hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      N.carrier H.reference.regularLimitSet := by
    intro y hy
    obtain ⟨w, _, hw⟩ := hNA (mem_image_of_mem _ hy)
    exact hw ▸ w.property
  obtain ⟨hc, hcmax, hcε, hd, hdε⟩ :=
    hclock t ⟨ht.1.le, ht.2⟩ (hssC.trans hst) N hcenter hR
  have hsmall : B * (T - t) ≤ η := by
    have hdt : 0 ≤ T - t := sub_nonneg.mpr ht.2.le
    have hnear : T - t < η / (B + 1) := by linarith
    have hprod := (lt_div_iff₀ (by positivity : 0 < B + 1)).1 hnear
    nlinarith
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hclose₀ : RoundCylinderClose H.epsilon 0
      (generalizedCylinderPullback N.time_cylinder N.coordinate_map 0) :=
    ⟨N.metric_comparison.1 0 hzero, N.metric_comparison.2.choose,
      N.metric_comparison.2.choose_spec.1,
      N.metric_comparison.2.choose_spec.2 0 hzero⟩
  have hr (τ : ℝ) (hτ : τ ∈ Ioc (-1 : ℝ) 0 ∩ Ici (-d)) :
      T + τ / Q ∈ Icc t T := by
    constructor
    · have hdiv : t - T ≤ τ / Q := by
        apply (le_div_iff₀ (show 0 < Q from hQ)).2
        have hcut : -(Q * (T - t)) ≤ τ := hτ.2
        nlinarith
      linarith
    · exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hτ.1.2 hQ.le)
  have htail := htolerance hc hcmax hcε hdε
    (generalizedCylinderPullback N.time_cylinder N.coordinate_map 0)
    (H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR hweak) hclose₀
    (fun τ hτ => ?_) (fun τ hτ z hz j hj a b => ?_)
  · exact cylinderFamilyClose_of_split
      (H.regularNeckWeakenedTerminalTensor_retained_comparison P04 hΩ ht N x₀ hR
        hcapture hc hcmax hcε hdε) htail
  · have hg := (H.regularNeckSpatialMap_smooth P04 ⟨ht.1.le, ht.2⟩ N x₀ hcapture).mono
      (prod_mono subset_rfl (DeepHorn.neckInterval_subset H.epsilon_pos hweak))
    apply (roundCylinderTensorSmoothOn_smul_pullback
      ((H.terminalFlow P04).metric (T + τ / Q)) hg Q).congr
    intro z hz v w
    exact H.regularNeckWeakenedTerminalTensor_regular P04 hΩ ht N x₀ hR hweak hcapture
      hτ.1 ⟨ht.1.trans_le (hr τ hτ).1, (hr τ hτ).2⟩ z hz v w
  · exact (hjets t ht (hssJ.trans hst).le N hcenter hNA hR hweak τ hτ.1
      (hr τ hτ) z hz j hj a b).trans hsmall

end SingularTimeAssumptions
end PoincareConjecture
