import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Jets.TailIdentity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.UniformJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_uniform_neck_tail_coefficient_bound
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hΩ : H.reference.regularLimitSet.Nonempty) (hε : H.epsilon ≤ 1 / 200)
    (x₀ : H.regularRegion P04) (hQ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (m : ℕ) (hm : m ≤ ⌊H.epsilon⁻¹⌋₊) :
    ∃ s B : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 ≤ B ∧
      ∀ t (ht : t ∈ Ioo H.reference.tMinus T), s ≤ t →
        ∀ N : GeneralizedStrongNeck F t H.epsilon,
          N.center = H.reference.forward t ⟨ht.1.le, ht.2⟩ x₀ →
          H.reference.inverse t ⟨ht.1.le, ht.2⟩ '' N.carrier ⊆ Subtype.val '' A →
          ∀ hR : (F.connection t).scalarCurvature N.center <
            (H.terminalConnection P04).scalarCurvature x₀,
          ∀ {δ : ℝ} (hεδ : H.epsilon ≤ δ),
          ∀ τ ∈ Ioc (-1 : ℝ) 0,
            T + τ / (H.terminalConnection P04).scalarCurvature x₀ ∈ Icc t T →
          ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-δ⁻¹) δ⁻¹ →
          ∀ j ≤ m, ∀ a b : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y =>
              roundCylinderTensorCoefficient
                  (H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR hεδ τ)
                  (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
                roundCylinderTensorCoefficient (fun z v w =>
                  ((H.terminalConnection P04).scalarCurvature x₀ /
                    (F.connection t).scalarCurvature N.center) *
                    generalizedCylinderPullback N.time_cylinder N.coordinate_map 0 z v w)
                  (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ B * (T - t) := by
  obtain ⟨s, B, hs, hsT, hB, htime⟩ :=
    H.exists_uniform_neck_coordinate_tail_bound P04 hε x₀ hQ hA m hm
  obtain ⟨C, hC, hcoeff⟩ := exists_cylinder_coefficient_jet_constant m
  let Q := (H.terminalConnection P04).scalarCurvature x₀
  refine ⟨s, C * Q * B, hs, hsT, by positivity, ?_⟩
  intro t ht hst N hcenter hNA hR δ hεδ τ hτ hr z hz j hj a b
  have hhalf : H.epsilon < 1 / 2 := by linarith
  have hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      N.carrier H.reference.regularLimitSet := by
    intro y hy
    obtain ⟨w, _, hw⟩ := hNA (mem_image_of_mem _ hy)
    exact hw ▸ w.property
  let r := T + τ / Q
  let f := H.regularNeckCenteredLift P04 ⟨ht.1.le, ht.2⟩ N hhalf x₀ z
  let g₁ := ((H.terminalFlow P04).metric r).pullbackCoefficients f
  let g₀ := ((H.terminalFlow P04).metric t).pullbackCoefficients f
  let B₁ := H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR hεδ τ
  let B₀ : RoundCylinderTwoTensor := fun y v w =>
    (Q / (F.connection t).scalarCurvature N.center) *
      generalizedCylinderPullback N.time_cylinder N.coordinate_map 0 y v w
  have hz' := DeepHorn.neckInterval_subset H.epsilon_pos hεδ hz
  have hf := (H.regularNeckCenteredLift_smooth P04 ⟨ht.1.le, ht.2⟩ N hhalf x₀ hcapture z).contMDiffAt
    ((centeredNeckDomain_isOpen (N.spatialNeck hhalf) z.2).mem_nhds
      (zero_mem_centeredNeckDomain (N.spatialNeck hhalf) hz'))
  have hg₁ : ContDiffAt ℝ ∞ g₁ 0 := ((H.terminalFlow P04).metric r).contDiffAt_pullbackCoefficients hf
  have hg₀ : ContDiffAt ℝ ∞ g₀ 0 := ((H.terminalFlow P04).metric t).contDiffAt_pullbackCoefficients hf
  have hlocal : (fun p : E => centeredCylinderMetric B₁ z.1 z.2 p -
      centeredCylinderMetric B₀ z.1 z.2 p) =ᶠ[𝓝 0] fun p => Q • (g₁ p - g₀ p) := by
    have hn : {p : E | cylinderHeightCovector p + z.2 ∈ Ioo (-δ⁻¹) δ⁻¹} ∈ 𝓝 0 :=
      (isOpen_Ioo.preimage (cylinderHeightCovector.continuous.add continuous_const)).mem_nhds
        (by simpa only [mem_preimage, Pi.add_apply, map_zero, zero_add] using hz)
    filter_upwards [hn] with p hp
    rw [H.regularNeckWeakenedTerminalTensor_centered P04 hΩ ht N hhalf x₀ hR hεδ hcapture
        hτ ⟨ht.1.trans_le hr.1, hr.2⟩ z hp,
      H.regularNeckScaledOldTensor_centered P04 ht N hhalf x₀ hcapture z
        (DeepHorn.neckInterval_subset H.epsilon_pos hεδ hp), smul_sub]
  have hD : ContDiffAt ℝ ∞ (fun p : E => centeredCylinderMetric B₁ z.1 z.2 p -
      centeredCylinderMetric B₀ z.1 z.2 p) 0 :=
    ((hg₁.sub hg₀).const_smul Q).congr_of_eventuallyEq hlocal
  have hjets : ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun p : E =>
      centeredCylinderMetric B₁ z.1 z.2 p - centeredCylinderMetric B₀ z.1 z.2 p) 0‖ ≤
        Q * (B * (T - t)) := by
    intro k hk
    rw [(hlocal.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,
      iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) ((hg₁.sub hg₀).of_le (by exact_mod_cast le_top)),
      fun_iteratedFDeriv_sub_apply (hg₁.of_le (by exact_mod_cast le_top))
        (hg₀.of_le (by exact_mod_cast le_top)), norm_smul, Real.norm_eq_abs, abs_of_pos hQ]
    have htime' := htime t ⟨ht.1.le, ht.2⟩ hst N hcenter hNA z hz' r hr k hk
    exact (mul_le_mul_of_nonneg_left htime' hQ.le).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hr.2 t) hB) hQ.le)
  have hbound := hcoeff B₁ B₀ z.1 z.2 hD (Q * (B * (T - t)))
    (by exact mul_nonneg hQ.le (mul_nonneg hB (sub_nonneg.mpr ht.2.le))) hjets j hj a b
  simpa only [mul_assoc] using hbound

end PoincareConjecture.SingularTimeAssumptions
