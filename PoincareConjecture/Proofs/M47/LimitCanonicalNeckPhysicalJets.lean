import PoincareConjecture.Proofs.M47.LimitCanonicalNeckMetricJets
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalCoefficientJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistencePullbackSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem limitCanonical_neck_physical_pullback
    {H : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder H C origin Q I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization H F) (h0 : (0 : ℝ) ∈ I)
    (ht : origin + 0 / Q ∈ H.interval)
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g) (hsource : N.carrier ⊆ U)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback (M13.scaleSmoothMetric (F.metric (origin + 0 / Q)) Q e.scale_pos)
        (limitCanonicalPhysicalChart e hU R 0 h0 ht ∘ N.coordinate_map) z v w =
      generalizedCylinderPullback e N.coordinate_map 0 z v w := by
  let f := limitCanonicalPhysicalChart e hU R 0 h0 ht
  have hx : N.coordinate_map z ∈ U := hsource (N.coordinate_map_mem_of_axial_mem hz)
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3) f (N.coordinate_map z) :=
    f.mdifferentiableAt (by simp)
      (by rw [limitCanonicalPhysicalChart_source]; exact hx)
  have hmap : MDifferentiableAt Ic (𝓡 3) N.coordinate_map z :=
    (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  simp only [generalizedCylinderPullback, dif_pos h0, roundCylinderPullback]
  change Q * (F.metric (origin + 0 / Q)).inner (f (N.coordinate_map z))
      (mfderiv Ic (𝓡 3) (f ∘ N.coordinate_map) z v)
      (mfderiv Ic (𝓡 3) (f ∘ N.coordinate_map) z w) = _
  rw [mfderiv_comp z hf hmap]
  exact limitCanonicalPhysicalChart_metric e hU R 0 h0 ht hx _ _

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E₃ G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_eventually_physical_neck_metric_jets
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (N : EpsilonNeck (G.limit.flow.metric 0))
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ k in atTop,
      let f := limitCanonicalPhysicalTerminalChart G F R k
      let g := M13.scaleSmoothMetric
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      let B : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback g (f ∘ N.coordinate_map) z v w
      K ⊆ G.exhaustion.space k ∧ RoundCylinderTensorSmoothOn N.epsilon B ∧
        ∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ j ≤ Nat.floor N.epsilon⁻¹, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
              roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
                roundCylinderPullback (G.limit.flow.metric 0) N.coordinate_map z v w)
                  (chartAt E₂ q) y a b) (0, z)‖ ≤ rho := by
  let alpha := N.scale⁻¹ ^ 2
  have halpha : 0 ≤ alpha := sq_nonneg _
  let delta := rho / (alpha + 1)
  have hdelta : 0 < delta := div_pos hrho (by positivity)
  have hsmall : alpha * delta ≤ rho := by
    have he : (alpha + 1) * delta = rho := by dsimp only [delta]; field_simp
    nlinarith
  filter_upwards [limitCanonical_eventually_neck_metric_jets G P N
    (Nat.floor N.epsilon⁻¹) le_rfl hK hNK hdelta] with k hk
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let g := M13.scaleSmoothMetric
    ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let B0 := roundCylinderPullback g (f ∘ N.coordinate_map)
  let D0 := roundCylinderPullback (G.limit.flow.metric 0) N.coordinate_map
  let T0 := generalizedCylinderPullback (G.embedding k) N.coordinate_map 0
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have hsource : N.carrier ⊆ f.source := by
    change N.carrier ⊆ (limitCanonicalPhysicalTerminalChart G F R k).source
    rw [limitCanonicalPhysicalTerminalChart, limitCanonicalPhysicalChart_source]
    exact hNK.trans hk.1
  have hsmooth : ContMDiffOn Ic (𝓡 3) ∞ (f ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    f.contMDiffOn_toFun.comp N.coordinate_map_smooth
      (fun _ hz => hsource (N.coordinate_map_mem_of_axial_mem hz.2))
  have hB0 : RoundCylinderTensorSmoothOn N.epsilon B0 :=
    capPersistence_roundCylinderTensorSmoothOn_pullback g hsmooth
  have hD0 : RoundCylinderTensorSmoothOn N.epsilon D0 :=
    capPersistence_roundCylinderTensorSmoothOn_pullback
      (G.limit.flow.metric 0) N.coordinate_map_smooth
  have hread (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (v w : RoundCylinderTangent z) : B0 z v w = T0 z v w :=
    limitCanonical_neck_physical_pullback (G.embedding k) (G.exhaustion.space_open k)
      (R (G.subsequence k)) h0 (limitCanonical_terminal_clock_mem G k)
      N (hNK.trans hk.1) z hz v w
  refine ⟨hk.1, hB0.const_mul, ?_⟩
  intro q z hz j hj a b
  have hcenter : (0, z) ∈ (chartAt E₂ q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using (chartAt E₂ q).map_source (mem_chart_source E₂ q)
  have hnew := (hB0 q a b).contDiffAt
    (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hcenter)
  have hold := (hD0 q a b).contDiffAt
    (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hcenter)
  have heq : (fun y => roundCylinderTensorCoefficient B0 (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient D0 (chartAt E₂ q) y a b) =ᶠ[𝓝 (0, z)]
      (fun y => roundCylinderTensorCoefficient T0 (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient D0 (chartAt E₂ q) y a b) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (0, z) ∈ (univ : Set E₂) ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hz⟩)] with y hy
    exact congrArg (fun r : ℝ => r - roundCylinderTensorCoefficient D0
      (chartAt E₂ q) y a b) (hread ((chartAt E₂ q).symm y.1, y.2) hy.2 _ _)
  have hraw : ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient B0 (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient D0 (chartAt E₂ q) y a b) (0, z)‖ ≤ delta := by
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    exact (hk.2 q z hz j hj a b).le
  have hscale : (fun y =>
      roundCylinderTensorCoefficient (fun z v w => alpha * B0 z v w) (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient (fun z v w => alpha * D0 z v w) (chartAt E₂ q) y a b) =
      (fun y => alpha • (roundCylinderTensorCoefficient B0 (chartAt E₂ q) y a b -
        roundCylinderTensorCoefficient D0 (chartAt E₂ q) y a b)) := by
    funext y
    simp only [roundCylinderTensorCoefficient, smul_eq_mul]
    ring
  change ‖iteratedFDeriv ℝ j (fun y =>
    roundCylinderTensorCoefficient (fun z v w => alpha * B0 z v w) (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient (fun z v w => alpha * D0 z v w) (chartAt E₂ q) y a b)
        (0, z)‖ ≤ rho
  rw [hscale, iteratedFDeriv_const_smul_apply'
    ((hnew.sub hold).of_le (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg halpha]
  exact (mul_le_mul_of_nonneg_left hraw halpha).trans hsmall

end PoincareConjecture.M47
