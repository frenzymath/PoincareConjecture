import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.Comparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalNeck

private theorem exists_staticCylinder_fullDomain_tolerance
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    (m : ℕ) (hm : m ≤ ⌊δ⁻¹⌋₊) :
    ∃ η : ℝ, 0 < η ∧ ∀ (B₀ B₁ : RoundCylinderTwoTensor),
      RoundCylinderClose δ 0 B₀ → RoundCylinderTensorSmoothOn δ B₁ →
      (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-δ⁻¹) δ⁻¹ →
        ∀ j, j ≤ m → ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B₁
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
              roundCylinderTensorCoefficient B₀
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-δ⁻¹) δ⁻¹ →
        roundCylinderJetErrorSquared 0 B₁ m z ≤ (3 * ε ^ 2 + δ ^ 2) / 4 := by
  obtain ⟨C, hC, hCb⟩ := exists_evolvingCylinderJetErrorSquared_bound
    (J := Icc (-δ⁻¹) δ⁻¹) isCompact_Icc m
  have hgap : 0 < ε ^ 2 - δ ^ 2 := by nlinarith
  let θ := (ε ^ 2 - δ ^ 2) / (2 * δ ^ 2)
  have hθ : 0 < θ := div_pos hgap (by positivity)
  have hθeq : θ * (2 * δ ^ 2) = ε ^ 2 - δ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  let η := Real.sqrt (θ * (ε ^ 2 - δ ^ 2) / (4 * ((1 + θ) * C + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hηsq : η ^ 2 = θ * (ε ^ 2 - δ ^ 2) / (4 * ((1 + θ) * C + 1)) :=
    Real.sq_sqrt (by positivity)
  have hηeq : (4 * ((1 + θ) * C + 1)) * η ^ 2 = θ * (ε ^ 2 - δ ^ 2) := by
    rw [hηsq, mul_div_cancel₀ _ (by positivity)]
  refine ⟨η, hη, ?_⟩
  intro B₀ B₁ hclose hsmooth hjet z hz
  have herr : roundCylinderJetErrorSquared 0 (cylinderDifference 0 B₁ B₀) m z ≤
      C * η ^ 2 := by
    apply hCb 0 (by constructor <;> norm_num) _ z ⟨hz.1.le, hz.2.le⟩ η hη.le
    · intro a b
      simp only [cylinderDifference_coefficient]
      have hp : (0, z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
          Ioo (-δ⁻¹) δ⁻¹ := by
        rw [roundCylinder_sphereChart_target]
        exact ⟨mem_univ _, hz⟩
      have hn := ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod
        isOpen_Ioo).mem_nhds hp
      exact ((hsmooth z.1 a b).contDiffAt hn).sub ((hclose.1 z.1 a b).contDiffAt hn)
    · simpa only [cylinderDifference_coefficient] using hjet z hz
  have hlimit : roundCylinderJetErrorSquared 0 B₀ m z ≤ δ ^ 2 := by
    obtain ⟨_, bound, hb, hbound⟩ := hclose
    exact (DeepHorn.evolvingCylinderJetErrorSquared_mono (by norm_num) B₀ z hm).trans
      ((hbound z hz).trans hb.le)
  have hweighted := cylinderDifference_jetError_weighted_le (by norm_num : (0 : ℝ) < 1)
    B₁ B₀ hsmooth hclose.1 m z hz hθ
  have hbound := hweighted.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlimit (by positivity))
    (mul_le_mul_of_nonneg_left herr (by positivity)))
  apply (mul_le_mul_iff_right₀ hθ).mp
  have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
  nlinarith

end PoincareConjecture.TerminalNeck

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}




theorem exists_late_static_neck_terminal_full_domain_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    {ε l u : ℝ} (hεpos : 0 < ε) (hε : ε ≤ 1 / 200) (hl : 0 < l) (hu : 0 < u) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ N : EpsilonNeck ((H.terminalFlow P04).metric t),
        N.epsilon = ε → N.carrier ⊆ A →
        l ≤ N.connection.scalarCurvature N.center →
        N.connection.scalarCurvature N.center ≤ u →
        0 < ((H.terminalFlow P04).connection T).scalarCurvature N.center ∧
        let B : RoundCylinderTwoTensor := fun z v w =>
          ((H.terminalFlow P04).connection T).scalarCurvature N.center *
            roundCylinderPullback ((H.terminalFlow P04).metric T) N.coordinate_map z v w
        RoundCylinderTensorSmoothOn ε B ∧
          ∃ bound : ℝ, bound < (2 * ε) ^ 2 ∧
            ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
              roundCylinderJetErrorSquared 0 B ⌊(2 * ε)⁻¹⌋₊ z ≤ bound := by
  have hweak : ε ≤ 2 * ε := by linarith
  let m := ⌊(2 * ε)⁻¹⌋₊
  have hm : m ≤ ⌊ε⁻¹⌋₊ := Nat.floor_mono
    ((inv_le_inv₀ (mul_pos (by norm_num) hεpos) hεpos).2 hweak)
  obtain ⟨η, hη, htolerance⟩ := TerminalNeck.exists_staticCylinder_fullDomain_tolerance
    hεpos (show ε < 2 * ε by linarith) m hm
  obtain ⟨C, hC, hcoeff⟩ := exists_cylinder_coefficient_jet_constant m
  obtain ⟨s, hs, hsT, hsmall⟩ := H.exists_late_static_neck_normalized_jet_small
    P04 hA hε hl hu m hm (div_pos hη hC)
  refine ⟨s, hs, hsT, ?_⟩
  intro t ht N hNε hNA hql hqu
  obtain ⟨hQ, hjet⟩ := hsmall t ht N hNε hNA hql hqu
  let Q := ((H.terminalFlow P04).connection T).scalarCurvature N.center
  let q := N.connection.scalarCurvature N.center
  let B₁ : RoundCylinderTwoTensor := fun z v w => Q *
    roundCylinderPullback ((H.terminalFlow P04).metric T) N.coordinate_map z v w
  let B₀ : RoundCylinderTwoTensor := fun z v w => q *
    roundCylinderPullback ((H.terminalFlow P04).metric t) N.coordinate_map z v w
  have hpow : N.scale⁻¹ ^ 2 = q := by
    rw [N.scale_eq_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, inv_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul N.scalar_center_pos.le]
    norm_num [q]
  have hclose : RoundCylinderClose ε 0 B₀ := by
    simpa only [B₀, q, hpow, hNε] using N.metric_comparison.close
  have hsmooth : RoundCylinderTensorSmoothOn ε B₁ := by
    apply roundCylinderTensorSmoothOn_smul_pullback
    simpa only [hNε] using N.coordinate_map_smooth
  refine ⟨hQ, hsmooth, 13 * ε ^ 2 / 4, ?_, ?_⟩
  · nlinarith [sq_pos_of_pos hεpos]
  · have hfull := htolerance B₀ B₁ hclose hsmooth ?_
    · intro z hz
      convert hfull z hz using 1
      ring
    intro z hz j hj a b
    have hzold : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      simpa only [hNε] using hz
    let f := centeredNeckLift N z.1 z.2
    let gT := ((H.terminalFlow P04).metric T).pullbackCoefficients f
    let gt := ((H.terminalFlow P04).metric t).pullbackCoefficients f
    have hf := centeredNeckLift_contMDiffAt N z.1 z.2 (zero_mem_centeredNeckDomain N hzold)
    have hgT := ((H.terminalFlow P04).metric T).contDiffAt_pullbackCoefficients hf
    have hgt := ((H.terminalFlow P04).metric t).contDiffAt_pullbackCoefficients hf
    have hlocal : (fun p : E => centeredCylinderMetric B₁ z.1 z.2 p -
        centeredCylinderMetric B₀ z.1 z.2 p) =ᶠ[𝓝 0] fun p => Q • gT p - q • gt p := by
      filter_upwards [(centeredNeckDomain_isOpen N z.2).mem_nhds
        (zero_mem_centeredNeckDomain N hzold)] with p hp
      rw [centeredCylinderMetric_smul, centeredCylinderMetric_smul,
        centeredCylinderMetric_pullback _ N.coordinate_map_smooth _ _ hp,
        centeredCylinderMetric_pullback _ N.coordinate_map_smooth _ _ hp]
      rfl
    have hdiff : ContDiffAt ℝ ∞ (fun p : E => centeredCylinderMetric B₁ z.1 z.2 p -
        centeredCylinderMetric B₀ z.1 z.2 p) 0 :=
      ((hgT.const_smul Q).sub (hgt.const_smul q)).congr_of_eventuallyEq hlocal
    have hjs : ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun p : E =>
        centeredCylinderMetric B₁ z.1 z.2 p - centeredCylinderMetric B₀ z.1 z.2 p) 0‖ ≤ η / C := by
      intro k hk
      rw [(hlocal.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
      exact hjet z hzold k hk
    have hh := hcoeff B₁ B₀ z.1 z.2 hdiff (η / C) (div_pos hη hC).le hjs j hj a b
    simpa only [mul_div_cancel₀ _ hC.ne'] using hh

end PoincareConjecture.SingularTimeAssumptions
