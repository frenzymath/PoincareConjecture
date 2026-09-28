import PoincareConjecture.Proofs.M28.Generalized.StrongNeckQuarterBounds
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeLower
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.LocalNormalCharts











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

local notation "E" => EuclideanSpace ℝ (Fin 3)





theorem exists_strongNeck_source_center_charts_accuracy
    (hShi : LocalCurvatureDerivativeEstimates.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∃ K R rho : ℝ, 0 < K ∧
        R = RiemannianMetric.localInjectivityRadius 3 K (1 / 8)
          (normalizedNeckVolumeLowerConstant * (1 / 8 : ℝ) ^ 3) ∧
        0 < R ∧ R < 1 / 8 ∧ 0 < rho ∧ 2 * rho < R ∧
        ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
          ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
            ∀ (F : GeneralizedRicciFlowData.{u}) (t : ℝ)
              (S : GeneralizedStrongNeck F t epsilon)
              (H : RescaledRawCylinderData (C := F.slice t)
                (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
                (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)),
              let G := GeneralizedStrongNeck.rescaled_half_flow S H
              let p : strongNeckOpen S := strongNeckSourceCenter S
              (∀ s ∈ Icc (-(1 / 2 : ℝ)) 0, ∀ x : strongNeckOpen S,
                (G.connection s).curvatureTensorNorm x ≤ K) ∧
              ∃ L : E ≃L[ℝ] E,
              ∃ Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E (strongNeckOpen S) ∞,
                Phi.source = Metric.ball 0 R ∧
                Phi.target = (G.metric 0).ball p R ∧
                Phi 0 = p ∧
                (∀ v w, (G.metric 0).pullbackCoefficients (extChartAt (𝓡 3) p).symm
                  (extChartAt (𝓡 3) p p) (L v) (L w) = inner ℝ v w) ∧
                HasFDerivAt (fun w => extChartAt (𝓡 3) p (Phi w))
                  L.toContinuousLinearMap 0 ∧
                (∀ v w, (G.metric 0).pullbackCoefficients Phi 0 v w = inner ℝ v w) ∧
                (∀ w ∈ Metric.ball 0 R,
                  (G.metric 0).IsGeodesicOn (fun s : ℝ => Phi (s • w))
                    {s : ℝ | s • w ∈ Metric.ball 0 R}) ∧
                (∀ w ∈ Metric.ball 0 R, ∀ s ∈ Icc (0 : ℝ) 1,
                  (G.metric 0).tangentNorm (Phi (s • w))
                    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun a : ℝ => Phi (a • w)) s 1) = ‖w‖) ∧
                (∀ w ∈ Metric.ball 0 R,
                  (G.metric 0).edist p (Phi w) = ENNReal.ofReal ‖w‖) ∧
                (∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
                  (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (G.metric 0).pullbackCoefficients Phi x v v ∧
                    (G.metric 0).pullbackCoefficients Phi x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
                (∀ m : ℕ, ∀ s ∈ Icc (-(1 / 4 : ℝ)) 0, ∀ x ∈ Metric.ball (0 : E) R,
                  (G.connection s).curvatureDerivativeNorm m (Phi x) ≤ B m) ∧
                (G.connection 0).scalarCurvature (Phi 0) = 1 := by
  classical
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, hsource⟩ :=
    exists_strongNeck_source_quarter_bounds_accuracy hShi
  let v : ℝ := normalizedNeckVolumeLowerConstant * (1 / 8 : ℝ) ^ 3
  have hv : 0 < v :=
    mul_pos normalizedNeckVolumeLowerConstant_pos (pow_pos (by norm_num) 3)
  let R : ℝ := RiemannianMetric.localInjectivityRadius 3 K (1 / 8) v
  have hR : 0 < R :=
    RiemannianMetric.localInjectivityRadius_pos 3 K (by norm_num) v
  have hRsmall : R < 1 / 8 :=
    RiemannianMetric.localInjectivityRadius_lt 3 K (by norm_num) v
  obtain ⟨rho, hrho, hrhoR, hcomparison⟩ :=
    RiemannianMetric.exists_uniform_radial_comparison_radius hR K
  refine ⟨epsilon₀, hepsilon₀, hthreshold, K, R, rho, hK, rfl,
    hR, hRsmall, hrho, hrhoR, ?_⟩
  intro epsilon hepsilon hsmall
  obtain ⟨B, hB, hfamily⟩ := hsource epsilon hepsilon hsmall
  refine ⟨B, hB, ?_⟩
  intro F t S H
  let G := GeneralizedStrongNeck.rescaled_half_flow S H
  let p : strongNeckOpen S := strongNeckSourceCenter S
  have hepsilon200 : epsilon ≤ (1 / 200 : ℝ) := hsmall.trans hthreshold
  have hhalf : epsilon < 1 / 2 := hepsilon200.trans_lt (by norm_num)
  let N := GeneralizedStrongNeck.rescaled_half_source_neck S H hhalf
  obtain ⟨hcurv, hderiv⟩ := hfamily F t S H
  have hinv : (200 : ℝ) ≤ epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le hepsilon hepsilon200
    norm_num at h
    exact h
  have hbuffer : (1 : ℝ) ≤ epsilon⁻¹ / 16 := by linarith only [hinv]
  have houter : (1 : ℝ) ≤ epsilon⁻¹ / 8 := by linarith only [hinv]
  have hbig : IsCompact (closure ((G.metric 0).ball p (epsilon⁻¹ / 8))) :=
    (GeneralizedStrongNeck.rescaled_half_center_ball_capture S H hhalf).2.1
  have hcompact : IsCompact (closure ((G.metric 0).ball p 1)) :=
    hbig.of_isClosed_subset isClosed_closure (closure_mono
      (fun x hx => hx.trans_le (ENNReal.ofReal_le_ofReal houter)))
  have hvolume (q : strongNeckOpen S) (hq : q ∈ (G.metric 0).ball p (1 / 8)) :
      ENNReal.ofReal v ≤ (G.metric 0).volumeMeasure ((G.metric 0).ball q (1 / 8)) := by
    exact normalized_neck_ball_volume_lower N rfl rfl hepsilon200
      (by norm_num : (0 : ℝ) < 1) hbuffer
      (hq.trans_le (ENNReal.ofReal_le_ofReal (by norm_num : (1 / 8 : ℝ) ≤ 1)))
      (by norm_num : (0 : ℝ) < 1 / 8) le_rfl
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : strongNeckOpen S → Type _) :=
    ⟨(G.metric 0).toRiemannianMetric⟩
  have hp : p ∈ (G.metric 0).ball p (1 / 8) := by
    change (G.metric 0).edist p p < ENNReal.ofReal (1 / 8 : ℝ)
    rw [show (G.metric 0).edist p p = 0 from Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  obtain ⟨L, Phi, hsourcePhi, htargetPhi, hzero, hL, hd, hgeo, hdist, hell⟩ :=
    exists_normal_chart_of_local_noncollapse (G.metric 0) (G.connection 0) p
      (n := 3) (K := K) (δ := (1 / 8 : ℝ)) (v := v)
      (r := (1 / 8 : ℝ)) (S := (1 : ℝ)) (R := R) (ρ := rho)
      (by norm_num) hK.le (by norm_num) hv (by norm_num) (by norm_num)
      rfl hrhoR hcomparison hcompact
      (fun x _ => hcurv 0 (by norm_num) x) hvolume p hp
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi (Metric.ball 0 R) := by
    simpa only [hsourcePhi] using Phi.contMDiffOn
  have hnormalized : ∀ v w, (G.metric 0).pullbackCoefficients Phi 0 v w = inner ℝ v w :=
    (G.metric 0).pullbackCoefficients_zero_of_orthonormal p
      (hsmooth.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)))
      hzero hd hL
  have hspeed : ∀ w ∈ Metric.ball 0 R, ∀ s ∈ Icc (0 : ℝ) 1,
      (G.metric 0).tangentNorm (Phi (s • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun a : ℝ => Phi (a • w)) s 1) = ‖w‖ := by
    intro w hw s hs
    exact (G.metric 0).tangentNorm_radial_of_normalized_exponential p L
      hzero hL hd hgeo hw hs
  refine ⟨hcurv, L, Phi, hsourcePhi, htargetPhi, hzero, hL, hd,
    hnormalized, hgeo, hspeed, hdist, hell, ?_, ?_⟩
  · intro m s hs x hx
    apply hderiv m s hs (Phi x)
    have hmem : Phi x ∈ (G.metric 0).ball p R := by
      rw [← htargetPhi]
      exact Phi.map_source (hsourcePhi.symm ▸ hx)
    exact hmem.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hRsmall, hbuffer]))
  · rw [hzero]
    exact GeneralizedStrongNeck.rescaled_half_scalar_at_center S H

end PoincareConjecture.M28
