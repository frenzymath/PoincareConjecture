import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.UniformFamilySpeedJetBounds
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.EmbeddedFirstJetTimeBounds
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SpeedGradientTimeBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceCurvatureTime
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessAmbientAcceleration
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_uniform_embedded_threeJet_time_modulus [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U)
    (hrhoe : ∀ p, rho (e p) = p)
    {tau R nu0 V0 B0 : ℝ} (hat : a < tau) (htb : tau < b)
    (hR : 0 ≤ R) (hnu0 : 0 < nu0) (hV0 : 0 ≤ V0) (hB0 : 0 ≤ B0) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ eta : ℝ, 0 < eta ∧
      ∀ c : ℝ → ℝ → M, M62ShrinkingCurve F c →
        (∀ x, nu0 ≤ curveSpeed F c a x ∧ curveSpeed F c a x ≤ V0) →
        (∀ x, |deriv (curveSpeed F c a) x| ≤ B0) →
        (∀ t ∈ Ioo a b, ∀ x, m62CurvatureSquared F c t x ≤ R) →
        ∀ s ∈ Icc tau b, ∀ t ∈ Icc tau b, |s - t| < eta → ∀ x : ℝ,
          ‖e (c x s) - e (c x t)‖ < epsilon ∧
          ‖deriv (fun y => e (c y s)) x - deriv (fun y => e (c y t)) x‖ < epsilon ∧
          ‖deriv (deriv (fun y => e (c y s))) x -
              deriv (deriv (fun y => e (c y t))) x‖ < epsilon := by
  classical
  have hab : a < b := hat.trans htb
  obtain ⟨K, J, m, V, G, J1, J2, hK, hBounds, hJ, hm, hV, hG, hJ1, hJ2, hcommon⟩ :=
    exists_uniform_c2_speed_jet_bounds F hcompact hat htb hR hnu0 hV0 hB0
  obtain ⟨E1, _E2, _E3, ⟨hE1, _hE2, _hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  obtain ⟨C01, hC01, h01⟩ := exists_uniform_embedded_firstJet_time_lipschitz F hcompact he
    (Real.sqrt_nonneg R) hV hJ1
  obtain ⟨CH, hCH, hHtime⟩ := exists_uniform_embeddedCurvature_time_lipschitz F hcompact hab he
    hK hK hK hBounds (Real.sqrt_nonneg R) hJ1 hJ2
  let Cv := (K + R) * V
  let Cg := (K + R) * V * (G / m) +
    V ^ 2 * (K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * J1)
  have hCv : 0 ≤ Cv := mul_nonneg (add_nonneg hK hR) hV
  have hCg : 0 ≤ Cg := by dsimp only [Cg]; positivity
  let L := 1 + C01 + CH + Cv + Cg
  have hL : 0 < L := by dsimp only [L]; linarith only [hC01, hCH, hCv, hCg]
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hC01, hCH, hCv, hCg]
  have hL01 : C01 ≤ L := by dsimp only [L]; linarith only [hCH, hCv, hCg]
  have hLH : CH ≤ L := by dsimp only [L]; linarith only [hC01, hCv, hCg]
  have hLv : Cv ≤ L := by dsimp only [L]; linarith only [hC01, hCH, hCg]
  have hLg : Cg ≤ L := by dsimp only [L]; linarith only [hC01, hCH, hCv]
  let X := ((ℝ × W) × W) × (W × (ℝ × ℝ))
  let D : Set X := ((Icc tau b ×ˢ range e) ×ˢ closedBall (0 : W) (E1 * V)) ×ˢ
    (closedBall (0 : W) (E1 * Real.sqrt R) ×ˢ (Icc m V ×ˢ Icc (-G) G))
  have hecompact : IsCompact (range e) := by
    simpa only [image_univ] using hcompact.image he.continuous
  have hD : IsCompact D :=
    ((isCompact_Icc.prod hecompact).prod (isCompact_closedBall _ _)).prod
      ((isCompact_closedBall _ _).prod (isCompact_Icc.prod isCompact_Icc))
  let B : (ℝ × W) × W → W := fun z => coordinateHessian (F.connection z.1.1) e (rho z.1.2)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1.2 z.2) (mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1.2 z.2)
  let Phi : X → W := fun z => B z.1 + z.2.2.1 ^ 2 • z.2.1 +
    (z.2.2.2 / z.2.2.1) • z.1.2
  have hBC : ContinuousOn B ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_pullback_contDiffOn F he hU hrho).continuousOn
  have hp : Continuous (fun z : X => z.1.2) := continuous_fst.snd
  have hh : Continuous (fun z : X => z.2.1) := continuous_snd.fst
  have hv : Continuous (fun z : X => z.2.2.1) := continuous_snd.snd.fst
  have hg : Continuous (fun z : X => z.2.2.2) := continuous_snd.snd.snd
  have hBinput : ContinuousOn (fun z : X => B z.1) D :=
    hBC.comp continuous_fst.continuousOn (fun z hz =>
      ⟨⟨⟨hat.le.trans hz.1.1.1.1, hz.1.1.1.2⟩, heU hz.1.1.2⟩, mem_univ _⟩)
  have hPhi : ContinuousOn Phi D :=
    (hBinput.add ((hv.pow 2).continuousOn.smul hh.continuousOn)).add
      ((hg.continuousOn.div hv.continuousOn
        (fun z hz => (hm.trans_le hz.2.2.1.1).ne')).smul hp.continuousOn)
  have hUC := Metric.uniformContinuousOn_iff.mp (hD.uniformContinuousOn_of_continuous hPhi)
  have hleft := (smooth_retraction_differentials he hU heU hrho hrhoe).2.2
  have hBval (r : ℝ) (p : M) (Y : TangentSpace (𝓡 n) p) :
      B ((r, e p), (mfderiv (𝓡 n) 𝓘(ℝ, W) e p Y : W)) =
        coordinateHessian (F.connection r) e p Y Y := by
    dsimp only [B]
    rw [hleft, hrhoe]
  intro epsilon hepsilon
  obtain ⟨d, hd, hPhiMod⟩ := hUC epsilon hepsilon
  refine ⟨min epsilon d / L, div_pos (lt_min hepsilon hd) hL, ?_⟩
  intro c hc hinitial hgrad0 hcurv s hs t ht hst x
  obtain ⟨hglobalJet, hspeedGrad, hlater⟩ := hcommon c hc hinitial hgrad0 hcurv
  have hspeed (r : ℝ) (hr : r ∈ Icc a b) (y : ℝ) :
      m ≤ curveSpeed F c r y ∧ curveSpeed F c r y ≤ V :=
    ⟨(hspeedGrad r hr y).1, (hspeedGrad r hr y).2.1⟩
  have hgrad (r : ℝ) (hr : r ∈ Icc a b) (y : ℝ) :
      |deriv (curveSpeed F c r) y| ≤ G := (hspeedGrad r hr y).2.2
  have hclosed (r : ℝ) (hr : r ∈ Icc tau b) : r ∈ Icc a b :=
    ⟨hat.le.trans hr.1, hr.2⟩
  have hqclosed (r : ℝ) (hr : r ∈ Icc a b) (y : ℝ) :
      m62CurvatureSquared F c r y ≤ R := by
    have hcont : ContinuousOn (fun z => m62CurvatureSquared F c z y) (Icc a b) :=
      (curvatureSquared_continuousOn F c hc).comp
        (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨mem_univ _, hz⟩)
    apply le_on_closure (fun z hz => hcurv z hz y)
    · simpa only [closure_Ioo hab.ne] using hcont
    · exact continuousOn_const
    · simpa only [closure_Ioo hab.ne] using hr
  have hk (r : ℝ) (hr : r ∈ Icc a b) (y : ℝ) : m62Curvature F c r y ≤ Real.sqrt R :=
    Real.sqrt_le_sqrt (hqclosed r hr y)
  have hkLater (r : ℝ) (hr : r ∈ Ioo tau b) (y : ℝ) :
      m62Curvature F c r y ≤ Real.sqrt R := hk r ⟨hat.le.trans hr.1.le, hr.2.le⟩ y
  have h01bound := h01 c hc tau b hat.le htb.le le_rfl hkLater
    (fun r hr y => (hspeed r ⟨hat.le.trans hr.1.le, hr.2.le⟩ y).2)
    (fun r hr y => (hlater r hr y).1) s hs t ht x
  have hHbound := hHtime c hc tau b hat.le htb.le le_rfl hkLater
    (fun r hr y => (hlater r hr y).1) (fun r hr y => (hlater r hr y).2) s hs t ht x
  have hgBound : |deriv (curveSpeed F c s) x - deriv (curveSpeed F c t) x| ≤ Cg * |s - t| :=
    curveSpeed_spatial_derivative_time_lipschitz F c hc hK hR hJ hm hV hG hJ1 hBounds
      hcurv hglobalJet hspeed hgrad hat.le htb.le le_rfl (fun r hr y => (hlater r hr y).1)
      s hs t ht x
  have hvBound : |curveSpeed F c s x - curveSpeed F c t x| ≤ Cv * |s - t| := by
    have hder (r : ℝ) (hr : r ∈ Ioo tau b) :
        DifferentiableAt ℝ (fun z => curveSpeed F c z x) r ∧
          ‖deriv (fun z => curveSpeed F c z x) r‖ ≤ Cv := by
      have hr' : r ∈ Ioo a b := ⟨hat.trans hr.1, hr.2⟩
      have hrc := Ioo_subset_Icc_self hr'
      have hdv := hasDerivAt_speed F c hc hr' x
      have hunit := (unitTangent_norm F c hc hrc x).le
      have hric : |m62TangentRicci F c r x| ≤ K :=
        hBounds.ricci r hrc (c x r) (spatialUnitTangent F c r x)
          (spatialUnitTangent F c r x) hunit hunit
      have hco : |m62TangentRicci F c r x + m62CurvatureSquared F c r x| ≤ K + R := by
        calc
          _ ≤ |m62TangentRicci F c r x| + |m62CurvatureSquared F c r x| := abs_add_le _ _
          _ ≤ K + R := add_le_add hric (by
            rw [abs_of_nonneg (curvatureSquared_nonneg F c r x)]
            exact hcurv r hr' x)
      refine ⟨hdv.differentiableAt, ?_⟩
      rw [hdv.deriv, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_nonneg (speed_nonneg F c r x)]
      exact mul_le_mul hco (hspeed r hrc x).2 (speed_nonneg F c r x) (add_nonneg hK hR)
    have hcont : ContinuousOn (fun r => curveSpeed F c r x) (Icc tau b) :=
      (speed_continuousOn F c hc).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨mem_univ _, hclosed r hr⟩)
    have hopen : LipschitzOnWith ⟨Cv, hCv⟩ (fun r => curveSpeed F c r x) (Ioo tau b) :=
      (convex_Ioo tau b).lipschitzOnWith_of_nnnorm_deriv_le
        (fun r hr => (hder r hr).1) (fun r hr => (hder r hr).2)
    have hcont' : ContinuousOn (fun r => curveSpeed F c r x) (closure (Ioo tau b)) := by
      simpa only [closure_Ioo htb.ne] using hcont
    have hclose : LipschitzOnWith ⟨Cv, hCv⟩ (fun r => curveSpeed F c r x) (Icc tau b) := by
      simpa only [closure_Ioo htb.ne] using LipschitzOnWith.closure hcont' hopen
    simpa only [Real.dist_eq] using! hclose.dist_le_mul s hs t ht
  let P : ℝ → W := fun r => deriv (fun y => e (c y r)) x
  let H : ℝ → W := fun r =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x r) (m62CurvatureVector F c r x)
  let input : ℝ → X := fun r =>
    (((r, e (c x r)), P r), (H r, (curveSpeed F c r x, deriv (curveSpeed F c r) x)))
  have hdata := c2ShrinkingCurve_embedded_closed_data (m63C2_of_m62 hc) he
  have hP (r : ℝ) (hr : r ∈ Icc a b) : P r =
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x r) (curveVelocity (fun y => c y r) x) : W) :=
    (hdata.2.1 r hr x).deriv
  have hin (r : ℝ) (hr : r ∈ Icc tau b) : input r ∈ D := by
    have hrc := hclosed r hr
    have hPb : ‖P r‖ ≤ E1 * V := by
      rw [hP r hrc]
      exact ((hE r hrc (c x r) (curveVelocity (fun y => c y r) x) 0 0).1).trans
        (mul_le_mul_of_nonneg_left (hspeed r hrc x).2 hE1)
    have hHb : ‖H r‖ ≤ E1 * Real.sqrt R :=
      ((hE r hrc (c x r) (m62CurvatureVector F c r x) 0 0).1).trans
        (mul_le_mul_of_nonneg_left (hk r hrc x) hE1)
    exact ⟨⟨⟨hr, mem_range_self _⟩, by simpa only [mem_closedBall, dist_zero_right] using hPb⟩,
      ⟨by simpa only [mem_closedBall, dist_zero_right] using hHb,
        ⟨hspeed r hrc x, abs_le.mp (hgrad r hrc x)⟩⟩⟩
  have hsecond (r : ℝ) (hr : r ∈ Icc tau b) :
      deriv (deriv (fun y => e (c y r))) x = Phi (input r) := by
    have hrc := hclosed r hr
    have hne := (speed_pos F c hc hrc x).ne'
    have hBpoint : B ((r, e (c x r)), P r) = coordinateHessian (F.connection r) e (c x r)
        (curveVelocity (fun y => c y r) x) (curveVelocity (fun y => c y r) x) := by
      rw [hP r hrc]
      exact hBval r (c x r) _
    have hcurv := embedded_curvature_eq_acceleration_sub_tangent F he c
      (hc.spatial_regular r hrc) (hc.immersed r hrc) x
    rw [← hBpoint] at hcurv
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : W => z i) hcurv
    simp only [Phi, input, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hi
    change _ = B ((r, e (c x r)), P r) i + curveSpeed F c r x ^ 2 * H r i +
      (deriv (curveSpeed F c r) x / curveSpeed F c r x) * P r i
    change H r i = (curveSpeed F c r x ^ 2)⁻¹ *
      (_ - B ((r, e (c x r)), P r) i) -
      (deriv (curveSpeed F c r) x / curveSpeed F c r x ^ 3) * P r i at hi
    field_simp [hne] at hi ⊢
    nlinarith only [hi]
  have hinputBound : dist (input s) (input t) ≤ L * |s - t| := by
    have habs := abs_nonneg (s - t)
    have htime : |s - t| ≤ L * |s - t| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hL1 habs
    have hposition := h01bound.1.trans (mul_le_mul_of_nonneg_right hL01 habs)
    have hfirst := h01bound.2.trans (mul_le_mul_of_nonneg_right hL01 habs)
    have hcurvature := hHbound.trans (mul_le_mul_of_nonneg_right hLH habs)
    have hspeedTime := hvBound.trans (mul_le_mul_of_nonneg_right hLv habs)
    have hgradient := hgBound.trans (mul_le_mul_of_nonneg_right hLg habs)
    simp only [input]
    exact max_le (max_le (max_le htime hposition) hfirst)
      (max_le hcurvature (max_le hspeedTime hgradient))
  have hsmall : L * |s - t| < min epsilon d := by
    simpa only [mul_comm] using (lt_div_iff₀ hL).mp hst
  have hsmallE := hsmall.trans_le (min_le_left _ _)
  have hsmallD := hsmall.trans_le (min_le_right _ _)
  refine ⟨(h01bound.1.trans (mul_le_mul_of_nonneg_right hL01 (abs_nonneg _))).trans_lt hsmallE,
    (h01bound.2.trans (mul_le_mul_of_nonneg_right hL01 (abs_nonneg _))).trans_lt hsmallE, ?_⟩
  rw [hsecond s hs, hsecond t ht]
  simpa only [dist_eq_norm] using hPhiMod (input s) (hin s hs) (input t) (hin t ht)
    (hinputBound.trans_lt hsmallD)

end PoincareConjecture.M63
