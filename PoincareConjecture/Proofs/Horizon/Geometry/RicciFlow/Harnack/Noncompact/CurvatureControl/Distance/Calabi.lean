import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.LengthVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.RicciIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.FiniteDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma radial_parameter_open (w : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    IsOpen {s : ℝ | s • w ∈ Metric.ball 0 R} :=
  Metric.isOpen_ball.preimage (continuous_id.smul continuous_const)

private lemma radial_parameter_contains {w : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hw : w ∈ Metric.ball 0 R) :
    Icc (0 : ℝ) 1 ⊆ {s : ℝ | s • w ∈ Metric.ball 0 R} := by
  intro s hs
  rw [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg hs.1]
  exact (mul_le_of_le_one_left (norm_nonneg w) hs.2).trans_lt
    (by simpa only [Metric.mem_ball, dist_zero_right] using hw)

private lemma hasDerivAt_radial_length
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ Metric.ball 0 R) (hw0 : w ≠ 0)
    (hgeo : (F.metric t).IsGeodesicOn (fun s : ℝ => e (s • w))
      {s : ℝ | s • w ∈ Metric.ball 0 R})
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1,
      (F.metric t).tangentNorm (e (s • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • w)) s 1) = ‖w‖) :
    HasDerivAt (fun s => ∫ u in (0 : ℝ)..1,
      (F.metric s).tangentNorm (e (u • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun a : ℝ => e (a • w)) u 1))
      (-(∫ u in (0 : ℝ)..1, (F.connection t).ricci (e (u • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun a : ℝ => e (a • w)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun a : ℝ => e (a • w)) u 1) / ‖w‖)) t := by
  have h := F.hasDerivAt_integral_speed zero_le_one (radial_parameter_open w R)
    (radial_parameter_contains hw)
    (fun s hs => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn
      hgeo hs).contMDiffWithinAt) ht (by
      intro s hs hzero
      have h := hspeed s hs
      rw [hzero, RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero] at h
      exact hw0 (norm_eq_zero.mp h.symm))
  apply h.congr_deriv
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  dsimp only
  rw [hspeed s hs]
  exact neg_div _ _

theorem exists_calabi_radial_data_of_finite
    {m : ℕ} {N : Type u} [TopologicalSpace N] [T3Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
    [IsManifold (𝓡 (m + 1)) ∞ N]
    (g : RiemannianMetric (m + 1) N) (D : LeviCivitaData g)
    (hm : 0 < m) (hc : MetricComplete g)
    (hRic : ∀ y : N, ∀ z : TangentSpace (𝓡 (m + 1)) y, 0 ≤ D.ricci y z z)
    (p x : N) {r : ℝ} (hx : x ∈ g.ball p r) (hpx : p ≠ x)
    (hfinite : g.edist p x ≠ ⊤) :
    ∃ (R : ℝ) (e : EuclideanSpace ℝ (Fin (m + 1)) → N)
      (w v : EuclideanSpace ℝ (Fin (m + 1)))
      (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1))) N),
      (∀ z ∈ Metric.ball 0 R, g.IsGeodesicOn (fun s : ℝ => e (s • z))
        {s : ℝ | s • z ∈ Metric.ball 0 R}) ∧
      (∀ z ∈ Metric.ball 0 R, ∀ s ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (e (s • z))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun u : ℝ => e (u • z)) s 1) = ‖z‖) ∧
      w ∈ Metric.ball 0 R ∧ w ≠ 0 ∧ e w = p ∧
      v ∈ B.source ∧ B.source ⊆ Metric.ball 0 R ∧ EqOn e B B.source ∧ e v = x ∧
      (∀ y ∈ B.target, B.symm y ≠ 0) ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (fun y => ‖B.symm y‖) B.target ∧
      ‖w‖ + ‖v‖ = (g.edist p x).toReal ∧
      (∀ z ∈ ({w, v} : Set (EuclideanSpace ℝ (Fin (m + 1)))),
        g.edist (e 0) (e z) = ENNReal.ofReal ‖z‖ ∧
        ∀ s ∈ Icc (0 : ℝ) 1, e (s • z) ∈ g.ball p r) ∧
      g.inner x (D.gradient (fun y => ‖B.symm y‖) x)
        (D.gradient (fun y => ‖B.symm y‖) x) = 1 ∧
      D.laplacian (fun y => ‖B.symm y‖) x ≤ 2 * (m : ℝ) / (g.edist p x).toReal := by
  have hdpos : 0 < (g.edist p x).toReal := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : N → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) N
    exact ENNReal.toReal_pos (edist_pos.mpr hpx).ne' hfinite
  let R := (g.edist p x).toReal + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete_of_finite hc hfinite
  obtain ⟨L, e, hL, he, he0, hed, hrad⟩ :=
    g.exists_orthonormal_radial_exponential_of_metricComplete hc (γ (1 / 4)) hR
  have hgeo := fun z hz => (hrad z hz).1
  have hspeed := fun z hz s hs => ((hrad z hz).2 s hs).1
  obtain ⟨v, hv, hnorm, hxv, hsplit, hmatch⟩ := g.exists_quarter_shifted_radial_vector
    hε hγ hγ0 hγ1 hmin (by dsimp [R]; linarith) L e hL he0 hed hgeo
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; positivity)
  have heorigin := he.contMDiffAt (Metric.isOpen_ball.mem_nhds
    (show (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ Metric.ball 0 R by simpa using hR))
  have hmetric := g.pullbackCoefficients_zero_of_orthonormal (γ (1 / 4)) heorigin he0 hed hL
  have hinit := RiemannianMetric.isInvertible_mfderiv_zero_of_chart_derivative
    (heorigin.mdifferentiableAt (by simp)) he0 hed
  let w := (-1 / 3 : ℝ) • v
  have hw : w ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖w‖ = (1 / 3 : ℝ) * ‖v‖ := by dsimp [w]; rw [norm_smul]; norm_num
      _ ≤ ‖v‖ := by nlinarith [norm_nonneg v]
      _ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hw0 : w ≠ 0 := smul_ne_zero (by norm_num) hv0
  have hback : e w = p := by
    have h := (hmatch (-1 / 3) (by norm_num)).self_of_nhds
    norm_num only [show (3 / 4 : ℝ) * (-1 / 3) + 1 / 4 = 0 by ring] at h
    simpa only [w, neg_div] using h.trans hγ0
  have hminback : g.edist (e ((-1 / 3 : ℝ) • v)) (e v) =
      ENNReal.ofReal ((4 / 3 : ℝ) * ‖v‖) := by
    rw [show e ((-1 / 3 : ℝ) • v) = p from hback, hxv, hnorm,
      show (4 / 3 : ℝ) * ((3 / 4) * (g.edist p x).toReal) = (g.edist p x).toReal by ring,
      ENNReal.ofReal_toReal hfinite]
  have hend := g.isInvertible_mfderiv_of_minimizing_backward_extension
    D he hinit hgeo hspeed hv hv0 hminback
  have htailmin : g.edist (γ (1 / 4)) (e v) = ENNReal.ofReal ‖v‖ := by
    have h := hmin (1 / 4) (by norm_num) 1 (by norm_num)
    rw [hγ1] at h
    rw [hxv, h, hnorm, show |(1 / 4 : ℝ) - 1| = 3 / 4 by norm_num,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4),
      ENNReal.ofReal_toReal hfinite]
  have hquarter_finite : g.edist p (γ (1 / 4)) ≠ ⊤ := by
    rw [← hγ0, hmin 0 (by norm_num) (1 / 4) (by norm_num)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  have hi := g.isInvertible_mfderiv_on_minimizing_segment D he he0 hinit
    hgeo hspeed hv hv0 htailmin hend
  obtain ⟨B, hvB, hBU, heB, hB, hBi, hzero, hBnorm⟩ :=
    RiemannianMetric.exists_smooth_radial_inverse_branch Metric.isOpen_ball he hv hv0 hend
  have hgauss := g.radial_gauss_identity D he hmetric hgeo
  have hgrad : g.inner x (D.gradient (fun y => ‖B.symm y‖) x)
      (D.gradient (fun y => ‖B.symm y‖) x) = 1 := by
    rw [← hxv]
    exact g.inner_gradient_inverse_branch D B heB hB hBi hvB hv0 (hgauss v hv)
  let θ := ‖v‖⁻¹ • v
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hθ : ‖θ‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hnormθ (s : ℝ) (hs : 0 ≤ s) : ‖s • θ‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg hs, hθ, mul_one]
  have hRv : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hsub : ∀ s ∈ Icc 0 ‖v‖, s • θ ∈ Metric.ball 0 R := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right, hnormθ s hs.1]
    exact hs.2.trans_lt hRv
  have hi' : ∀ s ∈ Icc 0 ‖v‖,
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ)).IsInvertible := by
    intro s hs
    have hst : s / ‖v‖ ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hn.le, (div_le_one hn).mpr hs.2⟩
    rw [show s • θ = (s / ‖v‖) • v by simp only [θ, smul_smul, div_eq_mul_inv]]
    exact hi (s / ‖v‖) hst
  obtain ⟨b, hnb, hbsub, hbi⟩ := RiemannianMetric.exists_regular_radial_extension
    Metric.isOpen_ball he θ hn.le hsub hi'
  have htθ : ‖v‖ • θ = v := by
    dsimp only [θ]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hgaussNear : ∀ᶠ y in 𝓝 (‖v‖ • θ), ∀ z,
      g.inner (e y) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y z) = inner ℝ y z := by
    rw [htθ]
    filter_upwards [Metric.isOpen_ball.mem_nhds hv] with y hy
    exact hgauss y hy
  have hlap := g.laplacian_inverse_branch_le_of_ricci D hm Metric.isOpen_ball
    (by simpa using hn.trans hRv) he hgeo hmetric θ hθ (hn.trans hnb)
    ⟨hn, hnb⟩ (k := 0) le_rfl hbsub (fun s hs => (hbi s hs).injective)
    (fun s _ z => by simpa using hRic (e (s • θ)) z) B heB hB hBi
    (by simpa only [htθ] using hvB) hgaussNear
  rw [htθ, hxv] at hlap
  have hwlen : ‖w‖ = (g.edist p (γ (1 / 4))).toReal := by
    dsimp only [w]
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hcurveball : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ g.ball p r := by
    intro s hs
    change g.edist p (γ s) < ENNReal.ofReal r
    rw [← hγ0, hmin 0 (by norm_num) s hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (zero_le : (0 : ℝ≥0∞) ≤ g.edist p x)
      (by simpa only [ENNReal.ofReal_le_one] using hs.2)).trans_lt hx
  refine ⟨R, e, w, v, B, hgeo, hspeed, hw, hw0, hback, hvB, hBU, heB, hxv,
    hzero, hBnorm, by rw [hwlen]; exact hsplit, ?_, hgrad, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · subst z
      refine ⟨?_, ?_⟩
      · rw [he0, hback, hwlen]
        have hcomm : g.edist p (γ (1 / 4)) = g.edist (γ (1 / 4)) p := by
          let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : N → Type _) :=
            ⟨g.toRiemannianMetric⟩
          exact Manifold.riemannianEDist_comm
        rw [hcomm]
        have hquarter_finite' := hquarter_finite
        rw [hcomm] at hquarter_finite'
        exact (ENNReal.ofReal_toReal hquarter_finite').symm
      · intro s hs
        have h := (hmatch (-s / 3) ⟨by linarith [hs.2], by linarith [hs.1]⟩).self_of_nhds
        dsimp only at h
        rw [show s • w = (-s / 3) • v by dsimp [w]; rw [smul_smul]; congr 1; ring, h]
        exact hcurveball _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
    · have hz' : z = v := mem_singleton_iff.mp hz
      subst z
      refine ⟨by rw [he0]; exact htailmin, ?_⟩
      intro s hs
      have h := (hmatch s ⟨by linarith [hs.1], hs.2⟩).self_of_nhds
      dsimp only at h
      rw [h]
      exact hcurveball _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · have hhalf : (g.edist p x).toReal / 2 ≤ ‖v‖ := by rw [hnorm]; linarith
    simpa using hlap.trans
      (RiemannianMetric.radius_comparison_of_half_le (k := 0) (Nat.cast_nonneg m) hdpos hhalf)

theorem exists_distance_spacetime_upper_support
    {m : ℕ} {N : Type u} [TopologicalSpace N] [T3Space N] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
    [IsManifold (𝓡 (m + 1)) ∞ N]
    {J : Set ℝ} (F : RicciFlow (m + 1) N J)
    {t r Λ scale : ℝ} (ht : t ∈ interior J) (hm : 0 < m)
    (hcomplete : MetricComplete (F.metric t))
    (hRic : ∀ y : N, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ (F.connection t).ricci y v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : N)
    (hx : x ∈ (F.metric t).ball p r) (hpx : p ≠ x)
    (hupper : ∀ y ∈ (F.metric t).ball p r,
      ∀ v : TangentSpace (𝓡 (m + 1)) y,
      (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v) :
    ∃ (U : Set N) (rho : ℝ → N → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (rho t) U ∧
      rho t x = ((F.metric t).edist p x).toReal ∧
      (∀ s : ℝ, ∀ y ∈ U, ((F.metric s).edist p y).toReal ≤ rho s y) ∧
      (F.metric t).inner x ((F.connection t).gradient (rho t) x)
        ((F.connection t).gradient (rho t) x) = 1 ∧
      (F.connection t).laplacian (rho t) x ≤
        2 * (m : ℝ) / ((F.metric t).edist p x).toReal ∧
      DifferentiableAt ℝ (fun s => rho s x) t ∧
      -(4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) ≤
        deriv (fun s => rho s x) t := by
  obtain ⟨R, e, w, v, B, hgeo, hspeed, hw, hw0, hwp, hvB, hBU, heB, hvx,
    hzero, hBnorm, hsum, hsegments, hgrad, hlap⟩ :=
    exists_calabi_radial_data_of_finite (F.metric t) (F.connection t) hm hcomplete hRic
      p x hx hpx ((F.metric t).edist_ne_top p x)
  have hxB : x ∈ B.target := by rw [← hvx, heB hvB]; exact B.map_source hvB
  have hinvx : B.symm x = v := by rw [← hvx, heB hvB, B.left_inv hvB]
  have hv0 : v ≠ 0 := by simpa only [hinvx] using hzero x hxB
  have hv : v ∈ Metric.ball 0 R := hBU hvB
  let len : ℝ → EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun s z =>
    ∫ u in (0 : ℝ)..1, (F.metric s).tangentNorm (e (u • z))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1)
  let rho : ℝ → N → ℝ := fun s y => len s w + len s (B.symm y)
  have hlen (z : EuclideanSpace ℝ (Fin (m + 1))) (hz : z ∈ Metric.ball 0 R) :
      len t z = ‖z‖ := by
    calc
      len t z = ∫ _u in (0 : ℝ)..1, ‖z‖ := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hspeed z hz u (by simpa only [uIcc_of_le zero_le_one] using hu)
      _ = ‖z‖ := by simp
  have hsliceeq : EqOn (rho t) (fun y => ‖w‖ + ‖B.symm y‖) B.target := by
    intro y hy
    dsimp only [rho]
    rw [hlen w hw, hlen (B.symm y) (hBU (B.map_target hy))]
  have hslicegerm : rho t =ᶠ[𝓝 x] (fun y => ‖w‖ + ‖B.symm y‖) :=
    hsliceeq.eventuallyEq_of_mem (B.open_target.mem_nhds hxB)
  have htime (z : EuclideanSpace ℝ (Fin (m + 1))) (hz : z ∈ Metric.ball 0 R)
      (hz0 : z ≠ 0) :
      HasDerivAt (fun s => len s z)
        (-(∫ u in (0 : ℝ)..1, (F.connection t).ricci (e (u • z))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1) / ‖z‖)) t :=
    hasDerivAt_radial_length F ht hz hz0 (hgeo z hz) (hspeed z hz)
  have htimeLower (z : EuclideanSpace ℝ (Fin (m + 1)))
      (hz : z ∈ Metric.ball 0 R) (hz0 : z ≠ 0) (hzseg : z ∈ ({w, v} : Set _)) :
      -(2 * ((m + 1 : ℕ) : ℝ) * scale + 4 * Λ / scale) ≤
        deriv (fun s => len s z) t := by
    rw [(htime z hz hz0).deriv]
    apply neg_le_neg
    apply (F.connection t).integral_ricci_div_speed_le_of_minimizing
      (radial_parameter_open z R) (radial_parameter_contains hz) (hgeo z hz)
      zero_le_one (norm_pos_iff.mpr hz0) (hspeed z hz)
      (by simpa only [zero_smul, one_smul, one_mul] using (hsegments z hzseg).1) hΛ hscale
    intro u hu
    have h := hupper (e (u • z)) ((hsegments z hzseg).2 u hu)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1)
    have hsq : (F.metric t).inner (e (u • z))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1) = ‖z‖ ^ 2 := by
      have hh := congrArg (fun c : ℝ => c ^ 2) (hspeed z hz u hu)
      dsimp only [RiemannianMetric.tangentNorm] at hh
      rw [Real.sq_sqrt] at hh
      · exact hh
      · by_cases hzv : mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1 = 0
        · simp [hzv]
        · exact ((F.metric t).pos _ _ hzv).le
    rwa [hsq] at h
  have hrad : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
      (fun y => ‖B.symm y‖) x := hBnorm.contMDiffAt (B.open_target.mem_nhds hxB)
  refine ⟨B.target, rho, B.open_target, hxB,
    (contMDiffOn_const.add hBnorm).congr hsliceeq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsliceeq hxB]
    dsimp only
    rw [hinvx]
    exact hsum
  · intro s y hy
    have hdist (z : EuclideanSpace ℝ (Fin (m + 1))) (hz : z ∈ Metric.ball 0 R) :
        ((F.metric s).edist (e 0) (e z)).toReal ≤ len s z := by
      have h := (F.metric s).toReal_edist_le_integral_speed zero_le_one
        (radial_parameter_open z R) (radial_parameter_contains hz)
        (fun u hu => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn (hgeo z hz) hu).contMDiffWithinAt)
      simpa only [zero_smul, one_smul] using h
    have hfirst := hdist w hw
    have hsecond := hdist (B.symm y) (hBU (B.map_target hy))
    rw [hwp] at hfirst
    rw [heB (B.map_target hy), B.right_inv hy] at hsecond
    have hcomm : (F.metric s).edist (e 0) p = (F.metric s).edist p (e 0) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : N → Type _) :=
        ⟨(F.metric s).toRiemannianMetric⟩
      exact Manifold.riemannianEDist_comm
    rw [hcomm] at hfirst
    exact ((F.metric s).toReal_edist_triangle p (e 0) y).trans (add_le_add hfirst hsecond)
  · have hgerm : (F.connection t).gradient (rho t) x =
        (F.connection t).gradient (fun y => ‖w‖ + ‖B.symm y‖) x := by
      unfold LeviCivitaData.gradient
      rw [Poincare.mvfderiv_eq_of_eventuallyEq hslicegerm]
    rw [hgerm, (F.connection t).gradient_const_add_at (hrad.mdifferentiableAt (by simp))]
    exact hgrad
  · rw [(F.connection t).laplacian_eq_of_eventuallyEq hslicegerm,
      (F.connection t).laplacian_const_add_at hrad]
    exact hlap
  · dsimp only [rho]
    rw [hinvx]
    exact (htime w hw hw0).differentiableAt.add (htime v hv hv0).differentiableAt
  · dsimp only [rho]
    rw [hinvx, deriv_fun_add (htime w hw hw0).differentiableAt
      (htime v hv hv0).differentiableAt]
    have hwlo := htimeLower w hw hw0 (by simp)
    have hvlo := htimeLower v hv hv0 (by simp)
    have htwice : -(4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) =
        -(2 * ((m + 1 : ℕ) : ℝ) * scale + 4 * Λ / scale) +
        -(2 * ((m + 1 : ℕ) : ℝ) * scale + 4 * Λ / scale) := by ring
    rw [htwice]
    exact add_le_add hwlo hvlo

end PoincareConjecture.RicciFlow
