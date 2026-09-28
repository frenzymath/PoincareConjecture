import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Calabi







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}

private lemma finite_radial_parameter_open (w : EuclideanSpace ℝ (Fin (m + 1))) (R : ℝ) :
    IsOpen {s : ℝ | s • w ∈ Metric.ball 0 R} :=
  Metric.isOpen_ball.preimage (continuous_id.smul continuous_const)

private lemma finite_radial_parameter_contains {w : EuclideanSpace ℝ (Fin (m + 1))}
    {R : ℝ} (hw : w ∈ Metric.ball 0 R) :
    Icc (0 : ℝ) 1 ⊆ {s : ℝ | s • w ∈ Metric.ball 0 R} := by
  intro s hs
  rw [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg hs.1]
  exact (mul_le_of_le_one_left (norm_nonneg w) hs.2).trans_lt
    (by simpa only [Metric.mem_ball, dist_zero_right] using hw)

private lemma finite_hasDerivAt_radial_length
    (F : RicciFlow (m + 1) M J) {t : ℝ} (ht : t ∈ interior J)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R : ℝ}
    {w : EuclideanSpace ℝ (Fin (m + 1))} (hw : w ∈ Metric.ball 0 R) (hw0 : w ≠ 0)
    (hgeo : (F.metric t).IsGeodesicOn (fun s : ℝ => e (s • w))
      {s : ℝ | s • w ∈ Metric.ball 0 R})
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1,
      (F.metric t).tangentNorm (e (s • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun u : ℝ => e (u • w)) s 1) = ‖w‖) :
    HasDerivAt (fun s => ∫ u in (0 : ℝ)..1,
      (F.metric s).tangentNorm (e (u • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • w)) u 1))
      (-(∫ u in (0 : ℝ)..1, (F.connection t).ricci (e (u • w))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • w)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • w)) u 1) / ‖w‖)) t := by
  have h := F.hasDerivAt_integral_speed zero_le_one (finite_radial_parameter_open w R)
    (finite_radial_parameter_contains hw)
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



theorem exists_distance_spacetime_upper_support_of_finite
    (F : RicciFlow (m + 1) M J)
    {t r Λ scale : ℝ} (ht : t ∈ interior J) (hm : 0 < m)
    (hcomplete : MetricComplete (F.metric t))
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ (F.connection t).ricci y v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hx : x ∈ (F.metric t).ball p r) (hpx : p ≠ x)
    (hupper : ∀ y ∈ (F.metric t).ball p r,
      ∀ v : TangentSpace (𝓡 (m + 1)) y,
      (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v) :
    ∃ (U : Set M) (rho : ℝ → M → ℝ), IsOpen U ∧ x ∈ U ∧
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
  have hfinite : (F.metric t).edist p x ≠ ⊤ := by
    exact ne_top_of_lt (show (F.metric t).edist p x < ENNReal.ofReal r from hx)
  obtain ⟨R, e, w, v, B, hgeo, hspeed, hw, hw0, hwp, hvB, hBU, heB, hvx,
    hzero, hBnorm, hsum, hsegments, hgrad, hlap⟩ :=
    exists_calabi_radial_data_of_finite (F.metric t) (F.connection t) hm hcomplete hRic
      p x hx hpx hfinite
  have hxB : x ∈ B.target := by rw [← hvx, heB hvB]; exact B.map_source hvB
  have hinvx : B.symm x = v := by rw [← hvx, heB hvB, B.left_inv hvB]
  have hv0 : v ≠ 0 := by simpa only [hinvx] using hzero x hxB
  have hv : v ∈ Metric.ball 0 R := hBU hvB
  let len : ℝ → EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun s z =>
    ∫ u in (0 : ℝ)..1, (F.metric s).tangentNorm (e (u • z))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1)
  let rho : ℝ → M → ℝ := fun s y => len s w + len s (B.symm y)
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
      (hz0 : z ≠ 0) : HasDerivAt (fun s => len s z)
        (-(∫ u in (0 : ℝ)..1, (F.connection t).ricci (e (u • z))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun a : ℝ => e (a • z)) u 1) / ‖z‖)) t :=
    finite_hasDerivAt_radial_length F ht hz hz0 (hgeo z hz) (hspeed z hz)
  have htimeLower (z : EuclideanSpace ℝ (Fin (m + 1)))
      (hz : z ∈ Metric.ball 0 R) (hz0 : z ≠ 0) (hzseg : z ∈ ({w, v} : Set _)) :
      -(2 * ((m + 1 : ℕ) : ℝ) * scale + 4 * Λ / scale) ≤ deriv (fun s => len s z) t := by
    rw [(htime z hz hz0).deriv]
    apply neg_le_neg
    apply (F.connection t).integral_ricci_div_speed_le_of_minimizing
      (finite_radial_parameter_open z R) (finite_radial_parameter_contains hz) (hgeo z hz)
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
  · calc
      rho t x = ‖w‖ + ‖B.symm x‖ := hsliceeq hxB
      _ = ‖w‖ + ‖v‖ := by rw [hinvx]
      _ = _ := hsum
  · intro s y hy
    have hdist (z : EuclideanSpace ℝ (Fin (m + 1))) (hz : z ∈ Metric.ball 0 R) :
        ((F.metric s).edist (e 0) (e z)).toReal ≤ len s z := by
      have h := (F.metric s).toReal_edist_le_integral_speed zero_le_one
        (finite_radial_parameter_open z R) (finite_radial_parameter_contains hz)
        (fun u hu => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn
          (hgeo z hz) hu).contMDiffWithinAt)
      simpa only [zero_smul, one_smul] using h
    have hfirst := hdist w hw
    have hsecond := hdist (B.symm y) (hBU (B.map_target hy))
    have hγw : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (m + 1)) 1
        (fun u : ℝ => e (u • w)) (Icc 0 1) := fun u hu =>
        ((Conjugate.Realization.contMDiffAt_of_isGeodesicOn (hgeo w hw)
          (finite_radial_parameter_contains hw hu)).of_le (by norm_num)).contMDiffWithinAt
    have hγy : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (m + 1)) 1
        (fun u : ℝ => e (u • (B.symm y))) (Icc 0 1) := fun u hu =>
        ((Conjugate.Realization.contMDiffAt_of_isGeodesicOn
          (hgeo (B.symm y) (hBU (B.map_target hy)))
          (finite_radial_parameter_contains (hBU (B.map_target hy)) hu)).of_le
            (by norm_num)).contMDiffWithinAt
    have hfirstE := (F.metric s).edist_le_ofReal_integral_speed zero_le_one hγw
      ((PoincareConjecture.RiemannianMetric.continuousOn_speed_of_contMDiffOn (F.metric s)
        (finite_radial_parameter_open w R)
        (fun u hu => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn
          (hgeo w hw) hu).contMDiffWithinAt)).mono (finite_radial_parameter_contains hw))
    have hsecondE := (F.metric s).edist_le_ofReal_integral_speed zero_le_one hγy
      ((PoincareConjecture.RiemannianMetric.continuousOn_speed_of_contMDiffOn (F.metric s)
        (finite_radial_parameter_open (B.symm y) R)
        (fun u hu => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn
          (hgeo (B.symm y) (hBU (B.map_target hy))) hu).contMDiffWithinAt)).mono
        (finite_radial_parameter_contains (hBU (B.map_target hy))))
    rw [hwp] at hfirst
    rw [heB (B.map_target hy), B.right_inv hy] at hsecond
    simp only [zero_smul, one_smul] at hfirstE hsecondE
    rw [hwp] at hfirstE
    rw [heB (B.map_target hy), B.right_inv hy] at hsecondE
    have hfirst_fin : (F.metric s).edist (e 0) p ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by
        exact hfirstE)
    have hsecond_fin : (F.metric s).edist (e 0) y ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsecondE
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    have htriangle := Manifold.riemannianEDist_triangle (I := 𝓡 (m + 1))
      (x := p) (y := e 0) (z := y)
    change (F.metric s).edist p y ≤ (F.metric s).edist p (e 0) +
      (F.metric s).edist (e 0) y at htriangle
    have hcomm : (F.metric s).edist p (e 0) = (F.metric s).edist (e 0) p :=
      Manifold.riemannianEDist_comm
    have hfirst' : ((F.metric s).edist p (e 0)).toReal ≤ len s w := by
      simpa only [hcomm] using hfirst
    have hfirst_fin' : (F.metric s).edist p (e 0) ≠ ⊤ := by
      simpa only [hcomm] using hfirst_fin
    have hsum_fin : (F.metric s).edist p (e 0) +
        (F.metric s).edist (e 0) y ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hfirst_fin', hsecond_fin⟩
    have hreal := ENNReal.toReal_mono hsum_fin htriangle
    rw [ENNReal.toReal_add hfirst_fin' hsecond_fin] at hreal
    dsimp only [rho]
    exact hreal.trans (add_le_add hfirst' hsecond)
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
