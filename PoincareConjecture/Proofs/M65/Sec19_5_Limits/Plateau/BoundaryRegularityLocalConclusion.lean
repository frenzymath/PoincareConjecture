import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHeinzGeometry
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHeinzC1
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHeinzChart










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

open M65Euler

set_option maxHeartbeats 1800000 in




theorem weakDisk_boundary_local_contMDiff
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
    {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {gamma : LoopCircle → M} (hgamma : Continuous gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e gamma) (hmin : F.MinimizesEnergy g) (hconf : F.Conformal g)
    {f : LoopPlane → M} (hf : M65InteriorDiskRepresentative connection F f)
    {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ (r : ℝ) (q : LoopPlane → M), 0 < r ∧
      ContMDiffOn (𝓡 2) (𝓡 3) 1 q (closedBall 0 r ∩ {z | 0 ≤ z 1}) ∧
      EqOn q (f ∘ diskBoundaryCoordinate p) (ball 0 r ∩ {z | 0 < z 1}) ∧
      ∀ t ∈ Icc (-r) r, q (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        gamma (F.parameter (boundaryCirclePoint hp t)) := by
  classical
  obtain ⟨Q, R, alpha, B, hR, hRQ, ha, _ha1, hB, Y, hYv, _hYd, hdecay⟩ :=
    weakDisk_exists_boundary_full_energy_decay g he hinj hemb compact hgamma hsmooth hregular
      F hmin hp
  obtain ⟨r0, beta0, H0, q, hr0, hb0, _hb01, hH0, hqc, hqAE, hholder, htrace, hqf, hqs⟩ :=
    weakDisk_boundary_representative_matches_interior g connection he hinj hemb compact
      hgamma hsmooth hregular F hmin hf hp
  obtain ⟨C, b, T, hC, hCreg, hb, hbzero, hT, hlift⟩ :=
    continuous_boundary_parameter_lift gamma hsmooth hregular F.parameter hp
  let a := min (r0 / 2) (min (Q / 2) (T / 2))
  have hQ : 0 < Q := hR.trans hRQ
  have hapos : 0 < a := lt_min (half_pos hr0) (lt_min (half_pos hQ) (half_pos hT))
  have har0 : a ≤ r0 := (min_le_left _ _).trans (by linarith)
  have haQ : a < Q := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have haT : a ≤ T := ((min_le_right _ _).trans (min_le_right _ _)).trans (by linarith)
  let Ya := restrict_map Y (ball_subset_ball haQ.le)
  have hqYa : q =ᵐ[volume.restrict (ball (0 : LoopPlane) a)] Ya.value := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (ball_subset_closedBall.trans (closedBall_subset_closedBall har0)) hqAE] with z hz
    exact hz.trans (hYv z).symm
  have htraceC : ∀ t ∈ Icc (-a) a,
      q (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) = C (b t) := by
    intro t ht
    exact (htrace t (Icc_subset_Icc (neg_le_neg har0) har0 ht)).trans
      (hlift t (Icc_subset_Icc (neg_le_neg haT) haT ht)).symm
  have hq0 : q 0 = C 0 := by
    simpa only [zero_smul, hbzero] using htraceC 0 ⟨by linarith, hapos.le⟩
  obtain ⟨j, E, r1, A, L, hr1, hr1a, hE, hEs, _hA, hAL, hAD, hqcsrc, hEcsrc,
      X, hXv, hXd, hXe, hXc, hXs, haxis⟩ :=
    continuous_boundary_straight_weak_chart e he hinj hapos Ya
      (hqc.mono (closedBall_subset_closedBall har0)) hqYa
      (hqs.mono (inter_subset_inter_left _ (ball_subset_ball har0)))
      C hC 0 hCreg b hb hbzero htraceC
  rw [← hq0] at hqcsrc hEcsrc hXe
  obtain ⟨gE, DE, r2, hr2, _hr2r0, _hsrc2, hHc, hHs, hHeq, hHconf⟩ :=
    continuous_boundary_plane_geometry connection hr0 hf.smooth hf.harmonic
      (m65Attainment_conformal F he hinj hf hconf) hqc hp hqf
  let c := chartAt LoopAmbient (q 0)
  let H := c ∘ q
  let s := min (1 / 2 : ℝ) (min (r1 / 2) (min (r2 / 2) (R / 2)))
  have hs : 0 < s := lt_min (by norm_num)
    (lt_min (half_pos hr1) (lt_min (half_pos hr2) (half_pos hR)))
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hsr1 : s < r1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hsr2 : s < r2 := ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (by linarith)
  have hsR : s ≤ R / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hsr0 : s ≤ r0 := hsr1.le.trans (hr1a.le.trans har0)
  let U := ball (0 : LoopPlane) s ∩ {z | 0 < z 1}
  let K := closedBall (0 : LoopPlane) s
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hUK : U ⊆ K := inter_subset_left.trans ball_subset_closedBall
  have hK : IsCompact K := isCompact_closedBall _ _
  have hHcK : ContinuousOn H K := hHc.mono (closedBall_subset_closedBall hsr2.le)
  have hHsU : ContDiffOn ℝ ∞ H U :=
    hHs.mono (inter_subset_inter_left _ (ball_subset_ball hsr2.le))
  have hsource : MapsTo H K E.source :=
    hEcsrc.mono_left (closedBall_subset_closedBall hsr1.le)
  have hdiag := fun z hz => (hHconf z
    (inter_subset_inter_left _ (ball_subset_ball hsr2.le) hz)).1
  have hmixed := fun z hz => (hHconf z
    (inter_subset_inter_left _ (ball_subset_ball hsr2.le) hz)).2
  obtain ⟨hGc, hGsymm, hGpos, hGdiag, hGmixed⟩ :=
    straight_metric_data gE hU hUK hK hHcK hHsU E hE hEs hsource hdiag hmixed
  obtain ⟨Cg, hCg, hgrowth⟩ := straight_harmonic_transverse_growth DE hU hHsU
    (hK.image_of_continuousOn hHcK) (fun z hz => mem_image_of_mem H (hUK hz))
    E hE hEs (by rintro _ ⟨z, hz, rfl⟩; exact hsource hz) j
    (fun z hz => hHeq z (inter_subset_inter_left _ (ball_subset_ball hsr2.le) hz))
    hdiag hmixed
  let Xs := restrict_map X (ball_subset_ball hsr1.le)
  have hnear (z : LoopPlane) (hz : z ∈ U) : Xs.value =ᶠ[𝓝 z] E ∘ H := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact hXe (closedBall_subset_closedBall hsr1.le (hUK hy))
  have hD (z : LoopPlane) (hz : z ∈ U) : fderiv ℝ Xs.value z = fderiv ℝ (E ∘ H) z :=
    (hnear z hz).fderiv_eq
  have hD2 (z : LoopPlane) (hz : z ∈ U) :
      fderiv ℝ (fderiv ℝ Xs.value) z = fderiv ℝ (fderiv ℝ (E ∘ H)) z :=
    (hnear z hz).fderiv.fderiv_eq
  let beta := min beta0 (alpha / 2)
  have hbeta : 0 < beta := lt_min hb0 (half_pos ha)
  have hbb : beta ≤ beta0 := min_le_left _ _
  have hba : 2 * beta ≤ alpha := by have := min_le_right beta0 (alpha / 2); linarith
  have hhold : ∀ x ∈ closedBall (0 : LoopPlane) (s / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (s / 2),
      ‖Xs.value z - Xs.value x‖ ≤ (L : ℝ) * H0 * dist z x ^ beta := by
    intro x hx z hz
    have hx0 := closedBall_subset_closedBall (show s / 2 ≤ r0 by linarith) hx
    have hz0 := closedBall_subset_closedBall (show s / 2 ≤ r0 by linarith) hz
    have hdist : dist z x ≤ 1 := by
      have hh := dist_triangle z (0 : LoopPlane) x
      rw [dist_zero_right, dist_zero_left] at hh
      have hxn := mem_closedBall_zero_iff.mp hx
      have hzn := mem_closedBall_zero_iff.mp hz
      linarith
    change ‖X.value z - X.value x‖ ≤ _
    rw [hXv, hXv]
    calc
      _ ≤ (L : ℝ) * ‖e (q z) - e (q x)‖ := hAL.norm_sub_le _ _
      _ ≤ (L : ℝ) * (H0 * dist z x ^ beta0) :=
        mul_le_mul_of_nonneg_left (hholder x hx0 z hz0) L.coe_nonneg
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' (dist_nonneg) hdist hbeta.le hbb) (by positivity)
  obtain ⟨ell, upper, hell, _hupper, hmetric⟩ :=
    m65EmbeddingMetric_uniform_bounds g e he hinj compact
  let Lambda := (L : ℝ) ^ 2 * (2 / ell) * B
  have hLambda : 0 ≤ Lambda := by dsimp only [Lambda]; positivity
  have henergy : ∀ x ∈ closedBall (0 : LoopPlane) (s / 4),
      ∀ r : ℝ, 0 < r → r ≤ s / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖Xs.derivative i z‖ ^ 2) ≤
        Lambda * r ^ (2 * beta) := by
    intro x hx r hr hrr
    have hsub : closedBall x r ⊆ ball (0 : LoopPlane) s := by
      apply closedBall_subset_ball'
      rw [dist_zero_right]
      have hxn := mem_closedBall_zero_iff.mp hx
      linarith
    have hsubQ : closedBall x r ⊆ ball (0 : LoopPlane) Q :=
      hsub.trans (ball_subset_ball (hsr1.le.trans (hr1a.le.trans haQ.le)))
    have hXI := integrable_finsetSum Finset.univ (fun i _ =>
      (Xs.derivative_memLp i _ (isCompact_closedBall _ _) hsub).norm.integrable_sq)
    have hYI := Y.energy_integrable g he hinj hemb compact _ (isCompact_closedBall _ _) hsubQ
    have hpoint (z : LoopPlane) : (∑ i : Fin 2, ‖Xs.derivative i z‖ ^ 2) ≤
        ((L : ℝ) ^ 2 * (2 / ell)) * m65EmbeddedEnergyDensity g e Y.value Y.derivative z := by
      have hsum : (∑ i : Fin 2, ‖Xs.derivative i z‖ ^ 2) ≤
          (L : ℝ) ^ 2 * ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        change ‖X.derivative i z‖ ^ 2 ≤ _
        rw [hXd]
        have hh := (ContinuousLinearMap.le_opNorm (fderiv ℝ A (e (q z)))
          (Y.derivative i z)).trans
            (mul_le_mul_of_nonneg_right (hAD _) (norm_nonneg _))
        simpa only [Ya, restrict_map, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
      have hbound := (m65EmbeddedEnergyDensity_bounds g e hmetric Y.value Y.derivative z).1
      have hequiv : (∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2) ≤
          (2 / ell) * m65EmbeddedEnergyDensity g e Y.value Y.derivative z := by
        apply (mul_le_mul_iff_right₀ (show 0 < ell / 2 by positivity)).mp
        calc
          _ ≤ m65EmbeddedEnergyDensity g e Y.value Y.derivative z := hbound
          _ = _ := by field_simp
      exact hsum.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hequiv (sq_nonneg (L : ℝ)))
    calc
      _ ≤ ∫ z in closedBall x r,
          ((L : ℝ) ^ 2 * (2 / ell)) * m65EmbeddedEnergyDensity g e Y.value Y.derivative z :=
        setIntegral_mono_on hXI (hYI.const_mul _) measurableSet_closedBall (fun z _ => hpoint z)
      _ = ((L : ℝ) ^ 2 * (2 / ell)) *
          ∫ z in closedBall x r, m65EmbeddedEnergyDensity g e Y.value Y.derivative z :=
        integral_const_mul _ _
      _ ≤ ((L : ℝ) ^ 2 * (2 / ell)) * (B * r ^ alpha) :=
        mul_le_mul_of_nonneg_left
          (hdecay x (closedBall_subset_closedBall (by linarith) hx) r hr (by linarith))
          (by positivity)
      _ ≤ Lambda * r ^ (2 * beta) := by
        dsimp only [Lambda]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' hr.le (by linarith) (by positivity) hba)
          (by positivity)
  have hzero : ∀ z ∈ closedBall (0 : LoopPlane) (s / 2), z 1 = 0 →
      ∀ k : Fin 3, k ≠ j → Xs.value z k = 0 := by
    intro z hz hz1 k hkj
    have hzn := mem_closedBall_zero_iff.mp hz
    have hz0 : |z 0| ≤ s / 2 := by
      have hh : |z 0| ≤ ‖z‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z 0
      exact hh.trans hzn
    have heq : z = z 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
      ext i; fin_cases i <;> simp [EuclideanSpace.basisFun_apply, hz1]
    change X.value z k = 0
    rw [heq, haxis (z 0) ⟨by linarith [(abs_le.mp hz0).1], by linarith [(abs_le.mp hz0).2]⟩]
    simp [EuclideanSpace.basisFun_apply, hkj]
  let G := fun z => gE.pullbackCoefficients E.symm (E (H z))
  have hhalfK : closedBall (0 : LoopPlane) (s / 2) ∩ {z | 0 ≤ z 1} ⊆ K :=
    inter_subset_left.trans (closedBall_subset_closedBall (by linarith))
  have hhalfU : ball (0 : LoopPlane) (s / 2) ∩ {z | 0 < z 1} ⊆ U :=
    inter_subset_inter_left _ (ball_subset_ball (by linarith))
  have hC1 : ContDiffOn ℝ 1 Xs.value
      (closedBall (0 : LoopPlane) (s / 256) ∩ {z | 0 ≤ z 1}) :=
    heinz_quadratic_contDiffOn hs Xs
      (hXs.mono (inter_subset_inter_left _ (ball_subset_ball hsr1.le)))
      (hXc.mono (closedBall_subset_closedBall (by linarith)))
      hCg (by positivity) hbeta hLambda hhold henergy j hzero G
      (hGc.mono hhalfK) (fun z hz => hGsymm z (hhalfK hz))
      (fun z hz => hGpos z (hhalfK hz))
      (fun z hz => by rw [hD z (hhalfU hz)]; exact hGdiag z (hhalfU hz))
      (fun z hz => by rw [hD z (hhalfU hz)]; exact hGmixed z (hhalfU hz))
      (fun z hz => by rw [hD z hz, hD2 z hz]; exact hgrowth z hz)
  let S := closedBall (0 : LoopPlane) (s / 256) ∩ {z | 0 ≤ z 1}
  have hSK1 : S ⊆ closedBall (0 : LoopPlane) r1 :=
    inter_subset_left.trans (closedBall_subset_closedBall (by linarith))
  have hmapE : MapsTo Xs.value S E.target := by
    intro z hz
    change X.value z ∈ E.target
    rw [hXe (hSK1 hz)]
    exact E.map_source (hEcsrc (hSK1 hz))
  have hbackE : EqOn (E.symm ∘ Xs.value) H S := by
    intro z hz
    change E.symm (X.value z) = H z
    rw [hXe (hSK1 hz)]
    exact E.left_inv (hEcsrc (hSK1 hz))
  have hmapc : MapsTo (E.symm ∘ Xs.value) S c.target := by
    intro z hz
    rw [hbackE hz]
    exact c.map_source (hqcsrc (hSK1 hz))
  have hback : EqOn (c.symm ∘ E.symm ∘ Xs.value) q S := by
    intro z hz
    change c.symm ((E.symm ∘ Xs.value) z) = q z
    rw [hbackE hz]
    exact c.left_inv (hqcsrc (hSK1 hz))
  have hqC1 : ContMDiffOn (𝓡 2) (𝓡 3) 1 q S :=
    (contMDiffOn_chart_symm.comp
      ((hEs.of_le (by simp)).contMDiffOn.comp hC1.contMDiffOn hmapE) hmapc).congr
        (fun z hz => (hback hz).symm)
  refine ⟨s / 256, q, by positivity, hqC1,
    hqf.mono (inter_subset_inter_left _ (ball_subset_ball (by linarith))), ?_⟩
  intro t ht
  exact htrace t (Icc_subset_Icc (by linarith) (by linarith) ht)

end PoincareConjecture.M65Boundary
