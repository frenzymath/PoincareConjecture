import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryGeometry
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceBoundaryAlternative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff Manifold Bundle BigOperators

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

set_option maxHeartbeats 1600000 in

theorem boundary_branch_residual_holder (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
      (r : ℝ) (m : ℕ) (Q : ℂ → Fin 3 → ℂ), 0 < r ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ W, dbar (complexGradient H) z =
        harmonicMatrix DE H z (complexGradient H z)) ∧
      ContinuousOn Q K ∧ ContDiffOn ℝ 1 Q W ∧
      (∀ z ∈ K, Q z ≠ 0) ∧
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) ∧
      MemLp (fun z => fderiv ℝ Q z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ Q z Complex.I) 2 (volume.restrict W) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ w ∈ K,
        ‖Q z - Q w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  let f := S.disk.map
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let chart := chartAt LoopAmbient (f x)
  let G := chart ∘ f
  let P := e ∘ boundaryCoordinate p
  let H := G ∘ P
  have hp : ‖p‖ = 1 := by
    change ‖orthonormalBasisOneI.repr.symm x‖ = 1
    rw [orthonormalBasisOneI.repr.symm.norm_map, hx]
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  have hxK : x ∈ loopDiskSet := by
    rw [loopDiskSet, mem_closedBall_zero_iff, hx]
  obtain ⟨gE, DE, O, hO, hxO, hsource, hG, hGi, hmetric, heq⟩ :=
    exists_closedDisk_harmonic_chart connection S.interior_smooth S.boundary_regular S.harmonic hxK
  let xC : LoopCircle := ⟨x, hx⟩
  obtain ⟨s, hs⟩ := m65LoopAngular_continuous_surjective.2 (S.disk.reparameterization.map xC)
  have hsvalue : gamma (m65LoopAngular s) = f x := by
    rw [hs, ← S.disk.boundary_eq xC]
  have hsSource : gamma (m65LoopAngular s) ∈ chart.source := by
    rw [hsvalue]
    exact mem_chart_source LoopAmbient (f x)
  obtain ⟨j, U, J, sigma, V, hI, hc, hU, hcs, hsig, hV, hinverse, hdata,
      _hUtarg, hUarc⟩ := exists_chart_Jordan_tangent gamma.continuous hinj hsmooth hregular
        (f x) hsSource
  have hcenter : G (e p) ∈ U := by
    change chart (f (e (e.symm x))) ∈ U
    rw [e.apply_symm_apply]
    simpa only [Function.comp_apply, hsvalue] using hcs
  obtain ⟨r, hr, hPclosed, hPopen, hHU, hH, hHi, hHeq⟩ :=
    exists_harmonic_boundary_halfDisk DE hO hp
      (by change e p ∈ O; simpa only [p, e.apply_symm_apply] using hxO)
      hG hGi heq hU hcenter
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  have hPK : MapsTo P K loopDiskSet := fun _ hz => (hPclosed hz).1
  have hKunique : UniqueDiffOn ℝ K := (halfDisk_differential_domain hr).2.2.1
  have hSrc (z : ℂ) (hz : z ∈ K) : f (P z) ∈ chart.source := hsource (hPclosed hz)
  have hNorm (z : ℂ) (hz : z ∈ K) (v : ℂ) :
      gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
        diskConformalFactor g f (P z) * ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2 :=
    complex_parameter_within_conformal_norm g gE (f x) S.boundary_regular S.weakly_conformal
      (hKunique z hz) hz (hasDerivAt_boundaryCoordinate p z) hPK (hSrc z hz)
      ((hmetric (P z) (hPclosed hz)).self_of_nhds) v
  have hConf (z : ℂ) (hz : z ∈ K) :
      let T := fderivWithin ℝ H K z
      gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T Complex.I) (T Complex.I) ∧
        gE.inner (H z) (T 1) (T Complex.I) = 0 := by
    let T := fderivWithin ℝ H K z
    have h1 := hNorm z hz 1
    have hI' := hNorm z hz Complex.I
    have hsum := hNorm z hz (1 + Complex.I)
    have hsumNorm : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
      norm_num [Complex.sq_norm, Complex.normSq_apply]
    simp only [norm_one, norm_I, one_pow, mul_one] at h1 hI'
    rw [hsumNorm, map_add] at hsum
    change gE.inner (H z) (T 1 + T Complex.I) (T 1 + T Complex.I) = _ at hsum
    simp only [map_add, add_apply] at hsum
    rw [gE.symm (H z) (T Complex.I) (T 1)] at hsum
    exact ⟨h1.trans hI'.symm, by linarith⟩
  have hArc (t : ℝ) (ht : ‖(t : ℂ)‖ ≤ r) :
      H (t : ℂ) ∈ (chart ∘ gamma ∘ m65LoopAngular) '' J := by
    have htK : (t : ℂ) ∈ K := ⟨mem_closedBall_zero_iff.mpr ht, by simp⟩
    apply hUarc _ (hHU htK)
    change chart.symm (chart (f (P (t : ℂ)))) ∈ range gamma
    rw [chart.left_inv (hSrc (t : ℂ) htK)]
    have hPt : ‖P (t : ℂ)‖ = 1 := by
      change ‖orthonormalBasisOneI.repr (boundaryCoordinate p (t : ℂ))‖ = 1
      rw [orthonormalBasisOneI.repr.norm_map, norm_boundaryCoordinate hp]
      simp
    exact ⟨S.disk.reparameterization.map ⟨P (t : ℂ), hPt⟩,
      (S.disk.boundary_eq ⟨P (t : ℂ), hPt⟩).symm⟩
  have hZero (z : ℂ) (hz : z ∈ K) : fderivWithin ℝ H K z = 0 ↔
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (P z) = 0 :=
    complex_parameter_within_zero_iff (f x) S.boundary_regular (hKunique z hz) hz
      (hasDerivAt_boundaryCoordinate p z)
      (mul_ne_zero Complex.I_ne_zero (mul_ne_zero hp0 (Complex.exp_ne_zero _))) hPK (hSrc z hz)
  have hnot : ¬∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0, fderivWithin ℝ H K z = 0 := by
    intro hzero
    obtain ⟨V0, hV0, hVzero⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hzero
    have hball : ball (0 : ℂ) r ∈ 𝓝 0 := isOpen_ball.mem_nhds (mem_ball_self hr)
    obtain ⟨δ, hδ, hall⟩ := Metric.mem_nhds_iff.mp
      (inter_mem hV0 (inter_mem (boundaryInverse_coordinate_eventually hp0) hball))
    let T := ball (0 : ℂ) δ ∩ {z | 0 < z.im}
    have hTK (z : ℂ) (hz : z ∈ T) : z ∈ K :=
      ⟨ball_subset_closedBall (hall hz.1).2.2, (show 0 < z.im from hz.2).le⟩
    have hTzero (z : ℂ) (hz : z ∈ T) : fderivWithin ℝ H K z = 0 :=
      hVzero ⟨(hall hz.1).1, (show 0 < z.im from hz.2).le⟩
    have hPT : P '' T ⊆ {y : LoopPlane | y ∈ loopDiskSet ∧
        mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet y = 0} := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨hPK (hTK z hz), (hZero z (hTK z hz)).mp (hTzero z hz)⟩
    have hPInj : InjOn P T := by
      intro z hz w hw hzw
      have hc := e.injective hzw
      have hh := congrArg (boundaryInverse p) hc
      rw [(hall hz.1).2.1, (hall hw.1).2.1] at hh
      exact hh
    have hfinite : T.Finite := (S.finite_branches.subset hPT).of_finite_image hPInj
    have hTop : IsOpen T := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
    have hzT : ((δ / 2 : ℝ) : ℂ) * Complex.I ∈ T := by
      constructor
      · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, norm_I, mul_one,
          Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
        exact half_lt_self hδ
      · simpa using half_pos hδ
    exact (infinite_of_mem_nhds (((δ / 2 : ℝ) : ℂ) * Complex.I) (hTop.mem_nhds hzT)) hfinite
  obtain ⟨d, m, Q, hd, hdr, hQc, hQi, hQne, hfactor, hQ1, hQI, hholder⟩ :=
    halfDisk_Jordan_differential_factor_holder DE hr j hI hU hc hsig hV hH hHi hHU
      (fun y hy => (hdata y hy).1) hinverse (fun y hy => (hdata y hy).2.1)
      (fun y hy => (hdata y hy).2.2) hArc hConf hHeq hnot
  let Kd := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
  let Wd := ball (0 : ℂ) d ∩ {z | 0 < z.im}
  have hKd : Kd ⊆ K :=
    inter_subset_inter (closedBall_subset_closedBall hdr.le) Subset.rfl
  have hWd : Wd ⊆ ball (0 : ℂ) r ∩ {z | 0 < z.im} :=
    inter_subset_inter (ball_subset_ball hdr.le) Subset.rfl
  have hder (z : ℂ) (hz : z ∈ Kd) :
      fderivWithin ℝ H Kd z = fderivWithin ℝ H K z :=
    fderivWithin_subset hKd ((halfDisk_differential_domain hd).2.2.1 z hz)
      ((hH z (hKd hz)).differentiableWithinAt one_ne_zero)
  refine ⟨gE, DE, d, m, Q, hd, hPK.mono hKd Subset.rfl,
    (fun z hz => hSrc z (hKd hz)), hH.mono hKd, hHi.mono hWd,
    (fun z hz => hmetric (P z) (hPclosed (hKd hz))), ?_,
    (fun z hz => hHeq z (hWd hz)), hQc, hQi, hQne, ?_, hQ1, hQI, hholder⟩
  · intro z hz v
    change gE.inner (H z) (fderivWithin ℝ H Kd z v) (fderivWithin ℝ H Kd z v) = _
    rw [hder z hz]
    exact hNorm z (hKd hz) v
  · intro z hz
    change coordinateComplexification (fderivWithin ℝ H Kd z 1) -
        Complex.I • coordinateComplexification (fderivWithin ℝ H Kd z Complex.I) = _
    rw [hder z hz]
    exact hfactor z hz

theorem boundary_branch_residual (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
      (r : ℝ) (m : ℕ) (Q : ℂ → Fin 3 → ℂ), 0 < r ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ W, dbar (complexGradient H) z =
        harmonicMatrix DE H z (complexGradient H z)) ∧
      ContinuousOn Q K ∧ ContDiffOn ℝ 1 Q W ∧
      (∀ z ∈ K, Q z ≠ 0) ∧
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) ∧
      MemLp (fun z => fderiv ℝ Q z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ Q z Complex.I) 2 (volume.restrict W) := by
  obtain ⟨gE, DE, r, m, Q, hr, hP, hsrc, hH, hHi, hg, hn, heq,
      hQc, hQi, hQne, hf, h1, hI, _⟩ :=
    S.boundary_branch_residual_holder hinj hsmooth hregular hx
  exact ⟨gE, DE, r, m, Q, hr, hP, hsrc, hH, hHi, hg, hn, heq,
    hQc, hQi, hQne, hf, h1, hI⟩

end PoincareConjecture.M65MinimalDisk
