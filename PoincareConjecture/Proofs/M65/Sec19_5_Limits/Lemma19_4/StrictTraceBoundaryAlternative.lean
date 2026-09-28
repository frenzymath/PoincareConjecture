import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceHalfDiskAlternative
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceBoundaryDifferential
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceTargetArc
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceChart












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff Manifold Bundle BigOperators

namespace PoincareConjecture.M65StrictTrace

open M65Branch

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

set_option maxHeartbeats 1600000 in





theorem boundary_differential_zero_alternative (D : LeviCivitaData g)
    {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (ball (0 : LoopPlane) 1))
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hharm : ∀ z ∈ ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    {gamma : LoopCircle → M} (hgamma : Continuous gamma)
    (hinj : Function.Injective gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    (beta : LoopCircle → LoopCircle) (htrace : ∀ z : LoopCircle, f z = gamma (beta z))
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    (∀ᶠ y in 𝓝[loopDiskSet] x, mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet y = 0) ∨
      ∀ᶠ y in 𝓝[loopDiskSet] x,
        mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet y = 0 → y = x := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let q := chartAt LoopAmbient (f x)
  let G := q ∘ f
  let P := e ∘ boundaryCoordinate p
  let H := G ∘ P
  have hp : ‖p‖ = 1 := by
    change ‖orthonormalBasisOneI.repr.symm x‖ = 1
    rw [orthonormalBasisOneI.repr.symm.norm_map, hx]
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  have hxK : x ∈ loopDiskSet := by
    rw [loopDiskSet, mem_closedBall_zero_iff, hx]
  obtain ⟨gE, DE, O, hO, hxO, hsource, hG, hGi, hmetric, heq⟩ :=
    exists_closedDisk_harmonic_chart D hf hb hharm hxK
  let xC : LoopCircle := ⟨x, hx⟩
  obtain ⟨s, hs⟩ := m65LoopAngular_continuous_surjective.2 (beta xC)
  have hsvalue : gamma (m65LoopAngular s) = f x := by
    rw [hs, ← htrace xC]
  have hsSource : gamma (m65LoopAngular s) ∈ q.source := by
    rw [hsvalue]
    exact mem_chart_source LoopAmbient (f x)
  obtain ⟨j, U, J, sigma, V, hI, hc, hU, hcs, hsig, hV, hinverse, hdata,
      hUtarg, hUarc⟩ := exists_chart_Jordan_tangent hgamma hinj hsmooth hregular (f x) hsSource
  have hcenter : G (e p) ∈ U := by
    change q (f (e (e.symm x))) ∈ U
    rw [e.apply_symm_apply]
    simpa only [Function.comp_apply, hsvalue] using hcs
  obtain ⟨r, hr, hPclosed, hPopen, hHU, hH, hHi, hHeq⟩ :=
    exists_harmonic_boundary_halfDisk DE hO hp
      (by change e p ∈ O; simpa only [p, e.apply_symm_apply] using hxO)
      hG hGi heq hU hcenter
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  have hPK : MapsTo P K loopDiskSet := fun _ hz => (hPclosed hz).1
  have hKunique : UniqueDiffOn ℝ K := (halfDisk_differential_domain hr).2.2.1
  have hSrc (z : ℂ) (hz : z ∈ K) : f (P z) ∈ q.source := hsource (hPclosed hz)
  have hNorm (z : ℂ) (hz : z ∈ K) (v : ℂ) :
      gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
        diskConformalFactor g f (P z) * ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2 :=
    complex_parameter_within_conformal_norm g gE (f x) hb hconf (hKunique z hz) hz
      (hasDerivAt_boundaryCoordinate p z) hPK (hSrc z hz)
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
      H (t : ℂ) ∈ (q ∘ gamma ∘ m65LoopAngular) '' J := by
    have htK : (t : ℂ) ∈ K := ⟨mem_closedBall_zero_iff.mpr ht, by simp⟩
    apply hUarc _ (hHU htK)
    change q.symm (q (f (P (t : ℂ)))) ∈ range gamma
    rw [q.left_inv (hSrc (t : ℂ) htK)]
    have hPt : ‖P (t : ℂ)‖ = 1 := by
      change ‖orthonormalBasisOneI.repr (boundaryCoordinate p (t : ℂ))‖ = 1
      rw [orthonormalBasisOneI.repr.norm_map, norm_boundaryCoordinate hp]
      simp
    exact ⟨beta ⟨P (t : ℂ), hPt⟩, (htrace ⟨P (t : ℂ), hPt⟩).symm⟩
  have hAlt := halfDisk_differential_zero_alternative DE hr j hI hU hc hsig hV hH hHi hHU
    (fun y hy => (hdata y hy).1) hinverse (fun y hy => (hdata y hy).2.1)
    (fun y hy => (hdata y hy).2.2) hArc hConf hHeq
  have hZero (z : ℂ) (hz : z ∈ K) : fderivWithin ℝ H K z = 0 ↔
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (P z) = 0 :=
    complex_parameter_within_zero_iff (f x) hb (hKunique z hz) hz
      (hasDerivAt_boundaryCoordinate p z)
      (mul_ne_zero Complex.I_ne_zero (mul_ne_zero hp0 (Complex.exp_ne_zero _))) hPK (hSrc z hz)
  let back := boundaryInverse p ∘ e.symm
  have heback : Tendsto e.symm (𝓝[loopDiskSet] x) (𝓝[closedBall (0 : ℂ) 1] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(e.symm.continuous.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [mem_closedBall_zero_iff]
    change ‖orthonormalBasisOneI.repr.symm y‖ ≤ 1
    rw [orthonormalBasisOneI.repr.symm.norm_map]
    exact mem_closedBall_zero_iff.mp hy
  have hback : Tendsto back (𝓝[loopDiskSet] x) (𝓝[{z : ℂ | 0 ≤ z.im}] 0) :=
    (boundaryInverse_tendstoWithin hp).comp heback
  have hnearK : ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0, z ∈ K := by
    have hball : ∀ᶠ z : ℂ in 𝓝 0, z ∈ ball (0 : ℂ) r :=
      isOpen_ball.mem_nhds (mem_ball_self hr)
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hi
    exact ⟨ball_subset_closedBall hz, hi⟩
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; norm_num)
  have hPback : ∀ᶠ y in 𝓝[loopDiskSet] x, P (back y) = y := by
    filter_upwards [(continuous_id.continuousAt.eventually_ne hx0).filter_mono
      nhdsWithin_le_nhds] with y hy
    have hy0 : e.symm y ≠ 0 := by
      intro h
      apply hy
      change y = 0
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    change e (boundaryCoordinate p (boundaryInverse p (e.symm y))) = y
    rw [boundaryCoordinate_inverse hp0 hy0, e.apply_symm_apply]
  have hP0 : P 0 = x := by simp [P, boundaryCoordinate, p]
  rcases hAlt with hlocal | hisolated
  · left
    filter_upwards [hback.eventually hlocal, hback.eventually hnearK, hPback] with y hy hyK he
    exact Eq.mp (congrArg
      (fun w : LoopPlane => mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet w = 0) he)
      ((hZero (back y) hyK).mp hy)
  · right
    filter_upwards [hback.eventually hisolated, hback.eventually hnearK, hPback]
      with y hy hyK he hyzero
    have hDz : mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (P (back y)) = 0 :=
      Eq.mpr (congrArg
        (fun w : LoopPlane => mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet w = 0) he) hyzero
    have hby := hy ((hZero (back y) hyK).mpr hDz)
    rw [hby, hP0] at he
    exact he.symm

end PoincareConjecture.M65StrictTrace
