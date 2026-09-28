import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetResidualLog
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskInteriorFactor
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskConformal

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem interior_logarithmicDensity_integrable (S : M65MinimalDisk g connection gamma)
    {x : LoopPlane} (hx : x ∈ ball (0 : LoopPlane) 1) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ ball (0 : LoopPlane) 1 ∧
      IntegrableOn (fun z => -(∑ i : Fin 2, fderiv ℝ (fun y =>
        fderiv ℝ (fun w => Real.log (S.conformalFactor w)) y
          (EuclideanSpace.basisFun (Fin 2) ℝ i))
            z (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2) (ball x r) volume := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let z0 := e.symm x
  let q := chartAt LoopAmbient (S.disk.map x)
  let G := q ∘ S.disk.map
  let H := G ∘ e
  obtain ⟨gE, DE, V, hV, hxV, hVdisk, hsource, hG, hmetric, _heq⟩ :=
    S.exists_harmonic_chart_neighborhood hx
  obtain ⟨m, Q, hQc, hQ0, hfac⟩ := S.interior_branch_power_factor hx
  obtain ⟨VQ, hVQ, hQs⟩ := hQc.contDiffOn le_rfl (by simp)
  have hpre : ∀ᶠ z in 𝓝 z0, e z ∈ V := by
    have he : Tendsto e (𝓝 z0) (𝓝 x) := by
      have hh : Tendsto e (𝓝 z0) (𝓝 (e z0)) := e.continuous.continuousAt
      simpa only [z0, e.apply_symm_apply] using hh
    exact he (hV.mem_nhds hxV)
  have hall : ∀ᶠ z in 𝓝 z0,
      z ∈ VQ ∧ e z ∈ V ∧ Q z ≠ 0 ∧ complexGradient H z = (z - z0) ^ m • Q z := by
    filter_upwards [hVQ, hpre, hQc.continuousAt.eventually_ne hQ0, hfac] with z hz hv hn hf
    exact ⟨hz, hv, hn, hf⟩
  obtain ⟨d, hd, hds⟩ := Metric.mem_nhds_iff.mp hall
  let r := d / 2
  have hr : 0 < r := half_pos hd
  let K := closedBall z0 r
  let U := ball z0 r \ {z0}
  have hKsub (z : ℂ) (hz : z ∈ K) :
      z ∈ VQ ∧ e z ∈ V ∧ Q z ≠ 0 ∧ complexGradient H z = (z - z0) ^ m • Q z :=
    hds (closedBall_subset_ball (half_lt_self hd) hz)
  have hK : IsCompact K := isCompact_closedBall z0 r
  have hKU : UniqueDiffOn ℝ K := by
    apply uniqueDiffOn_convex (convex_closedBall z0 r)
    rw [interior_closedBall z0 hr.ne']
    exact nonempty_ball.mpr hr
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hUK : U ⊆ K := fun _ hz => ball_subset_closedBall hz.1
  have hcl : K ⊆ closure U := by
    have hh : ball z0 r ⊆ closure U := by
      simpa only [U, Set.sdiff_eq] using
        (dense_compl_singleton z0).open_subset_closure_inter (isOpen_ball (x := z0) (ε := r))
    simpa only [K, closure_ball z0 hr.ne', closure_closure] using closure_mono hh
  have hH : ContDiffOn ℝ ∞ H K :=
    hG.comp e.contDiff.contDiffOn (fun z hz => (hKsub z hz).2.1)
  have hQ : ContDiffOn ℝ 1 Q K := hQs.mono (fun z hz => (hKsub z hz).1)
  have hmap : MapsTo (orthonormalBasisOneI.repr ∘ (fun z : ℂ => z)) K loopDiskSet :=
    fun z hz => ball_subset_closedBall (hVdisk (hKsub z hz).2.1)
  have hnorm (z : ℂ) (hz : z ∈ K) (v : ℂ) :
      gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
        diskConformalFactor g S.disk.map (e z) * ‖v‖ ^ 2 := by
    have hh := complex_parameter_within_conformal_norm g gE (S.disk.map x)
      S.boundary_regular S.weakly_conformal (hKU z hz) hz (hasDerivAt_id z) hmap
      (hsource (hKsub z hz).2.1) (hmetric (e z) (hKsub z hz).2.1) v
    simpa +instances only [Function.comp_id, id_eq, norm_one, one_pow, mul_one, H, G, q, e]
      using! hh
  have hconf (z : ℂ) (hz : z ∈ K) :
      let T := fderivWithin ℝ H K z
      gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
        gE.inner (H z) (T 1) (T I) = 0 := by
    let T := fderivWithin ℝ H K z
    have h1 := hnorm z hz 1
    have hI := hnorm z hz I
    have hsum := hnorm z hz (1 + I)
    have hs : ‖(1 : ℂ) + I‖ ^ 2 = 2 := by
      norm_num [Complex.sq_norm, Complex.normSq_apply]
    simp only [norm_one, norm_I, one_pow, mul_one] at h1 hI
    rw [hs, map_add] at hsum
    change gE.inner (H z) (T 1 + T I) (T 1 + T I) = _ at hsum
    simp only [map_add, add_apply] at hsum
    rw [gE.symm (H z) (T I) (T 1)] at hsum
    exact ⟨h1.trans hI.symm, by linarith⟩
  have hfactor (z : ℂ) (hz : z ∈ U) :
      ∃ s : ℂ, s ≠ 0 ∧ complexGradient H z = s • Q z := by
    refine ⟨(z - z0) ^ m, pow_ne_zero m (sub_ne_zero.mpr ?_), (hKsub z (hUK hz)).2.2.2⟩
    simpa only [mem_singleton_iff] using hz.2
  have hL := residual_logarithmicDensity_integrable DE hK hKU hU hUK hcl hH hQ
    (fun z hz => (hKsub z hz).2.2.1) hfactor hconf
  let lam := fun z : LoopPlane => gE.inner (H (e.symm z))
    (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let L := fun z => -(∑ i : Fin 2, fderiv ℝ (fun y =>
    fderiv ℝ (fun w => Real.log (lam w)) y (b i)) z (b i)) / 2
  change IntegrableOn L (e.symm ⁻¹' U) volume at hL
  have hball (z : LoopPlane) : e.symm z ∈ ball z0 r ↔ z ∈ ball x r := by
    change dist (e.symm z) (e.symm x) < r ↔ dist z x < r
    rw [show dist (e.symm z) (e.symm x) = dist z x from
      orthonormalBasisOneI.repr.symm.dist_map z x]
  have hset : e.symm ⁻¹' U = ball x r \ {x} := by
    ext z
    change (e.symm z ∈ ball z0 r ∧ e.symm z ∉ {z0}) ↔
      (z ∈ ball x r ∧ z ∉ {x})
    rw [hball]
    simp only [z0, mem_singleton_iff, e.symm.injective.eq_iff]
  have hlam (z : LoopPlane) (hz : z ∈ ball x r) : lam z = S.conformalFactor z := by
    have hh := hnorm (e.symm z) (ball_subset_closedBall ((hball z).mpr hz)) 1
    have he : e (e.symm z) = z := e.apply_symm_apply z
    rw [he] at hh
    simpa +instances only [norm_one, one_pow, mul_one, e.apply_symm_apply, lam,
      conformalFactor, boundaryColumn, diskConformalFactor, diskColumn] using! hh
  have hactual (z : LoopPlane) (hz : z ∈ ball x r) : L z =
      -(∑ i : Fin 2, fderiv ℝ (fun y =>
        fderiv ℝ (fun w => Real.log (S.conformalFactor w)) y (b i)) z (b i)) / 2 := by
    have heq : (fun w => Real.log (lam w)) =ᶠ[𝓝 z]
        (fun w => Real.log (S.conformalFactor w)) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      rw [hlam w hw]
    have hpart (i : Fin 2) : (fun y => fderiv ℝ (fun w => Real.log (lam w)) y (b i))
        =ᶠ[𝓝 z] (fun y => fderiv ℝ (fun w => Real.log (S.conformalFactor w)) y (b i)) :=
      (heq.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun A => A (b i)) hy
    dsimp only [L]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun A => A (b i)) ((hpart i).fderiv_eq (𝕜 := ℝ))
  rw [hset] at hL
  have hactualL := hL.congr_fun (fun z hz => hactual z hz.1)
    (isOpen_ball.measurableSet.diff (measurableSet_singleton x))
  have hnull : (ball x r \ {x} : Set LoopPlane) =ᵐ[volume] ball x r := by
    exact sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right (measure_singleton x))
  refine ⟨r, hr, ?_, (integrableOn_congr_set_ae hnull).mp hactualL⟩
  intro z hz
  have hh := hVdisk (hKsub (e.symm z) (ball_subset_closedBall ((hball z).mpr hz))).2.1
  simpa only [e.apply_symm_apply] using hh

end PoincareConjecture.M65MinimalDisk
