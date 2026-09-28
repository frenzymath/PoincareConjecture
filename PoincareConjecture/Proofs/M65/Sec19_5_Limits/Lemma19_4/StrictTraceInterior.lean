import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchHarmonicEquation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Complex
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M65StrictTrace

open M65Branch

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem complex_chart_gradient_zero_iff (p : M) {f : LoopPlane → M} {z : ℂ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 3) f (orthonormalBasisOneI.repr z))
    (hsource : f (orthonormalBasisOneI.repr z) ∈ (chartAt LoopAmbient p).source) :
    complexGradient ((chartAt LoopAmbient p) ∘ f ∘ orthonormalBasisOneI.repr) z = 0 ↔
      mfderiv (𝓡 2) (𝓡 3) f (orthonormalBasisOneI.repr z) = 0 := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let q := chartAt LoopAmbient p
  let G := q ∘ f
  let H := G ∘ e
  have hq := (mdifferentiable_chart (I := 𝓡 3) p).mdifferentiableAt hsource
  have hG : DifferentiableAt ℝ G (e z) := (hq.comp (e z) hf).differentiableAt
  have hd := hG.hasFDerivAt.comp z e.hasFDerivAt
  change complexGradient H z = 0 ↔ mfderiv (𝓡 2) (𝓡 3) f (e z) = 0
  rw [complexGradient_eq_zero_iff]
  constructor
  · intro hH
    have hcoord (v : LoopPlane) : fderiv ℝ G (e z) v = 0 := by
      have hv := congrArg (fun L : ℂ →L[ℝ] LoopAmbient => L (e.symm v)) hd.fderiv
      change fderiv ℝ H z (e.symm v) = fderiv ℝ G (e z) (e (e.symm v)) at hv
      simpa only [hH, zero_apply, e.apply_symm_apply] using hv.symm
    apply ContinuousLinearMap.ext
    intro v
    have hv := m65PlaneDerivative_chart p hf hsource v
    change Proofs.M09.chartVectorField p (fderiv ℝ G (e z) v) (f (e z)) = _ at hv
    rw [hcoord v] at hv
    simpa +instances only [Proofs.M09.chartVectorField, VectorField.mpullback, map_zero,
      zero_apply, e, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using! hv.symm
  · intro hzero
    have hc := mfderiv_comp (e z) hq hf
    rw [mfderiv_eq_fderiv, hzero, ContinuousLinearMap.comp_zero] at hc
    change fderiv ℝ G (e z) = 0 at hc
    rw [hd.fderiv, hc, ContinuousLinearMap.zero_comp]





theorem interior_differential_zero_alternative (D : LeviCivitaData g)
    {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (Metric.ball (0 : LoopPlane) 1))
    (hb : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hharm : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    {x : LoopPlane} (hx : x ∈ Metric.ball (0 : LoopPlane) 1) :
    (∀ᶠ y in 𝓝 x, mfderiv (𝓡 2) (𝓡 3) f y = 0) ∨
      ∀ᶠ y in 𝓝 x, mfderiv (𝓡 2) (𝓡 3) f y = 0 → y = x := by
  by_cases hzero : ∀ᶠ y in 𝓝 x, mfderiv (𝓡 2) (𝓡 3) f y = 0
  · exact Or.inl hzero
  right
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let q := chartAt LoopAmbient (f x)
  let G := q ∘ f
  let H := G ∘ e
  let z0 := e.symm x
  obtain ⟨gE, DE, O, hO, hxO, hsource, _, hG, _, heq⟩ :=
    exists_closedDisk_harmonic_chart D hf hb hharm (Metric.ball_subset_closedBall hx)
  let W := Metric.ball (0 : LoopPlane) 1 ∩ O
  have hW : IsOpen W := Metric.isOpen_ball.inter hO
  let V := e ⁻¹' W
  have hV : IsOpen V := hW.preimage e.continuous
  have hz0 : z0 ∈ V := by
    change e (e.symm x) ∈ W
    simpa only [e.apply_symm_apply] using (show x ∈ W from ⟨hx, hxO⟩)
  have hH : ContDiffOn ℝ ∞ H V := hG.comp e.contDiff.contDiffOn (fun _ hz => hz)
  have hmatrix (z : ℂ) (hz : z ∈ V) :
      dbar (complexGradient H) z = harmonicMatrix DE H z (complexGradient H z) :=
    plane_harmonic_to_complex DE (hG.contDiffAt (hW.mem_nhds hz)) (heq (e z) hz)
  have hiff (z : ℂ) (hz : z ∈ V) : complexGradient H z = 0 ↔
      mfderiv (𝓡 2) (𝓡 3) f (e z) = 0 :=
    complex_chart_gradient_zero_iff (f x)
      ((hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hz.1)).mdifferentiableAt (by simp))
      (hsource ⟨Metric.ball_subset_closedBall hz.1, hz.2⟩)
  have hback : Tendsto e.symm (𝓝 x) (𝓝 z0) := e.symm.continuous.tendsto x
  have hnot : ¬∀ᶠ z in 𝓝 z0, complexGradient H z = 0 := by
    intro hn
    apply hzero
    filter_upwards [hback.eventually hn, hback.eventually (hV.mem_nhds hz0)] with y hy hyV
    exact Eq.mp (congrArg (fun w : LoopPlane => mfderiv (𝓡 2) (𝓡 3) f w = 0)
      (e.apply_symm_apply y)) ((hiff (e.symm y) hyV).mp hy)
  obtain ⟨m, K, hK, hK0, hfactor⟩ := exists_power_factor_of_local_matrix_equation hV hz0
    (contDiffOn_harmonicMatrix DE hV hH) (contDiffOn_complexGradient hV hH) hmatrix hnot
  have hnear : ∀ᶠ z in 𝓝 z0, complexGradient H z = 0 → z = z0 := by
    filter_upwards [hfactor, hK.continuousAt.eventually_ne hK0] with z hzf hzK hz
    by_contra hne
    have hp : (z - z0) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hne)
    exact (smul_ne_zero hp hzK) (hzf.symm.trans hz)
  filter_upwards [hback.eventually hnear, hback.eventually (hV.mem_nhds hz0)]
    with y hy hyV hyzero
  have hz : complexGradient H (e.symm y) = 0 := (hiff _ hyV).mpr
    (Eq.mpr (congrArg (fun w : LoopPlane => mfderiv (𝓡 2) (𝓡 3) f w = 0)
      (e.apply_symm_apply y)) hyzero)
  exact e.symm.injective (hy hz)

end PoincareConjecture.M65StrictTrace
