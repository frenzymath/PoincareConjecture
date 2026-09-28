import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalBall
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema
import Mathlib.Analysis.Calculus.LocalExtr.Basic



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_contMDiff_squared_edist_near
    (g : RiemannianMetric n M) (p : M) :
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      ∃ r : ℝ, 0 < r ∧ ∀ y : M, (g.edist y p).toReal < r →
        f y = (g.edist y p).toReal ^ 2 := by
  let := g.toMetricSpace
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨e, h0, he0, he, he', hgauss, _⟩ := g.exists_exponential_chart_gauss p
  obtain ⟨r, hr, hsource, hdist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e h0 he0 he he' hgauss
  let ρ : M → ℝ := fun y => g.inner p (e.symm y) (e.symm y)
  have hquad : ContDiff ℝ ∞ (fun v : E => g.inner p v v) :=
    (contDiff_const.clm_apply contDiff_id).clm_apply contDiff_id
  have hρ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ e.target :=
    (contMDiff_iff_contDiff.mpr hquad).comp_contMDiffOn he'
  obtain ⟨f, hf, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near
    e.open_target hρ (he0 ▸ e.map_source h0)
  have hnorm : Continuous (fun v : E => g.tangentNorm p v) := by
    unfold tangentNorm
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  have hV : {v : E | g.tangentNorm p v < r} ∈ 𝓝 0 :=
    (isOpen_lt hnorm continuous_const).mem_nhds (by simpa [tangentNorm] using hr)
  have hU : e '' {v : E | g.tangentNorm p v < r} ∈ 𝓝 p := by
    simpa only [he0] using e.image_mem_nhds h0 hV
  have heqdist : ∀ᶠ y in 𝓝 p, f y = (g.edist y p).toReal ^ 2 := by
    filter_upwards [heq, hU] with y hy hyU
    obtain ⟨v, hv, rfl⟩ := hyU
    rw [hy]
    change g.inner p (e.symm (e v)) (e.symm (e v)) = _
    rw [e.left_inv (hsource hv)]
    have hd : (g.edist (e v) p).toReal = g.tangentNorm p v := by
      change dist (e v) p = _
      rw [dist_comm, g.toMetricSpace_dist, hdist v hv]
      exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
    rw [hd]
    exact (Real.sq_sqrt (by
      by_cases hv0 : v = 0
      · simp [hv0]
      · exact (g.pos p v hv0).le)).symm
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp heqdist
  exact ⟨f, hf, s, hs, fun y hy => hball hy⟩




theorem exists_center_squared_distance_potential
    (g : RiemannianMetric n M) (p : M) :
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      g.gradient f p = 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∀ y : M, (g.edist y p).toReal < r → f y = (g.edist y p).toReal ^ 2) ∧
      ∀ y : M, (g.edist y p).toReal < r → ∀ γ : ℝ → M,
        g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
        γ (g.edist y p).toReal = p →
        (∀ s ∈ Icc 0 (g.edist y p).toReal,
          g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = 1) →
        (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
        mvfderiv (𝓡 n) f y (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) =
          -2 * (g.edist y p).toReal := by
  let := g.toMetricSpace
  obtain ⟨f, hf, r, hr, heq⟩ := g.exists_contMDiff_squared_edist_near p
  have hfp : f p = 0 := by
    have hp := heq p (by simpa only [← g.toMetricSpace_dist, dist_self] using hr)
    simpa only [← g.toMetricSpace_dist, dist_self, zero_pow (by decide : 2 ≠ 0)] using hp
  have hmin : IsLocalMin f p := by
    filter_upwards [Metric.ball_mem_nhds p hr] with y hy
    rw [hfp, heq y hy]
    exact sq_nonneg _
  have hneg := LeviCivitaData.mvfderiv_eq_zero_of_isLocalMax hf.neg hmin.neg
  have hdfp : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 := by
    have hneg' : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (-f) p = 0 := by
      ext v
      exact congrArg (fun A => A v) hneg
    rwa [mfderiv_neg, neg_eq_zero] at hneg'
  refine ⟨f, hf, (g.gradient_eq_zero_iff_mfderiv_eq_zero f p).mpr hdfp,
    r, hr, heq, ?_⟩
  intro y hy γ hγ hγ0 hγL _hspeed hγmin
  let L := (g.edist y p).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  by_cases hzero : L = 0
  · have hyp : y = p := dist_eq_zero.mp hzero
    rw [hyp]
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p _ = _
    rw [hdfp, zero_apply]
    have hpdist : (g.edist p p).toReal = 0 := dist_self p
    rw [hpdist, mul_zero]
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
  have hγd := (hγ.contMDiffAt (show (0 : ℝ) ∈ Icc 0 L from
    ⟨le_rfl, hL⟩)).mdifferentiableAt (by simp)
  have hfd := (hf (γ 0)).mdifferentiableAt (by simp)
  have hd := (hasMFDerivAt_iff_hasFDerivAt.mp
    (hfd.hasMFDerivAt.comp 0 hγd.hasMFDerivAt)).hasDerivAt
  have hscalar : HasDerivAt (fun t => f (γ t))
      (mvfderiv (𝓡 n) f y (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)) 0 := by
    change HasDerivAt (fun t => f (γ t))
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)) 0 at hd
    rw [hγ0] at hd
    exact hd
  have heqcurve : ∀ t ∈ Icc 0 L, f (γ t) = (L - t) ^ 2 := by
    intro t ht
    have hdist : (g.edist (γ t) p).toReal = L - t := by
      rw [← hγL, hγmin t ht L ⟨hL, le_rfl⟩,
        ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonpos (sub_nonpos.mpr ht.2)]
      ring
    rw [heq (γ t) (by rw [hdist]; dsimp [L] at *; linarith [ht.1]), hdist]
  have hpoly : HasDerivAt (fun t : ℝ => (L - t) ^ 2) (-2 * L) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_sub L).pow 2 using 1
    norm_num
  have hwithin : HasDerivWithinAt (fun t => f (γ t)) (-2 * L) (Icc 0 L) 0 :=
    hpoly.hasDerivWithinAt.congr heqcurve (heqcurve 0 ⟨le_rfl, hL⟩)
  exact (hscalar.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc hLpos 0 ⟨le_rfl, hL⟩)).symm.trans
      (hwithin.derivWithin (uniqueDiffOn_Icc hLpos 0 ⟨le_rfl, hL⟩))

end PoincareConjecture.RiemannianMetric
