import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RayComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Nonterminal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactDifferential



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]

open Poincare.VolumeComparison



theorem polarDensity_cross_le_on_nonterminal
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {p : M} {R κ : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ)
    {L : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))}
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 (m + 1)) p).symm
      (extChartAt (𝓡 (m + 1)) p p) (L v) (L w) = inner ℝ v w)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 (m + 1)) p (e v))
      L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun s : ℝ => e (s • v)) t 1) = ‖v‖)
    (hdist : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      -(m : ℝ) * κ * g.inner x v v ≤ D.ricci x v v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {t s : ℝ} (ht : t ∈ Ioo 0 R) (hs : s ∈ Ioo 0 R) (hts : t ≤ s)
    (hsS : s • θ ∈ localMinimizingSet (fun v => g.edist p (e v)) R \
      terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R) :
    (s ^ m * g.pullbackVolumeDensity e (s • θ)) * modelS κ t ^ m ≤
      (t ^ m * g.pullbackVolumeDensity e (t • θ)) * modelS κ s ^ m := by
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖r • θ‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr, hθ, mul_one]
  have hθ0 : θ ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at hθ
  obtain ⟨q, hq, hqR, hqS⟩ : ∃ q : ℚ, 1 < (q : ℝ) ∧ (q : ℝ) * ‖s • θ‖ < R ∧
      (q : ℝ) • (s • θ) ∈ localMinimizingSet (fun v => g.edist p (e v)) R := by
    by_contra h
    exact hsS.2 ⟨hsS.1, smul_ne_zero hs.1.ne' hθ0,
      mem_iInter.mpr (fun q hq => h ⟨q, hq⟩)⟩
  rw [hnorm s hs.1.le] at hqR
  have hsq : s < (q : ℝ) * s := by nlinarith [hs.1]
  obtain ⟨b, hsb, hbq⟩ := exists_between hsq
  have hb : 0 < b := hs.1.trans hsb
  have hbR : b < R := hbq.trans hqR
  have hsub (r : ℝ) (hr : r ∈ Icc 0 b) : r • θ ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm r hr.1] using hr.2.trans_lt hbR
  have hezero : ContMDiffAt (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e 0 :=
    he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))
  have hinit := isInvertible_mfderiv_zero_of_chart_derivative
    (hezero.mdifferentiableAt (by simp)) he0 hed
  have hi (r : ℝ) (hr : r ∈ Icc 0 b) :
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (r • θ)) := by
    by_cases hr0 : r = 0
    · subst r
      erw [zero_smul]
      exact hinit.injective
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    apply (g.isInvertible_mfderiv_of_minimizing_extension D he he0 hinit hgeo hspeed
      (hsub r hr) (smul_ne_zero hr0 hθ0)
      (q := (q : ℝ) * s / r) ((one_lt_div hrpos).mpr (hr.2.trans_lt hbq)) ?_ ?_).injective
    · simpa only [hnorm r hr.1, div_mul_cancel₀ _ hr0] using hqR
    · simpa only [mem_ofPred_eq, smul_smul, div_mul_cancel₀ _ hr0, hnorm r hr.1,
        norm_smul, Real.norm_of_nonneg (mul_nonneg (by linarith : 0 ≤ (q : ℝ)) hs.1.le),
        hθ, mul_one]
        using hqS.2
  have hric (r : ℝ) (hr : r ∈ Ioo 0 b) :
      ∀ v : TangentSpace (𝓡 (m + 1)) (e (r • θ)),
        -(m : ℝ) * κ * g.inner (e (r • θ)) v v ≤ D.ricci (e (r • θ)) v v := by
    apply hRic
    have hd := hdist (r • θ) (hsub r ⟨hr.1.le, hr.2.le⟩) 1 (by simp)
    simp only [one_smul, ENNReal.ofReal_one, mul_one, hnorm r hr.1.le] at hd
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr (hr.2.trans hbR))
  exact g.polarDensity_cross_le_on_regular_ray D hm Metric.isOpen_ball
    (by simpa using hR) he hgeo
    (g.pullbackCoefficients_zero_of_normalized_chart hezero he0 hed hL)
    θ hθ hb hκ hsub hi hric ⟨ht.1, hts.trans_lt hsb⟩ ⟨hs.1, hsb⟩ hts

end PoincareConjecture.RiemannianMetric
