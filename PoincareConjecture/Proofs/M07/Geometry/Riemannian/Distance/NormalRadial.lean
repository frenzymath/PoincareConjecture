import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem gauss_radial_inner_eq (g : RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M}
    {v : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : t ≠ 0)
    (hgauss : g.inner (e (t • v))
      (mfderiv (𝓡 n) (𝓡 n) e (t • v) (t • v))
      (mfderiv (𝓡 n) (𝓡 n) e (t • v) v) = g.inner p (t • v) v) :
    g.inner (e (t • v)) (mfderiv (𝓡 n) (𝓡 n) e (t • v) v)
      (mfderiv (𝓡 n) (𝓡 n) e (t • v) v) = g.inner p v v := by
  have hh := hgauss
  simp only [map_smul, smul_apply, smul_eq_mul] at hh
  exact (mul_left_cancel₀ ht) hh


theorem pathELength_radial_eq_of_gauss
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hgauss : ∀ v ∈ e.source, ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner p v w)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ e.source) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun t : ℝ => e (t • v)) (Icc 0 1) ∧
      g.pathELength (fun t : ℝ => e (t • v)) 0 1 =
        ENNReal.ofReal (g.tangentNorm p v) := by
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun t : ℝ => t • v) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const)
  refine ⟨(he.comp hsmooth.contMDiffOn hv).of_le (by simp), ?_⟩
  rw [pathELength_eq_lintegral_tangentNorm,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1))]
  have heq : (fun t => ENNReal.ofReal (g.tangentNorm (e (t • v))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t : ℝ => e (t • v)) t 1))) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] fun _ => ENNReal.ofReal (g.tangentNorm p v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hchain := mfderiv_comp t
      ((he.contMDiffAt (e.open_source.mem_nhds (hv t (Ioo_subset_Icc_self ht)))).mdifferentiableAt
        (by simp)) (hsmooth.mdifferentiable (by simp) t)
    have hd : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t : ℝ => t • v) t 1 = v := by
      rw [mfderiv_eq_fderiv]
      have hh : HasDerivAt (fun t : ℝ => t • v) v t := by
        simpa using (hasDerivAt_id t).smul_const v
      rw [hh.hasFDerivAt.fderiv]
      change (1 : ℝ) • v = v
      exact one_smul ℝ v
    have hchain1 : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t : ℝ => e (t • v)) t 1 =
        mfderiv (𝓡 n) (𝓡 n) e (t • v) v := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, hd] using
        congrArg (fun L => L 1) hchain
    rw [hchain1]
    congr 1
    unfold tangentNorm
    rw [g.gauss_radial_inner_eq p ht.1.ne' (hgauss (t • v)
      (hv t (Ioo_subset_Icc_self ht)) v)]
  rw [lintegral_congr_ae heq, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioo]
  simp


theorem edist_radial_le_of_gauss
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) (he0 : e 0 = p)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hgauss : ∀ v ∈ e.source, ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner p v w)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ e.source) :
    g.edist p (e v) ≤ ENNReal.ofReal (g.tangentNorm p v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨hsm, hlen⟩ := g.pathELength_radial_eq_of_gauss p e he hgauss v hv
  rw [← hlen]
  exact riemannianEDist_le_pathELength hsm (by simpa using he0) (by simp) zero_le_one

end PoincareConjecture.RiemannianMetric
