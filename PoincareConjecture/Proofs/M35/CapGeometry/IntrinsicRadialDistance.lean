import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialMetric
import PoincareConjecture.Proofs.M35.CapGeometry.RadialPointIdentification
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalRadius
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalRadial
import PoincareConjecture.Proofs.M10.VectorDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.M35.Uniqueness

private theorem unit_gauss_edist (g : RiemannianMetric 3 StandardCapSpace)
    (hzero : ∀ u v : StandardCapSpace, g.inner 0 u v = inner ℝ u v)
    (hgauss : ∀ x w : StandardCapSpace, g.inner x x w = inner ℝ x w)
    (x : StandardCapSpace) : g.edist 0 x = ENNReal.ofReal ‖x‖ := by
  let e := OpenPartialHomeomorph.refl StandardCapSpace
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := by
    simpa only [e, OpenPartialHomeomorph.refl_apply] using
      (contMDiff_id (I := 𝓡 3) (n := ∞)).contMDiffOn
  have he' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply] using
      (contMDiff_id (I := 𝓡 3) (n := ∞)).contMDiffOn
  have hg : ∀ v ∈ e.source, ∀ w : StandardCapSpace,
      g.inner (e v) (mfderiv (𝓡 3) (𝓡 3) e v v)
        (mfderiv (𝓡 3) (𝓡 3) e v w) = g.inner 0 v w := by
    intro v _hv w
    simpa [e, OpenPartialHomeomorph.refl_apply] using!
      (hgauss v w).trans (hzero v w).symm
  have hn : g.tangentNorm 0 x = ‖x‖ := by
    rw [RiemannianMetric.tangentNorm, hzero, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg x)]
  have hupper : g.edist 0 x ≤ ENNReal.ofReal ‖x‖ := by
    simpa only [e, hn, OpenPartialHomeomorph.refl_apply] using!
      g.edist_radial_le_of_gauss 0 e rfl he hg x (fun _ _ => mem_univ _)
  apply le_antisymm hupper
  let r : ℝ≥0 := ⟨‖x‖ + 1, by positivity⟩
  have hr : 0 < r := by change 0 < ‖x‖ + 1; positivity
  have hx : g.edist 0 x < r := hupper.trans_lt (by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x) |>.mpr (by
      change ‖x‖ < ‖x‖ + 1
      linarith))
  have hz : g.edist 0 0 < r := by
    have hself : g.edist 0 0 = 0 :=
      @edist_self StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace 0
    rw [hself]
    exact_mod_cast hr
  have hregularized (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      edist (Real.sqrt epsilon) (Real.sqrt (g.inner 0 x x + epsilon)) ≤ g.edist 0 x := by
    let f : StandardCapSpace → ℝ := fun y => Real.sqrt (g.inner 0 y y + epsilon)
    have hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f :=
      (g.contDiff_regularized_tangentNorm 0 hepsilon).contMDiff
    have hbound : ∀ y ∈ (univ : Set StandardCapSpace), ∀ v : TangentSpace (𝓡 3) y,
        ‖mvfderiv (𝓡 3) f y v‖ ≤ (1 : ℝ≥0) * g.tangentNorm y v := by
      intro y _hy v
      simpa [f, e, OpenPartialHomeomorph.refl_apply, Real.norm_eq_abs] using!
        g.regularized_tangentNorm_mfderiv_le 0 e he he' hg hepsilon
          (show y ∈ e.target from mem_univ y) v
    have hd := M10.edist_le_mul_riemannianEDist_of_vector_differential g
      hf.continuous.continuousOn (fun y _ => hf.mdifferentiable (by simp) y)
      hbound (fun y _ => mem_univ y) hz hx
    simpa [f] using hd
  have hlimit : Tendsto (fun epsilon : ℝ => edist (Real.sqrt epsilon)
      (Real.sqrt (g.inner 0 x x + epsilon))) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (g.tangentNorm 0 x))) := by
    have hc : Continuous (fun epsilon : ℝ => edist (Real.sqrt epsilon)
        (Real.sqrt (g.inner 0 x x + epsilon))) :=
      Real.continuous_sqrt.edist
        (Real.continuous_sqrt.comp (continuous_const.add continuous_id))
    simpa [edist_dist, Real.dist_eq, RiemannianMetric.tangentNorm,
      abs_of_nonneg, Real.sqrt_nonneg] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  rw [← hn]
  apply le_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon using
    hregularized epsilon hepsilon

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

include hrotation hcomplete

theorem intrinsicSpatialMetric_edist_zero (x : StandardCapSpace) :
    (intrinsicSpatialMetric g hrotation hcomplete).edist 0 x = ENNReal.ofReal ‖x‖ := by
  apply unit_gauss_edist _ (intrinsicSpatialMetric_inner_zero g hrotation hcomplete)
  intro y w
  by_cases hy : y = 0
  · subst y
    simp
  rw [intrinsicSpatialMetric_inner g hrotation hcomplete hy,
    real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hy]
  ring

theorem edist_zero_eq_radialArclength (P : M35StandardCapPredecessors)
    (x : StandardCapSpace) : g.edist 0 x = ENNReal.ofReal (radialArclength g ‖x‖) := by
  let F := intrinsicSpatialDiffeomorph g hrotation hcomplete
  let G := intrinsicSpatialMetric g hrotation hcomplete
  have hmetric : MetricHomothety G g F.symm 1 := by
    intro y u v
    rw [one_mul, mfderiv_eq_fderiv]
    exact (intrinsicSpatialMetric_pullback g hrotation hcomplete y u v).symm
  have H := P.metric_homothety StandardCapSpace StandardCapSpace G g F.symm
    1 zero_lt_one hmetric
  have hFzero : F.symm 0 = 0 := intrinsicSpatialInverse_zero g hrotation hcomplete
  have hdist := H.edist_eq 0 (F x)
  rw [hFzero, Diffeomorph.symm_apply_apply, Real.sqrt_one, ENNReal.ofReal_one,
    one_mul, intrinsicSpatialMetric_edist_zero] at hdist
  change g.edist 0 x = ENNReal.ofReal ‖intrinsicSpatialCoordinate g x‖ at hdist
  rwa [intrinsicSpatialCoordinate_norm] at hdist

theorem ball_zero_eq_radial_ball (P : M35StandardCapPredecessors) (r : ℝ) :
    g.ball 0 r = Metric.ball 0 ((radialArclengthOrderIso g hrotation hcomplete).symm r) := by
  let F := radialArclengthOrderIso g hrotation hcomplete
  ext x
  change g.edist 0 x < ENNReal.ofReal r ↔
    dist x (0 : StandardCapSpace) < F.symm r
  rw [edist_zero_eq_radialArclength g hrotation hcomplete P, dist_zero_right]
  have hs : 0 ≤ radialArclength g ‖x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg x)
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs]
  change F ‖x‖ < r ↔ ‖x‖ < F.symm r
  constructor
  · intro hx
    simpa only [OrderIso.symm_apply_apply] using F.symm.strictMono hx
  · intro hx
    simpa only [OrderIso.apply_symm_apply] using F.strictMono hx

end PoincareConjecture.M35.Uniqueness
