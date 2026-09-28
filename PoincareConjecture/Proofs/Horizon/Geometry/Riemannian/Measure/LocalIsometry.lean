import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Transitions
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [MeasurableSpace N] [BorelSpace N]

theorem volumeMeasure_image_eq_of_injOn_metric_pullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) {f : M → N}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w))
    {U s : Set M} (hU : IsOpen U) (hinj : InjOn f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    h.volumeMeasure (f '' s) = g.volumeMeasure s := by
  classical
  rcases isEmpty_or_nonempty M with hempty | hnonempty
  · simp only [eq_empty_of_isEmpty s, image_empty, measure_empty]
  have hbij (x : M) : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) :=
    g.mfderiv_bijective_of_pullback_eq h x (fun v w => (hinner x v w).symm)
  have hlocal := Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hf hbij
  let e : OpenPartialHomeomorph M N := OpenPartialHomeomorph.ofContinuousOpen
    (hinj.toPartialEquiv f U) hf.continuous.continuousOn hlocal.isOpenMap hU
  have heq : (e : M → N) = f := rfl
  have he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source := hf.of_le (by simp) |>.contMDiffOn
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target := by
    rintro y ⟨x, hx, rfl⟩
    have hleft : ∀ᶠ z in 𝓝 x, e.symm (f z) = z := by
      filter_upwards [hU.mem_nhds hx] with z hz
      exact e.left_inv hz
    exact ((Poincare.contMDiffAt_of_local_left_inverse (hf x) (hbij x)
      hleft).of_le (by simp)).contMDiffWithinAt
  have hnorm (x : M) (v : TangentSpace (𝓡 n) x) :
      g.tangentNorm x v = h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) :=
    congrArg Real.sqrt (hinner x v v)
  have hupper := g.volumeMeasure_image_le_of_tangentNorm_le h e hU
    (show U ⊆ e.source from Subset.rfl) he (by norm_num : (0 : ℝ) < 1)
    (fun z _ v => by rw [← hnorm]; simp) hs hsU
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  have hinverse := g.inverse_tangentNorm_le_of_le h e hD
    (show U ⊆ e.source from Subset.rfl)
    (C := 1) (fun z _ v => by rw [hnorm]; simp)
  have hinverse' : ∀ z ∈ e.target, ∀ v : TangentSpace (𝓡 n) z,
      g.tangentNorm (e.symm z) (mfderiv (𝓡 n) (𝓡 n) e.symm z v) ≤
        1 * h.tangentNorm z v := hinverse
  have hlower := g.volumeMeasure_le_image_of_inverse_tangentNorm_le h e hei
    (by norm_num : (0 : ℝ) < 1) hinverse' hs hsU
  exact le_antisymm (by simpa only [heq, ENNReal.ofReal_one, one_pow, one_mul] using hupper)
    (by simpa only [heq, ENNReal.ofReal_one, one_pow, one_mul] using hlower)



theorem volumeMeasure_ball_le_of_injOn_metric_pullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) {f : M → N}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (p : M) (r : ℝ) (hinj : InjOn f (g.ball p r)) :
    g.volumeMeasure (g.ball p r) ≤ h.volumeMeasure (h.ball (f p) r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hball : IsOpen (g.ball p r) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  rw [← g.volumeMeasure_image_eq_of_injOn_metric_pullback h hf hinner
    hball hinj hball.measurableSet Subset.rfl]
  apply measure_mono
  rintro _ ⟨x, hx, rfl⟩
  exact (g.edist_map_le_of_metric_pullback h hf hinner p x).trans_lt hx

end PoincareConjecture.RiemannianMetric
