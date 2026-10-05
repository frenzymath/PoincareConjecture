import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.LocalInverse
import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.ReturnedLoop

/-!
# The local short-loop alternative

A smooth nonsingular Gauss parametrization has a first collision on each
compact ball where injectivity fails. The two colliding radii are equal and
their terminal radial velocities are opposite. For an exponential family,
this produces an actual nonzero returning radial geodesic.

Reference: the localized Klingenberg argument supporting Morgan--Tian,
Theorem 1.36, p. 20. Nonsingularity and Gauss' identity are supplied by the
radial Jacobi and metric-compatibility arguments for the same exponential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Noninjectivity has an attained positive first collision with opposite
terminal radial velocities. The smooth inverse branches are constructed. -/
theorem exists_first_collision_with_opposite_velocities
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {R r : ℝ} (hrR : r < R)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ z ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f z))
    (hgauss : ∀ z ∈ Metric.ball 0 R, ∀ a : EuclideanSpace ℝ (Fin n),
      g.inner (f z) (mfderiv (𝓡 n) (𝓡 n) f z z)
        (mfderiv (𝓡 n) (𝓡 n) f z a) = inner ℝ z a)
    (hnot : ¬ InjOn f (Metric.closedBall 0 r)) :
    ∃ v w : EuclideanSpace ℝ (Fin n),
      0 < ‖v‖ ∧ ‖v‖ ≤ r ∧ ‖w‖ = ‖v‖ ∧ v ≠ w ∧ f v = f w ∧
      mfderiv (𝓡 n) (𝓡 n) f v v = -mfderiv (𝓡 n) (𝓡 n) f w w := by
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  have hlocal (z) (hz : z ∈ Metric.closedBall 0 r) : ∃ U ∈ 𝓝 z, InjOn f U := by
    obtain ⟨e, hez, _, heq, _, _⟩ :=
      exists_smooth_inverse_branch Metric.isOpen_ball hf hbij (hsub hz)
    exact ⟨e.source, e.open_source.mem_nhds hez, e.injOn.congr heq⟩
  obtain ⟨v, hv, w, hw, heq, hne, hpos, hmin⟩ :=
    exists_minimal_collision (hf.continuousOn.mono hsub) hlocal hnot
  obtain ⟨ev, hvs, _, hev, hvsmooth, hvismooth⟩ :=
    exists_smooth_inverse_branch Metric.isOpen_ball hf hbij (hsub hv)
  obtain ⟨ew, hws, _, hew, hwsmooth, hwismooth⟩ :=
    exists_smooth_inverse_branch Metric.isOpen_ball hf hbij (hsub hw)
  have hvle : ‖v‖ ≤ r := by simpa using hv
  have hwle : ‖w‖ ≤ r := by simpa using hw
  have hnorm := norm_eq_of_minimal_collision hvle hwle heq hne
    ((hf.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hv))).continuousAt)
    ((hf.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hw))).continuousAt)
    ev ew hvs hws hev.symm hew.symm hmin
  have hevd (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) ev v a = mfderiv (𝓡 n) (𝓡 n) f v a := by
    have h := (hev.eventuallyEq_of_mem (ev.open_source.mem_nhds hvs)).mfderiv_eq
      (I := 𝓡 n) (I' := 𝓡 n)
    exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A a) h
  have hewd (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) ew w a = mfderiv (𝓡 n) (𝓡 n) f w a := by
    have h := (hew.eventuallyEq_of_mem (ew.open_source.mem_nhds hws)).mfderiv_eq
      (I := 𝓡 n) (I' := 𝓡 n)
    exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A a) h
  have hreturn := g.radial_velocities_eq_neg_of_minimal_collision hvle hwle heq hne
    ev ew hvs hws hev.symm hew.symm hvsmooth hwsmooth hvismooth hwismooth
    (by intro a; rw [hevd, hevd]; exact hgauss v (hsub hv) a)
    (by intro a; rw [hewd, hewd]; rw [heq]; exact hgauss w (hsub hw) a) hmin
  refine ⟨v, w, ?_, hvle, hnorm.symm, hne, heq, ?_⟩
  · simpa only [hnorm, max_self] using hpos
  · exact (hevd v).symm.trans (hreturn.trans (congrArg Neg.neg (hewd w)))

/-- Failure of injectivity in a smaller ball produces a nonzero returning
ray of the very same exponential, at radius at most twice that ball's radius. -/
theorem exists_returning_radial_vector_of_not_injOn
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R r : ℝ} (hr : 0 < r) (hrR : 2 * r < R)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hbij : ∀ z ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e z))
    (hgauss : ∀ z ∈ Metric.ball 0 R, ∀ a : EuclideanSpace ℝ (Fin n),
      g.inner (e z) (mfderiv (𝓡 n) (𝓡 n) e z z)
        (mfderiv (𝓡 n) (𝓡 n) e z a) = inner ℝ z a)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hnot : ¬ InjOn e (Metric.closedBall 0 r)) :
    ∃ v : EuclideanSpace ℝ (Fin n),
      0 < ‖v‖ ∧ ‖v‖ ≤ r ∧ e ((2 : ℝ) • v) = e 0 := by
  have hrR' : r < R := by linarith
  obtain ⟨v, w, hvpos, hv, hnorm, _, heq, hvel⟩ :=
    g.exists_first_collision_with_opposite_velocities hrR' he hbij hgauss hnot
  have hvmem : v ∈ Metric.ball 0 R := by simpa using hv.trans_lt hrR'
  have hwm : ‖w‖ < R := hnorm ▸ hv.trans_lt hrR'
  exact ⟨v, hvpos, hv, g.exponential_double_eq_zero_of_opposite_radial_velocities
    he ((mul_le_mul_of_nonneg_left hv (by norm_num)).trans_lt hrR) hwm
    (hgeo v hvmem) (hgeo w (by simpa using hwm)) heq hvel⟩

end PoincareMT.RiemannianMetric
