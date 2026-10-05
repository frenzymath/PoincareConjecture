import PoincareLib.Geometry.Riemannian.Surface.Boundary

/-!
# The metric norm bound for surface turning

The quarter-turn of a metric-unit vector in an orthonormal surface frame
has unit length. Cauchy--Schwarz bounds its turning coefficient by the
metric norm of the covariant derivative. This is the pointwise estimate
used for Morgan--Tian, Claim 19.39 and Lemma 19.46, pp. 470 and 474-475;
see `proof-work/tasks/M64/derivations/2026-09-25-boundary-arc-turning.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

/-- In an orthonormal surface frame, the absolute turning coefficient of
a unit field is bounded by the metric norm of its covariant derivative.
This supplies the pointwise boundary-turning estimate for Morgan--Tian,
Claim 19.39 and Lemma 19.46, pp. 470 and 474-475. -/
theorem abs_surfaceTurningForm_le_tangentNorm (D : LeviCivitaData g)
    (e1 e2 T V : (x : S) → TangentSpace (𝓡 2) x) (x : S)
    (he1 : g.inner x (e1 x) (e1 x) = 1)
    (he2 : g.inner x (e2 x) (e2 x) = 1)
    (horth : g.inner x (e1 x) (e2 x) = 0)
    (hT : g.inner x (T x) (T x) = 1) :
    |D.surfaceTurningForm e1 e2 T V x| ≤
      g.tangentNorm x (D.connection T x (V x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let N := -g.inner x (T x) (e2 x) • e1 x + g.inner x (T x) (e1 x) • e2 x
  have horth' : g.inner x (e2 x) (e1 x) = 0 := by
    rw [g.symm]
    exact horth
  have hcoeff := (g.inner_self_eq_frameCoordinates_sq x he1 he2 horth (T x)).symm.trans hT
  have hN : g.inner x N N = 1 := by
    simp only [N, map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      he1, he2, horth, horth', mul_one, mul_zero, add_zero, zero_add]
    nlinarith only [hcoeff]
  have hNnorm : g.tangentNorm x N = 1 := by
    rw [RiemannianMetric.tangentNorm, hN, Real.sqrt_one]
  have hbound : |g.inner x (D.connection T x (V x)) N| ≤
      g.tangentNorm x (D.connection T x (V x)) * g.tangentNorm x N := by
    have h := abs_real_inner_le_norm (D.connection T x (V x)) N
    simpa only [norm_eq_sqrt_real_inner, RiemannianMetric.tangentNorm] using! h
  change |g.inner x (D.connection T x (V x)) N| ≤
    g.tangentNorm x (D.connection T x (V x))
  simpa only [hNnorm, mul_one] using hbound

end PoincareMT.LeviCivitaData
