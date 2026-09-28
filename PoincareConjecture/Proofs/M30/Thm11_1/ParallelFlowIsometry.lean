import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.MetricExpansion.Variation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

theorem flow_preserves_metric_of_parallel
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x} {Φ : ℝ → M → M}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ x, ∀ a : TangentSpace (𝓡 n) x, D.connection V x a = 0)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    (hΦ : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) V)
    (h0 : ∀ x, Φ 0 x = x)
    (t : ℝ) (x : M) (a b : TangentSpace (𝓡 n) x) :
    g.inner (Φ t x) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x a)
      (mfderiv (𝓡 n) (𝓡 n) (Φ t) x b) = g.inner x a b := by
  have hfun : Φ 0 = id := funext h0
  have hid : mfderiv (𝓡 n) (𝓡 n) (Φ 0) x = ContinuousLinearMap.id ℝ _ := by
    rw [hfun]
    exact mfderiv_id
  have hdiag (v : TangentSpace (𝓡 n) x) :
      g.inner (Φ t x) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) = g.inner x v v := by
    have hd (s : ℝ) : HasDerivAt (fun r => g.inner (Φ r x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ r) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ r) x v)) 0 s := by
      simpa only [hparallel, map_zero, zero_apply, mul_zero] using
        D.hasDerivAt_manifoldFlow_squared_length hV hs hΦ x v s
    have heq := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    rw [hid, h0] at heq
    exact heq
  have hp := hdiag (a + b)
  simp only [map_add, add_apply] at hp
  rw [g.symm (Φ t x) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x b)
    (mfderiv (𝓡 n) (𝓡 n) (Φ t) x a), g.symm x b a] at hp
  linarith [hdiag a, hdiag b]

end PoincareConjecture.M30
