import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Excess
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.LevelLocalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

theorem PoincareConjecture.RiemannianMetric.exists_proper_regular_slab_of_prescribed_approximation
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) (p : M)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    {r₀ r₁ R₀ R₁ T ε η δ H a b : ℝ}
    (hT : 0 < T) (hr : r₀ < r₁) (hrR : r₁ < R₀) (hR : R₀ < R₁)
    (ha : 0 < a) (hab : a < b)
    (hinner : r₁ + ε < a) (houter : b < R₀ - ε)
    (hsmall : (δ + 2 * ε) / T + H * T / 2 < 1)
    (hub : ∀ x : M, r₀ - T < (g.edist p x).toReal →
      (g.edist p x).toReal < R₁ + T →
        |u x - (g.edist p x).toReal| ≤ ε ∧
        g.tangentNorm x (D.gradient u x) ≤ 1 + η ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian u x v v ≤ H * g.inner x v v)
    (hgeo : ∀ x : M, r₁ < (g.edist p x).toReal →
      (g.edist p x).toReal < R₀ →
        ∃ q : M, T ≤ (g.edist x q).toReal ∧
          (g.edist p x).toReal + (g.edist x q).toReal -
            (g.edist p q).toReal ≤ δ) :
    let L := 1 - (δ + 2 * ε) / T - H * T / 2
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      IsProperMap ((Set.Ioo a b).restrictPreimage f) ∧
      (∀ x : M, f x ∈ Set.Ioo a b → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      (∀ x : M, f x ∈ Set.Ioo a b →
        r₁ < (g.edist p x).toReal ∧ (g.edist p x).toReal < R₀) ∧
      ∀ x : M, r₁ < (g.edist p x).toReal → (g.edist p x).toReal < R₀ →
        f =ᶠ[𝓝 x] u ∧
        |f x - (g.edist p x).toReal| ≤ ε ∧
        L ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 + η ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian f x v v ≤ H * g.inner x v v := by
  dsimp only
  let L := 1 - (δ + 2 * ε) / T - H * T / 2
  have hL : 0 < L := by dsimp [L]; linarith
  have hcompact (s : ℝ) : IsCompact {x : M | (g.edist p x).toReal ≤ s} := by
    apply (g.isCompact_closedBall_of_metricComplete hc p s).of_isClosed_subset
    · exact isClosed_le (g.continuous_toReal_edist p) continuous_const
    · intro x hx
      exact (ENNReal.ofReal_toReal (g.edist_ne_top p x)).symm.le.trans
        (ENNReal.ofReal_le_ofReal hx)
  obtain ⟨f, S, hf, _, _, heq, hband, hproper⟩ :=
    PoincareConjecture.exists_contMDiff_proper_band_localization
      (fun x => (g.edist p x).toReal) (g.continuous_toReal_edist p) hu
      hr hrR hR ha hab hinner houter (hcompact r₀) (hcompact R₀)
      (fun x hx hy => (hub x (by linarith) (by linarith)).1)
  have hbound (x : M) (hx : r₁ < (g.edist p x).toReal)
      (hy : (g.edist p x).toReal < R₀) :
      f =ᶠ[𝓝 x] u ∧
        |f x - (g.edist p x).toReal| ≤ ε ∧
        L ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 + η ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian f x v v ≤ H * g.inner x v v := by
    have hux := hub x (by linarith) (by linarith)
    have hlocal := heq x hx hy
    have hgrad : D.gradient f x = D.gradient u x := by
      simp only [PoincareConjecture.LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq hlocal]
    obtain ⟨q, hTq, hq⟩ := hgeo x hx hy
    have hball (y : M) (hyT : (g.edist x y).toReal ≤ T) :
        r₀ - T < (g.edist p y).toReal ∧ (g.edist p y).toReal < R₁ + T := by
      have hdist := abs_le.mp (g.abs_toReal_edist_sub_le p x y)
      exact ⟨by linarith [hdist.2], by linarith [hdist.1]⟩
    have hnorm := g.gradient_norm_lower_bound_of_distance_approx D hc p x q hT hTq hu
      (fun y hyT => (hub y (hball y hyT).1 (hball y hyT).2).1)
      (fun y hyT => (hub y (hball y hyT).1 (hball y hyT).2).2.2)
    have hexc : ((g.edist p x).toReal + (g.edist x q).toReal -
        (g.edist p q).toReal + 2 * ε) / T ≤ (δ + 2 * ε) / T :=
      div_le_div_of_nonneg_right (by linarith) hT.le
    have hlower : L ≤ g.tangentNorm x (D.gradient u x) := by
      dsimp [L]
      linarith
    refine ⟨hlocal, ?_, hgrad ▸ hlower, hgrad ▸ hux.2.1, ?_⟩
    · rw [hlocal.self_of_nhds]
      exact hux.1
    · intro v
      rw [D.hessian_eq_of_eventuallyEq hlocal]
      exact hux.2.2 v
  refine ⟨f, hf, hproper, ?_, ?_, hbound⟩
  · intro x hx
    have hxb := hband x hx
    apply (g.tangentNorm_gradient_pos_iff f x).mp
    exact hL.trans_le (hbound x hxb.1 hxb.2.1).2.2.1
  · intro x hx
    exact ⟨(hband x hx).1, (hband x hx).2.1⟩
