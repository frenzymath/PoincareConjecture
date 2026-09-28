import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Annulus
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.LevelLocalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem exists_proper_regular_slab_of_small_excess
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p : M) {r₀ r₁ R₀ R₁ T ε η δ a b : ℝ}
    (hT : 0 < T) (hTr : T < r₀) (hr : r₀ < r₁)
    (hrR : r₁ < R₀) (hR : R₀ < R₁)
    (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) (hab : a < b)
    (hinner : r₁ + ε < a) (houter : b < R₀ - ε)
    (hsmall : (δ + 2 * ε) / T +
      (4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η) * T / 2 < 1)
    (hgeo : ∀ x : M, r₁ < (g.edist p x).toReal → (g.edist p x).toReal < R₀ →
      ∃ q : M, T ≤ (g.edist x q).toReal ∧
        (g.edist p x).toReal + (g.edist x q).toReal - (g.edist p q).toReal ≤ δ) :
    let H := 4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η
    let L := 1 - (δ + 2 * ε) / T - H * T / 2
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      IsProperMap ((Set.Ioo a b).restrictPreimage f) ∧
      (∀ x : M, f x ∈ Set.Ioo a b → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      (∀ x : M, f x ∈ Set.Ioo a b →
        r₁ < (g.edist p x).toReal ∧ (g.edist p x).toReal < R₀) ∧
      ∀ x : M, r₁ < (g.edist p x).toReal → (g.edist p x).toReal < R₀ →
        |f x - (g.edist p x).toReal| ≤ ε ∧
        L ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 + η ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian f x v v ≤ H * g.inner x v v := by
  dsimp only
  let H := 4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η
  let L := 1 - (δ + 2 * ε) / T - H * T / 2
  have hL : 0 < L := by dsimp only [L, H]; linarith only [hsmall]
  obtain ⟨u, hu, hub⟩ := g.exists_distance_smoothing_with_excess_control D hc hK hsec
    p (r := r₀) (R := R₁) hT hTr hε hη
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
      (fun x hx hy => (hub x hx hy).1)
  have hbound (x : M) (hx : r₁ < (g.edist p x).toReal)
      (hy : (g.edist p x).toReal < R₀) :
      |f x - (g.edist p x).toReal| ≤ ε ∧
        L ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 + η ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian f x v v ≤ H * g.inner x v v := by
    have hux := hub x (hr.trans hx).le (hy.trans hR).le
    have hlocal := heq x hx hy
    have hgrad : D.gradient f x = D.gradient u x := by
      simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq hlocal]
    obtain ⟨q, hTq, hq⟩ := hgeo x hx hy
    obtain ⟨w, hw, hpair⟩ := hux.2.2.2 q hTq
    have hcs := D.abs_mvfderiv_le_gradient_norm u x w
    rw [← D.inner_gradient, hw, mul_one] at hcs
    have hexc : ((g.edist p x).toReal + (g.edist x q).toReal -
        (g.edist p q).toReal + 2 * ε) / T ≤ (δ + 2 * ε) / T :=
      div_le_div_of_nonneg_right (by linarith) hT.le
    have hlower : L ≤ g.tangentNorm x (D.gradient u x) := by
      have habs := neg_le_abs (g.inner x (D.gradient u x) w)
      dsimp only [L, H]
      linarith
    refine ⟨?_, hgrad ▸ hlower, hgrad ▸ hux.2.1, ?_⟩
    · rw [hlocal.self_of_nhds]
      exact hux.1
    · intro v
      rw [D.hessian_eq_of_eventuallyEq hlocal]
      exact hux.2.2.1 v
  refine ⟨f, hf, hproper, ?_, ?_, hbound⟩
  · intro x hx
    have hxb := hband x hx
    apply (g.tangentNorm_gradient_pos_iff f x).mp
    exact hL.trans_le (hbound x hxb.1 hxb.2.1).2.1
  · intro x hx
    exact ⟨(hband x hx).1, (hband x hx).2.1⟩

end PoincareConjecture.RiemannianMetric
