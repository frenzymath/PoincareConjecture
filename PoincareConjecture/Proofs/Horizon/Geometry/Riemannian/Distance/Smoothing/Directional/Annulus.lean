import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.CompactDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Excess
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

private theorem isCompact_real_distance_annulus
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (a b : ℝ) :
    IsCompact {y : M | a ≤ (g.edist p y).toReal ∧ (g.edist p y).toReal ≤ b} := by
  apply (g.isCompact_closedBall_of_metricComplete hc p b).of_isClosed_subset
  · exact (isClosed_le continuous_const (g.continuous_toReal_edist p)).inter
      (isClosed_le (g.continuous_toReal_edist p) continuous_const)
  · intro y hy
    exact (ENNReal.ofReal_toReal (g.edist_ne_top p y)).symm.le.trans
      (ENNReal.ofReal_le_ofReal hy.2)



theorem exists_distance_smoothing_with_excess_control
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hcomplete : PoincareConjecture.MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p : M) {r R T ε η : ℝ} (hT : 0 < T) (hTr : T < r)
    (hε : 0 < ε) (hη : 0 < η) :
    let H := 4 / (3 * (r - T)) + K * (R + T) / 4 + η
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      ∀ x : M, r ≤ (g.edist p x).toReal → (g.edist p x).toReal ≤ R →
        |rho x - (g.edist p x).toReal| ≤ ε ∧
        g.tangentNorm x (D.gradient rho x) ≤ 1 + η ∧
        (∀ v : TangentSpace (𝓡 n) x, D.hessian rho x v v ≤ H * g.inner x v v) ∧
        ∀ q : M, T ≤ (g.edist x q).toReal →
          ∃ w : TangentSpace (𝓡 n) x, g.tangentNorm x w = 1 ∧
            g.inner x (D.gradient rho x) w ≤
              -1 + ((g.edist p x).toReal + (g.edist x q).toReal -
                (g.edist p q).toReal + 2 * ε) / T + H * T / 2 := by
  dsimp only
  let S : Set M := {y | r - T ≤ (g.edist p y).toReal ∧
    (g.edist p y).toReal ≤ R + T}
  have hS : IsCompact S := isCompact_real_distance_annulus g hcomplete p (r - T) (R + T)
  obtain ⟨rho, hrho, herr, hgrad, hhess⟩ :=
    g.exists_distance_smoothing_on_compact D hcomplete hK hsec p hS
      (sub_pos.mpr hTr) (fun y hy => hy.1) (fun y hy => hy.2) hε hη
  refine ⟨rho, hrho, ?_⟩
  intro x hrx hRx
  have hxS : x ∈ S := ⟨by linarith, by linarith⟩
  refine ⟨herr x hxS, hgrad x hxS, hhess x hxS, ?_⟩
  intro q hTq
  have hball : ∀ y, (g.edist x y).toReal ≤ T → y ∈ S := by
    intro y hy
    have hdist := abs_le.mp (g.abs_toReal_edist_sub_le p x y)
    exact ⟨by linarith [hdist.2], by linarith [hdist.1]⟩
  exact g.exists_opposite_witness_of_distance_approx D hcomplete p x q hT hTq
    hrho (fun y hy => herr y (hball y hy)) (fun y hy => hhess y (hball y hy))

end PoincareConjecture.RiemannianMetric
