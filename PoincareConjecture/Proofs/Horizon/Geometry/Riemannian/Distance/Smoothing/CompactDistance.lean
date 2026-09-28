import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Quantitative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

private theorem exists_local_distance_smoothing_of_annulus
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p x : M) {r R : ℝ} (hr : 0 < r)
    (hrx : r ≤ (g.edist p x).toReal) (hRx : (g.edist p x).toReal ≤ R)
    {η : ℝ} (hη : 0 < η) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ rho : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
        (∀ y ∈ U, |rho y - (g.edist p y).toReal| ≤ ε) ∧
        (∀ y ∈ U, g.tangentNorm y (D.gradient rho y) ≤ 1 + η) ∧
        ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
          D.hessian rho y v v ≤
            (4 / (3 * r) + K * R / 4 + η) * g.inner y v v := by
  have hpx : p ≠ x := by
    intro heq
    rw [← heq] at hrx
    simp only [edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero] at hrx
    linarith
  obtain ⟨U, hU, hxU, _, hlocal⟩ :=
    g.exists_local_distance_smoothing_with_bounds D hcomplete hK hsec p x hpx hη
  have hinv : 4 / (3 * (g.edist p x).toReal) ≤ 4 / (3 * r) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hrx (by norm_num))
  have hcurv : K * (g.edist p x).toReal / 4 ≤ K * R / 4 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRx hK) (by norm_num)
  refine ⟨U, hU, hxU, ?_⟩
  intro ε hε
  obtain ⟨rho, hrho, herr, hgrad, hhess⟩ := hlocal ε hε
  refine ⟨rho, hrho, herr, hgrad, ?_⟩
  intro y hy v
  apply (hhess y hy v).trans
  apply mul_le_mul_of_nonneg_right (by linarith :
    4 / (3 * (g.edist p x).toReal) + K * (g.edist p x).toReal / 4 + η ≤
      4 / (3 * r) + K * R / 4 + η)
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos y v hv).le

theorem exists_distance_smoothing_on_compact
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p : M) {S : Set M} (hS : IsCompact S)
    {r R : ℝ} (hr : 0 < r)
    (hrS : ∀ x ∈ S, r ≤ (g.edist p x).toReal)
    (hRS : ∀ x ∈ S, (g.edist p x).toReal ≤ R)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      (∀ x ∈ S, |rho x - (g.edist p x).toReal| ≤ ε) ∧
      (∀ x ∈ S, g.tangentNorm x (D.gradient rho x) ≤ 1 + η) ∧
      ∀ x ∈ S, ∀ v : TangentSpace (𝓡 n) x,
        D.hessian rho x v v ≤ (4 / (3 * r) + K * R / 4 + η) * g.inner x v v := by
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨rho, hrho, herr, hgrad, hhess⟩ :=
    D.exists_contMDiff_approx_on_compact_of_local hS (g.continuous_toReal_edist p).continuousOn
      (L := 1 + η / 2) (H := 4 / (3 * r) + K * R / 4 + η / 2)
      (by linarith)
      (fun x hx => exists_local_distance_smoothing_of_annulus g D hcomplete hK hsec
        p x hr (hrS x hx) (hRS x hx) hhalf)
      hε hhalf
  refine ⟨rho, hrho, herr, ?_, ?_⟩
  · intro x hx
    simpa only [show (1 + η / 2) + η / 2 = 1 + η by ring] using hgrad x hx
  · intro x hx v
    simpa only [show (4 / (3 * r) + K * R / 4 + η / 2) + η / 2 =
      4 / (3 * r) + K * R / 4 + η by ring] using hhess x hx v

end PoincareConjecture.RiemannianMetric
