import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

private theorem exists_radial_variation_domain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {v : E} (hv : v ∈ Metric.ball 0 R) (w : E) :
    ∃ S : Set ℝ, ∃ a : ℝ, IsOpen S ∧ (0 : ℝ) ∈ S ∧ 1 < a ∧
      (∀ s ∈ S, v + s • w ∈ Metric.ball 0 R) ∧
      ∀ s ∈ S, ∀ t ∈ Ioo (-a) a, t • (v + s • w) ∈ Metric.ball 0 R := by
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hvR) ‖v‖
  let a := 1 + δ
  let S : Set ℝ := {s | a * ‖v + s • w‖ < R}
  have ha : 1 < a := by dsimp [a]; linarith
  have hS : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℝ) ∈ S := by
    simp only [S, mem_ofPred_eq, zero_smul, add_zero]
    dsimp [a]
    nlinarith
  refine ⟨S, a, hS, h0, ha, ?_, ?_⟩
  · intro s hs
    rw [Metric.mem_ball, dist_zero_right]
    exact (le_mul_of_one_le_left (norm_nonneg _) ha.le).trans_lt hs
  · intro s hs t ht
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (abs_lt.mpr ht).le (norm_nonneg _)).trans_lt hs

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem radialVariation_jacobi
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {R : ℝ} {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (w : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let γ : ℝ → M := fun τ => e (τ • v)
    let J : (τ : ℝ) → TangentSpace (𝓡 n) (γ τ) :=
      fun τ => mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
        (fun s : ℝ => e (τ • (v + s • w))) 0 1
    ConnectionVariation.manifoldCovDerivAlong g γ
        (ConnectionVariation.manifoldCovDerivAlong g γ J 1) 1 t +
      D.curvature (γ t) (J t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) = 0 := by
  obtain ⟨S, a, hS, h0, ha, hvelocity, hdomain⟩ := exists_radial_variation_domain hv w
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z : ℝ × ℝ => e (z.2 • (v + z.1 • w))) (S ×ˢ Ioo (-a) a) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact fun z hz => hdomain z.1 hz.1 z.2 hz.2
  have hvariation : ∀ s ∈ S,
      g.IsGeodesicOn (fun t : ℝ => e (t • (v + s • w))) (Ioo (-a) a) := by
    intro s hs τ hτ
    exact hgeo _ (hvelocity s hs) τ (hdomain s hs τ hτ)
  have ht' : t ∈ Ioo (-a) a := by constructor <;> linarith [ht.1, ht.2]
  have hjac :=
    ConnectionVariation.manifoldVariation_jacobi g D hS isOpen_Ioo h0 hsmooth hvariation ht'
  dsimp only at hjac
  rw [show v + (0 : ℝ) • w = v by simp] at hjac
  exact hjac

end PoincareConjecture.RiemannianMetric
