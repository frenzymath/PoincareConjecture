import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Spire
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Rescaling










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

private theorem one_le_inv_radius_sq {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    1 ≤ (r ^ 2)⁻¹ :=
  (one_le_inv₀ (sq_pos_of_pos hr)).mpr (by nlinarith only [hr, hr1])




theorem exists_subseq_prescribed_center_rescaled_unitBall_scalar_integral_tendsto_atTop
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι : Type*} [Fintype ι]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (q : ∀ j, ι → M j) (r : ℕ → ι → ℝ)
    (hn : 2 ≤ n) (hr : ∀ k i, 0 < r k i) (hr1 : ∀ k i, r k i ≤ 1)
    (hranti : ∀ i, Antitone (fun k => r k i))
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (C : ℕ → ℝ) (houtside : ∀ k j,
      (∫ x in (g j).ball (p j) 1 \ ⋃ i, (g j).ball (q j i) (r k i),
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C k)
    (hlarge : ∀ B : ℝ, ∃ j,
      B < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    (scale : ℕ → ℕ) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      let G := fun j => rescaledMetric (g (phi j)) (r (scale j) i ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (hr (scale j) i)))
      let DS := fun j => rescaledMetric_connection (g (phi j)) (D (phi j))
        (r (scale j) i ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos (hr (scale j) i)))
      Tendsto (fun j => ∫ x in (G j).ball (q (phi j) i) 1,
        (DS j).scalarCurvature x ∂(G j).volumeMeasure) atTop atTop := by
  obtain ⟨i, phi, hphi, hdiv⟩ :=
    exists_subseq_prescribed_center_scalar_integral_tendsto_atTop_at_scales
      g D p q r (by omega) hr hranti hcomplete hsec C houtside hlarge scale
  refine ⟨i, phi, hphi, ?_⟩
  apply tendsto_atTop_mono' atTop ?_ hdiv
  filter_upwards [hdiv.eventually (eventually_ge_atTop 0)] with j hj
  have hc := one_le_inv_radius_sq (hr (scale j) i) (hr1 (scale j) i)
  have hscale := rescaledMetric_integral_scalarCurvature_ball_mul
    (g (phi j)) (D (phi j)) hn (r (scale j) i ^ 2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (hr (scale j) i))) (q (phi j) i) (r (scale j) i)
  have hs : Real.sqrt (r (scale j) i ^ 2)⁻¹ * r (scale j) i = 1 := by
    rw [Real.sqrt_inv, Real.sqrt_sq (hr (scale j) i).le]
    exact inv_mul_cancel₀ (hr (scale j) i).ne'
  rw [hs] at hscale
  rw [hscale]
  exact le_mul_of_one_le_left hj (one_le_pow₀ (Real.one_le_sqrt.mpr hc))



theorem exists_prescribed_center_rescaled_pointed_limit_scalar_integral_tendsto_atTop
    {n : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι : Type*} [Fintype ι]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (q : ∀ j, ι → M j) (r : ℕ → ι → ℝ)
    (hn : 2 ≤ n) (hr : ∀ k i, 0 < r k i) (hr1 : ∀ k i, r k i ≤ 1)
    (hranti : ∀ i, Antitone (fun k => r k i))
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (C : ℕ → ℝ) (houtside : ∀ k j,
      (∫ x in (g j).ball (p j) 1 \ ⋃ i, (g j).ball (q j i) (r k i),
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C k)
    (hlarge : ∀ B : ℝ, ∃ j,
      B < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    (scale : ℕ → ℕ) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      let G := fun j => rescaledMetric (g (phi j)) (r (scale j) i ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (hr (scale j) i)))
      let DS := fun j => rescaledMetric_connection (g (phi j)) (D (phi j))
        (r (scale j) i ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos (hr (scale j) i)))
      ∃ theta : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
        StrictMono theta ∧ ProperSpace S.completedLimit.carrier ∧
        (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
          γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y) ∧
        PointedGHConvergesUnbounded
          (fun j => (G (theta j)).toBasedMetricSpace (q (phi (theta j)) i)) S.completedLimit ∧
        Tendsto (fun j => ∫ x in (G (theta j)).ball (q (phi (theta j)) i) 1,
          (DS (theta j)).scalarCurvature x ∂(G (theta j)).volumeMeasure) atTop atTop := by
  obtain ⟨i, phi, hphi, hdiv⟩ :=
    exists_subseq_prescribed_center_rescaled_unitBall_scalar_integral_tendsto_atTop
      g D p q r hn hr hr1 hranti hcomplete hsec C houtside hlarge scale
  have hc (j : ℕ) : 1 ≤ (r (scale j) i ^ 2)⁻¹ :=
    one_le_inv_radius_sq (hr (scale j) i) (hr1 (scale j) i)
  obtain ⟨theta, S, htheta, hproper, hgeodesic, hconverges⟩ :=
    exists_subseq_proper_geodesic_pointed_limit_of_metric_rescaling
      (fun j => g (phi j)) (fun j => q (phi j) i) (by omega)
      (fun j => hcomplete (phi j)) (fun j => D (phi j)) (fun j => hsec (phi j))
      (fun j => (r (scale j) i ^ 2)⁻¹) hc
  exact ⟨i, phi, hphi, theta, S, htheta, hproper, hgeodesic, hconverges,
    hdiv.comp htheta.tendsto_atTop⟩

end PoincareConjecture
