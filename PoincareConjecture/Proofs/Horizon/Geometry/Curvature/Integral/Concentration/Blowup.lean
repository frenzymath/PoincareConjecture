import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Selection
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Rescaling

noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

theorem exists_subseq_centers_rescaled_unitBall_scalar_integral_tendsto_atTop
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (p : ∀ j, M j)
    (hn : 2 ≤ n) (hcomplete : ∀ j, MetricComplete (g j))
    (D : ∀ j, LeviCivitaData (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (hlarge : ∀ C : ℝ, ∃ j : ℕ,
      C < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    (c : ℕ → ℝ) (hc : ∀ j, 1 ≤ c j) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ q : ∀ j, M (phi j),
      (∀ j, q j ∈ (g (phi j)).ball (p (phi j)) 1) ∧
      let G := fun j => rescaledMetric (g (phi j)) (c j) (zero_lt_one.trans_le (hc j))
      let DS := fun j => rescaledMetric_connection (g (phi j)) (D (phi j)) (c j)
        (zero_lt_one.trans_le (hc j))
      Tendsto (fun j => ∫ x in (G j).ball (q j) 1,
        (DS j).scalarCurvature x ∂(G j).volumeMeasure) atTop atTop := by
  let r : ℕ → ℝ := fun j => (Real.sqrt (c j))⁻¹
  have hr (j : ℕ) : 0 < r j := inv_pos.mpr
    (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hc j)))
  have hr1 (j : ℕ) : r j ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (hc j))
  let B : ℕ → ℝ := fun j =>
    (⌈RiemannianMetric.modelVolume n 1 3 /
      RiemannianMetric.modelVolume n 1 (r j / 2)⌉₊ : ℝ) *
      ((j : ℝ) + (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 (r j))
  obtain ⟨phi, hphi, hbound⟩ := Poincare.CurvatureIntegral.exists_strictMono_above_thresholds
    (fun j => ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    B hlarge
  have hcenters (j : ℕ) : ∃ q ∈ (g (phi j)).ball (p (phi j)) 1,
      (j : ℝ) < ∫ x in (g (phi j)).ball q (r j),
        (D (phi j)).scalarCurvature x ∂(g (phi j)).volumeMeasure :=
    (D (phi j)).exists_smallBall_scalar_integral_gt (p (phi j)) (by omega)
      (hr j) (hr1 j) (hcomplete (phi j)) (hsec (phi j)) j (hbound j)
  choose q hq hlarge' using hcenters
  refine ⟨phi, hphi, q, hq, ?_⟩
  apply tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
  dsimp only
  have hscale := rescaledMetric_integral_scalarCurvature_ball_mul
    (g (phi j)) (D (phi j)) hn (c j) (zero_lt_one.trans_le (hc j)) (q j) (r j)
  have hs : Real.sqrt (c j) * r j = 1 := mul_inv_cancel₀
    (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hc j))).ne'
  rw [hs] at hscale
  rw [hscale]
  exact (hlarge' j).le.trans (le_mul_of_one_le_left
    ((Nat.cast_nonneg j).trans (hlarge' j).le)
    (one_le_pow₀ (Real.one_le_sqrt.mpr (hc j))))

theorem exists_concentrated_rescaled_pointed_limit_scalar_integral_tendsto_atTop
    {n : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (p : ∀ j, M j)
    (hn : 2 ≤ n) (hcomplete : ∀ j, MetricComplete (g j))
    (D : ∀ j, LeviCivitaData (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (hlarge : ∀ C : ℝ, ∃ j : ℕ,
      C < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    (c : ℕ → ℝ) (hc : ∀ j, 1 ≤ c j) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ q : ∀ j, M (phi j),
      (∀ j, q j ∈ (g (phi j)).ball (p (phi j)) 1) ∧
      let G := fun j => rescaledMetric (g (phi j)) (c j) (zero_lt_one.trans_le (hc j))
      let DS := fun j => rescaledMetric_connection (g (phi j)) (D (phi j)) (c j)
        (zero_lt_one.trans_le (hc j))
      ∃ theta : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
        StrictMono theta ∧ ProperSpace S.completedLimit.carrier ∧
        (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
          γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y) ∧
        PointedGHConvergesUnbounded
          (fun j => (G (theta j)).toBasedMetricSpace (q (theta j))) S.completedLimit ∧
        Tendsto (fun j => ∫ x in (G (theta j)).ball (q (theta j)) 1,
          (DS (theta j)).scalarCurvature x ∂(G (theta j)).volumeMeasure) atTop atTop := by
  obtain ⟨phi, hphi, q, hq, hdiv⟩ :=
    exists_subseq_centers_rescaled_unitBall_scalar_integral_tendsto_atTop
      g p hn hcomplete D hsec hlarge c hc
  obtain ⟨theta, S, htheta, hproper, hgeodesic, hconverges⟩ :=
    exists_subseq_proper_geodesic_pointed_limit_of_metric_rescaling
      (fun j => g (phi j)) q (by omega) (fun j => hcomplete (phi j))
      (fun j => D (phi j)) (fun j => hsec (phi j)) c hc
  exact ⟨phi, hphi, q, hq, theta, S, htheta, hproper, hgeodesic, hconverges,
    hdiv.comp htheta.tendsto_atTop⟩

end PoincareConjecture
