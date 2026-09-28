import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RescaledRankGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.ScalarScaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

theorem exists_rescaled_pointed_limit_with_scalar_divergence_and_rank_growth_at_scaled_spire
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ N : ℕ,
      ∀ {M : ℕ → Type} [∀ j, TopologicalSpace (M j)]
        [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
        [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
        [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
        [∀ j, IsManifold (𝓡 n) ∞ (M j)],
      ∀ (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
        (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
        (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
        (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
          -1 ≤ (D j).sectionalCurvature x v w)
        (p q : ∀ j, M j)
        {V : BasedMetricSpaceBundle.{0}} [ProperSpace V.carrier],
      PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V →
      ∀ {σ cminus c cplus b ρ cap : ℝ},
      0 < σ → 0 ≤ c → c < Real.cos (2 * θ) → cminus < c → c < cplus →
      0 < ρ → ρ < σ * b / 2 → b ≤ cap →
      (∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
        HasLocalDistanceAscent cplus V.base y) →
      ∀ B : V.carrier → ℝ,
      (∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
        (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
          HasLocalDistanceAscent cminus x y) → a ≤ B x) →
      (∀ y : V.carrier, y ≠ V.base → σ * B y ≤ dist y V.base) →
      (∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ) →
      (∀ j, letI := (g j).toMetricSpace
        badAscentRadius c b (q j) ≤ badAscentRadius c b (p j)) →
      (∀ j, letI := (g j).toMetricSpace
        ∀ z : M j, dist (p j) z ≤ ρ →
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z) →
      let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
      Tendsto (fun j => ∫ x in (g j).ball (q j) (4 * a j),
        (D j).scalarCurvature x ∂(g j).volumeMeasure) atTop atTop →
      ∃ φ : ℕ → ℕ, ∃ hpos : ∀ j, 0 < a (φ j),
      let G := fun j => rescaledMetric (g (φ j)) ((4 * a (φ j)) ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hpos j))))
      let DS := fun j => rescaledMetric_connection (g (φ j)) (D (φ j))
        ((4 * a (φ j)) ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hpos j))))
      ∃ S : CompatiblePointedCompactSystem.{0},
        StrictMono φ ∧ (∀ j, 4 * a (φ j) ≤ 1) ∧
        ProperSpace S.completedLimit.carrier ∧
        (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
          γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y) ∧
        PointedGHConvergesUnbounded
          (fun j => (G j).toBasedMetricSpace (q (φ j))) S.completedLimit ∧
        CurvatureGEnegOne S.completedLimit.carrier ∧
        ComparisonAnglePackingBound V.carrier θ N ∧
        ComparisonAnglePackingBound S.completedLimit.carrier θ N ∧
        (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
          ∀ y : S.completedLimit.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
        minLocalAnglePackingRank V.carrier θ <
          minLocalAnglePackingRank S.completedLimit.carrier θ ∧
        Tendsto (fun j => ∫ x in (G j).ball (q (φ j)) 1,
          (DS j).scalarCurvature x ∂(G j).volumeMeasure) atTop atTop := by
  classical
  obtain ⟨N, hN⟩ := exists_rescaled_pointed_limit_with_rank_growth_at_scaled_spire n (by omega) θ hθ hθpi
  refine ⟨N, ?_⟩
  intro M _ _ _ _ _ _ _ g D hcomplete hsec p q V _ holdconv
    σ cminus c cplus b ρ cap hσ hc hcθ hminus hplus hρ hρb hbcap hascent
    B hmax hspire hqball hqref hqmin
  dsimp only
  intro hdiv
  let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiv.eventually (eventually_gt_atTop 0))
  let ψ : ℕ → ℕ := fun j => j + J
  have hψ : StrictMono ψ := fun i j hij => Nat.add_lt_add_right hij J
  have hpos (j : ℕ) : 0 < a (ψ j) := by
    by_contra! hj
    let : ConnectedSpace (M (ψ j)) := { toNonempty := ⟨p (ψ j)⟩ }
    let := (g (ψ j)).toMetricSpace
    have he : (g (ψ j)).ball (q (ψ j)) (4 * a (ψ j)) = ∅ := by
      rw [← (g (ψ j)).toMetricSpace_ball]
      exact Metric.ball_eq_empty.mpr (by linarith only [hj])
    have hlarge := hJ (ψ j) (by dsimp only [ψ]; omega)
    change 0 < ∫ x in (g (ψ j)).ball (q (ψ j)) (4 * a (ψ j)),
      (D (ψ j)).scalarCurvature x ∂(g (ψ j)).volumeMeasure at hlarge
    rw [he, setIntegral_empty] at hlarge
    exact lt_irrefl _ hlarge
  have holdsub : PointedGHConvergesUnbounded
      (fun j => (g (ψ j)).toBasedMetricSpace (p (ψ j))) V := by
    intro r hr
    obtain ⟨δ, hδ, hpositive, ⟨⟨C, hC⟩, hdist⟩⟩ := holdconv r hr
    exact ⟨fun j => δ (ψ j), hδ.comp hψ.tendsto_atTop,
      fun j => hpositive (ψ j), ⟨C, fun j => hC (ψ j)⟩,
      hdist.comp hψ.tendsto_atTop⟩
  obtain ⟨ξ, S, hξ, hsmall, hproper, hgeo, hnew, hcurv, hpackV, hpackY, hgrowth, hrank⟩ :=
    hN (fun j => g (ψ j)) (fun j => D (ψ j)) (fun j => hcomplete (ψ j))
      (fun j => hsec (ψ j)) (fun j => p (ψ j)) (fun j => q (ψ j)) holdsub
      hσ hc hcθ hminus hplus hρ hρb hbcap hascent B hmax hspire
      (fun j => hqball (ψ j)) (fun j => hqref (ψ j)) (fun j => hqmin (ψ j)) hpos
  let φ : ℕ → ℕ := ψ ∘ ξ
  have hφ : StrictMono φ := hψ.comp hξ
  refine ⟨φ, fun j => hpos (ξ j), S, hφ, hsmall, hproper, hgeo, hnew,
    hcurv, hpackV, hpackY, hgrowth, hrank, ?_⟩
  exact tendsto_rescaled_unitBall_scalar_integral_of_tendsto_ball_scalar_integral
    (fun j => g (φ j)) (fun j => D (φ j)) (fun j => q (φ j))
    (fun j => 4 * a (φ j)) hn
    (fun j => mul_pos (by norm_num) (hpos (ξ j)))
    (Eventually.of_forall hsmall) (hdiv.comp hφ.tendsto_atTop)

theorem exists_rescaled_pointed_limit_with_scalar_divergence_and_rank_growth
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ N : ℕ,
      ∀ {M : ℕ → Type} [∀ j, TopologicalSpace (M j)]
        [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
        [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
        [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
        [∀ j, IsManifold (𝓡 n) ∞ (M j)],
      ∀ (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
        (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
        (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
        (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
          -1 ≤ (D j).sectionalCurvature x v w)
        (p q : ∀ j, M j)
        {V : BasedMetricSpaceBundle.{0}} [ProperSpace V.carrier],
      PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V →
      ∀ {cminus c cplus b ρ cap : ℝ},
      0 ≤ c → c < Real.cos (2 * θ) → cminus < c → c < cplus →
      0 < ρ → ρ < b / 2 → b ≤ cap →
      (∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
        HasLocalDistanceAscent cplus V.base y) →
      ∀ B : V.carrier → ℝ,
      (∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
        (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
          HasLocalDistanceAscent cminus x y) → a ≤ B x) →
      (∀ y : V.carrier, y ≠ V.base → B y ≤ dist y V.base) →
      (∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ) →
      (∀ j, letI := (g j).toMetricSpace
        badAscentRadius c b (q j) ≤ badAscentRadius c b (p j)) →
      (∀ j, letI := (g j).toMetricSpace
        ∀ z : M j, dist (p j) z ≤ ρ →
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z) →
      let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
      Tendsto (fun j => ∫ x in (g j).ball (q j) (4 * a j),
        (D j).scalarCurvature x ∂(g j).volumeMeasure) atTop atTop →
      ∃ φ : ℕ → ℕ, ∃ hpos : ∀ j, 0 < a (φ j),
      let G := fun j => rescaledMetric (g (φ j)) ((4 * a (φ j)) ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hpos j))))
      let DS := fun j => rescaledMetric_connection (g (φ j)) (D (φ j))
        ((4 * a (φ j)) ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hpos j))))
      ∃ S : CompatiblePointedCompactSystem.{0},
        StrictMono φ ∧ (∀ j, 4 * a (φ j) ≤ 1) ∧
        ProperSpace S.completedLimit.carrier ∧
        (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
          γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y) ∧
        PointedGHConvergesUnbounded
          (fun j => (G j).toBasedMetricSpace (q (φ j))) S.completedLimit ∧
        CurvatureGEnegOne S.completedLimit.carrier ∧
        ComparisonAnglePackingBound V.carrier θ N ∧
        ComparisonAnglePackingBound S.completedLimit.carrier θ N ∧
        (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
          ∀ y : S.completedLimit.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
        minLocalAnglePackingRank V.carrier θ <
          minLocalAnglePackingRank S.completedLimit.carrier θ ∧
        Tendsto (fun j => ∫ x in (G j).ball (q (φ j)) 1,
          (DS j).scalarCurvature x ∂(G j).volumeMeasure) atTop atTop := by
  obtain ⟨N, hN⟩ := exists_rescaled_pointed_limit_with_scalar_divergence_and_rank_growth_at_scaled_spire
    n hn θ hθ hθpi
  refine ⟨N, ?_⟩
  intro M _ _ _ _ _ _ _ g D hcomplete hsec p q V _ holdconv
    cminus c cplus b ρ cap hc hcθ hminus hplus hρ hρb hbcap hascent
    B hmax hspire hqball hqref hqmin
  exact hN g D hcomplete hsec p q holdconv (σ := 1) zero_lt_one hc hcθ hminus hplus
    hρ (by simpa only [one_mul] using hρb) hbcap hascent B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy)
    hqball hqref hqmin

end PoincareConjecture.RiemannianMetric
