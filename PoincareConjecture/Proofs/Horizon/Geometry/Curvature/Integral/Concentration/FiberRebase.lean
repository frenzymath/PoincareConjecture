import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.Pointed
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.SuppliedRebase

noncomputable section
open Set Filter Topology
open Poincare.GromovHausdorff
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PoincareConjecture.RiemannianMetric

theorem exists_openFiber_lifts_rebased_limit_of_expanding_realizations
    {m k : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) (M j)]
    [∀ j, IsManifold (𝓡 (m+k)) ∞ (M j)]
    (g : ∀ j, RiemannianMetric (m+k) (M j))
    (hc : ∀ j, MetricComplete (g j))
    (f : ∀ j, M j → Fin k → ℝ)
    (U : ∀ j, TopologicalSpace.Opens (M j)) (c : ℕ → Fin k → ℝ)
    (p : ∀ j, openFiber (f j) (U j) (c j))
    {Y : BasedMetricSpaceBundle.{0}} [ProperSpace Y.carrier]
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
          dist (γ a) (γ b) = |a-b| * dist x y)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    {s t ε : ℕ → ℝ} (hs : ∀ j, ρ < s j) (ht : ∀ j, ρ < t j)
    (hsTop : Tendsto s atTop atTop) (htTop : Tendsto t atTop atTop)
    (hε : Tendsto ε atTop (𝓝 0)) :
    let incl := fun j => openFiberIncl (f j) (U j) (c j)
    let X := fun j => (g j).toBasedMetricSpace (incl j (p j))
    let E := fun j => incl j '' {z : openFiber (f j) (U j) (c j) |
      ((g j).edist (incl j (p j)) (incl j z)).toReal ≤ ρ}
    ∀ Q : ∀ j, PointedGHRealization
        (ballModel (X j) (s j) (hρ.trans_lt (hs j)))
        (ballModel Y (t j) (hρ.trans_lt (ht j))),
      Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0) →
      ∀ (K : Set Y.carrier) (hK : K ⊆ Metric.closedBall Y.base ρ),
      (∀ j (y : K), ∃ x : E j,
        dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr (by
          obtain ⟨z, hz, heq⟩ := x.property
          rw [← heq]
          exact hz.trans_lt (hs j))⟩)
          ((Q j).right ⟨y.val, Metric.mem_ball.mpr
            ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) →
      ∀ y : K, ∃ q : ∀ j, openFiber (f j) (U j) (c j),
        ∃ hq : ∀ j, ((g j).edist (incl j (p j)) (incl j (q j))).toReal ≤ ρ,
          (∀ j,
            dist ((Q j).left ⟨incl j (q j),
                Metric.mem_ball'.mpr ((hq j).trans_lt (hs j))⟩)
              ((Q j).right ⟨y.val, Metric.mem_ball.mpr
                ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) ∧
          Tendsto (fun j => ((g j).edist (incl j (p j)) (incl j (q j))).toReal)
            atTop (𝓝 (dist Y.base y.val)) ∧
          PointedGHConvergesUnbounded
            (fun j => (g j).toBasedMetricSpace (incl j (q j))) (Y.rebase y.val) := by
  classical
  dsimp only
  intro Q hQ K hK hback y
  let incl := fun j => openFiberIncl (f j) (U j) (c j)
  let X := fun j => (g j).toBasedMetricSpace (incl j (p j))
  choose x hx using fun j => hback j y
  choose q hq heq using fun j => (x j).property
  let a (j : ℕ) : (ballModel (X j) (s j) (hρ.trans_lt (hs j))).carrier :=
    ⟨incl j (q j), Metric.mem_ball'.mpr ((hq j).trans_lt (hs j))⟩
  let b (j : ℕ) : (ballModel Y (t j) (hρ.trans_lt (ht j))).carrier :=
    ⟨y.val, Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩
  have hcross (j : ℕ) : dist ((Q j).left (a j)) ((Q j).right (b j)) < ε j := by
    simpa only [a, b, incl, heq] using hx j
  have hab : Tendsto (fun j => dist ((Q j).left (a j)) ((Q j).right (b j)))
      atTop (𝓝 0) :=
    squeeze_zero (fun j => dist_nonneg) (fun j => (hcross j).le) hε
  have hrad : Tendsto (fun j => ((g j).edist (incl j (p j)) (incl j (q j))).toReal)
      atTop (𝓝 (dist Y.base y.val)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hε.eventually_lt_const hη] with j hj
    have h := abs_dist_base_sub_dist_base_lt_of_corresponding (Q j) (a j) (b j)
      (hcross j)
    change |((g j).edist (incl j (p j)) (incl j (q j))).toReal -
      dist Y.base y.val| < ε j at h
    simpa only [Real.dist_eq] using h.trans hj
  let (j : ℕ) : ProperSpace (X j).carrier := (g j).properSpace_toMetricSpace (hc j)
  have hgeo (j : ℕ) (v w : (X j).carrier) :
      ∃ γ : ℝ → (X j).carrier, γ 0 = v ∧ γ 1 = w ∧
        ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
          dist (γ a) (γ b) = |a-b| * dist v w := by
    obtain ⟨_, _, γ, _, h0, h1, hmin⟩ :=
      (g j).exists_minimizing_geodesic_of_metricComplete (hc j) v w
    refine ⟨γ, h0, h1, ?_⟩
    intro a ha b hb
    change ((g j).edist (γ a) (γ b)).toReal = |a-b| * ((g j).edist v w).toReal
    rw [hmin a ha b hb, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  refine ⟨q, hq, hcross, hrad, ?_⟩
  exact pointedGHConvergesUnbounded_rebase_of_expanding_realizations
    hgeo hYgeo (fun j => hρ.trans_lt (hs j)) (fun j => hρ.trans_lt (ht j))
    hsTop htTop Q hQ a b y.val (Eventually.of_forall fun _ => rfl) hab

end PoincareConjecture.RiemannianMetric
