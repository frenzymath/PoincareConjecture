import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.Pointed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.ExpandingRealizations
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.ExpandingSubsets








noncomputable section

open Set Filter Topology
open Poincare.GromovHausdorff
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PoincareConjecture.RiemannianMetric

private theorem pointedGHConvergesUnbounded_comp
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    (h : PointedGHConvergesUnbounded X Y) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    PointedGHConvergesUnbounded (fun j => X (φ j)) Y := by
  intro r hr
  obtain ⟨δ, hδ, hpos, ⟨⟨C, hC⟩, hdist⟩⟩ := h r hr
  exact ⟨fun j => δ (φ j), hδ.comp hφ, fun j => hpos (φ j),
    ⟨C, fun j => hC (φ j)⟩, hdist.comp hφ⟩



theorem exists_subseq_compact_openFiber_limit_in_expanding_realizations
    {m k : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) (M j)]
    [∀ j, IsManifold (𝓡 (m+k)) ∞ (M j)]
    (g : ∀ j, RiemannianMetric (m+k) (M j))
    (D : ∀ j, LeviCivitaData (g j))
    (hc : ∀ j, MetricComplete (g j)) (hn : 1 ≤ m+k)
    (hsec : ∀ j x (v w : TangentSpace (𝓡 (m+k)) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (f : ∀ j, M j → Fin k → ℝ) (hf : ∀ j, Continuous (f j))
    (U : ∀ j, TopologicalSpace.Opens (M j)) (c : ℕ → Fin k → ℝ)
    (p : ∀ j, openFiber (f j) (U j) (c j)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    let incl := fun j => openFiberIncl (f j) (U j) (c j)
    let X := fun j => (g j).toBasedMetricSpace (incl j (p j))
    let E := fun j => incl j '' {z : openFiber (f j) (U j) (c j) |
      ((g j).edist (incl j (p j)) (incl j z)).toReal ≤ ρ}
    ∃ φ : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
      StrictMono φ ∧ ProperSpace S.completedLimit.carrier ∧
      (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
        γ 0 = x ∧ γ 1 = y ∧
        ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
          dist (γ a) (γ b) = |a-b| * dist x y) ∧
      PointedGHConvergesUnbounded (fun j => X (φ j)) S.completedLimit ∧
      ∃ s t ε : ℕ → ℝ,
        Tendsto s atTop atTop ∧ Tendsto t atTop atTop ∧
        (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∃ hs : ∀ j, ρ < s j, ∃ ht : ∀ j, ρ < t j,
        ∃ Q : ∀ j, PointedGHRealization
          (ballModel (X (φ j)) (s j) (hρ.trans_lt (hs j)))
          (ballModel S.completedLimit (t j) (hρ.trans_lt (ht j))),
        Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0) ∧
        ∃ K : TopologicalSpace.NonemptyCompacts S.completedLimit.carrier,
        ∃ hK : (K : Set S.completedLimit.carrier) ⊆ Metric.closedBall S.completedLimit.base ρ,
          S.completedLimit.base ∈ K ∧
          (∀ j (x : E (φ j)), ∃ y : K,
            dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr (by
              obtain ⟨z, hz, heq⟩ := x.property
              rw [← heq]
              exact hz.trans_lt (hs j))⟩)
              ((Q j).right ⟨y.val, Metric.mem_ball.mpr
                ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) ∧
          (∀ j (y : K), ∃ x : E (φ j),
            dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr (by
              obtain ⟨z, hz, heq⟩ := x.property
              rw [← heq]
              exact hz.trans_lt (hs j))⟩)
              ((Q j).right ⟨y.val, Metric.mem_ball.mpr
                ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) := by
  classical
  let incl := fun j => openFiberIncl (f j) (U j) (c j)
  let X := fun j => (g j).toBasedMetricSpace (incl j (p j))
  let E := fun j => incl j '' {z : openFiber (f j) (U j) (c j) |
    ((g j).edist (incl j (p j)) (incl j z)).toReal ≤ ρ}
  dsimp only
  have hbound (j : ℕ) (x : (X j).carrier) (hx : x ∈ E j) :
      dist (X j).base x ≤ ρ := by
    obtain ⟨z, hz, rfl⟩ := hx
    exact hz
  have hbase (j : ℕ) : (X j).base ∈ E j := by
    refine ⟨p j, ?_, rfl⟩
    change dist (X j).base (X j).base ≤ ρ
    simpa only [dist_self] using hρ
  obtain ⟨φ₀, S, hφ₀, hproper, hgeo, hconv⟩ :=
    exists_subseq_proper_geodesic_pointed_limit_of_ricci_lower_bound
      g (fun j => incl j (p j)) hn 1 (by norm_num) hc D
      (fun j x v => (D j).ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound
        x 1 (hsec j x) v)
  let : ProperSpace S.completedLimit.carrier := hproper
  obtain ⟨φ₁, hφ₁, s, hjs, hs, Q, hQ⟩ :=
    exists_subseq_expanding_pointed_realizations hconv
  let t : ℕ → ℝ := fun j => (j : ℝ) + 2
  have ht (j : ℕ) : 0 < t j := by dsimp [t]; positivity
  have hsTop : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun j => (hjs j).le)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have htTop : Tendsto t atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hQzero : Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => pointedHausdorffDist_nonneg (Q j)) (fun j => (hQ j).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨φ₂, K, ε, hφ₂, hεpos, hεzero, hρs, hρt, hK, hfwd, hback⟩ :=
    exists_subseq_nonempty_compact_limit_of_expanding_bounded_subsets
      s t hs ht hsTop htTop Q hQzero (fun j => E (φ₀ (φ₁ j)))
      (fun j => ⟨_, hbase (φ₀ (φ₁ j))⟩)
      (fun j x hx => hbound (φ₀ (φ₁ j)) x hx)
  let φ := fun j => φ₀ (φ₁ (φ₂ j))
  have hφ : StrictMono φ := hφ₀.comp (hφ₁.comp hφ₂)
  have hconv' : PointedGHConvergesUnbounded (fun j => X (φ j)) S.completedLimit :=
    pointedGHConvergesUnbounded_comp hconv (fun j => φ₁ (φ₂ j))
      (hφ₁.comp hφ₂).tendsto_atTop
  have hbaseK : S.completedLimit.base ∈ K := by
    let x (j : ℕ) : E (φ₀ (φ₁ (φ₂ j))) := ⟨_, hbase _⟩
    choose y hy using fun j => hfwd j (x j)
    have hynear (j : ℕ) : dist (y j).val S.completedLimit.base < ε j := by
      have hh := hy j
      have hleft : (Q (φ₂ j)).left
          ⟨(x j).val, Metric.mem_ball'.mpr
            ((hbound _ (x j).val (x j).property).trans_lt (hρs j))⟩ =
          (Q (φ₂ j)).ambient.base := (Q (φ₂ j)).left_base
      rw [hleft, ← (Q (φ₂ j)).right_base] at hh
      rw [(Q (φ₂ j)).right_isometry.dist_eq] at hh
      change dist S.completedLimit.base (y j).val < ε j at hh
      simpa only [dist_comm] using hh
    have hyconv : Tendsto (fun j => (y j).val) atTop (𝓝 S.completedLimit.base) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun j => dist_nonneg) (fun j => (hynear j).le) hεzero
    exact K.isCompact.isClosed.mem_of_tendsto hyconv (Eventually.of_forall fun j => (y j).property)
  refine ⟨φ, S, hφ, hproper, hgeo, hconv',
    fun j => s (φ₂ j), fun j => t (φ₂ j), ε,
    hsTop.comp hφ₂.tendsto_atTop, htTop.comp hφ₂.tendsto_atTop, hεpos, hεzero,
    hρs, hρt, (fun j => Q (φ₂ j)), hQzero.comp hφ₂.tendsto_atTop,
    K, hK, hbaseK, ?_, ?_⟩
  · exact hfwd
  · exact hback


end PoincareConjecture.RiemannianMetric
