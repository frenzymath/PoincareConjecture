import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.PointSelection
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {b : ℝ} (F : RicciFlow 3 M (Iic b))

private theorem continuous_terminal_scalar
    (P : M23NormalizedKappaCompactnessPredecessors) :
    Continuous (F.connection b).scalarCurvature := by
  apply continuousOn_univ.mp
  exact (P.scalar_regular M (Iic b) F).continuousOn.comp
    (f := fun x : M => (b, x))
    (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => ⟨by simp only [mem_Iic, le_refl], mem_univ x⟩)

theorem exists_backward_controlled_point_of_m23_predecessors
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : MetricComplete (F.metric b))
    (hop : ∀ s ≤ b, ∀ y, (F.connection s).NonnegativeCurvatureOperator y)
    (hmono : ∀ s ≤ b, ∀ y,
      (F.connection s).scalarCurvature y ≤ (F.connection b).scalarCurvature y)
    (p x : M) (hd : 0 < ((F.metric b).edist p x).toReal)
    (hx : 0 < (F.connection b).scalarCurvature x) :
    let g := F.metric b
    let R := (F.connection b).scalarCurvature
    ∃ q : M, ∃ r : ℝ, q ∈ g.ball x ((g.edist p x).toReal / 2) ∧
      0 < r ∧ R x ≤ R q ∧ (g.edist p x).toReal / 2 ≤ (g.edist p q).toReal ∧
      r * Real.sqrt (R q) = (g.edist p x).toReal * Real.sqrt (R x) / 4 ∧
      g.ball q r ⊆ g.ball x ((g.edist p x).toReal / 2) ∧
      (∀ y ∈ g.ball q r, R y ≤ 4 * R q) ∧
      ∀ s ≤ b, ∀ y ∈ g.ball q r,
        |(F.connection s).curvatureTensorNorm y| ≤ 4 * R q := by
  let g := F.metric b
  let R := (F.connection b).scalarCurvature
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hc
  have hdist (u v : M) : dist u v = (g.edist u v).toReal := rfl
  have hnorm (s : ℝ) (hs : s ≤ b) (y : M) :
      (F.connection s).curvatureTensorNorm y ≤ (F.connection s).scalarCurvature y :=
    (F.connection s).curvatureTensorNorm_le_scalarCurvature_sharp
      (P.tensor_calculus 3 M (F.metric s) (F.connection s)) y (hop s hs y)
  have hR (y : M) : 0 ≤ R y := (Real.sqrt_nonneg _).trans (hnorm b le_rfl y)
  obtain ⟨q, r, hq, hr, hRq, hdistq, hscale, hsubset, hcontrol⟩ :=
    Poincare.AncientVolume.exists_curvature_controlled_point_of_continuous R hR
      (F.continuous_terminal_scalar P) p x hd hx
  simp only [hdist, g.toMetricSpace_ball] at hq hdistq hscale hsubset hcontrol
  refine ⟨q, r, hq, hr, hRq, hdistq, hscale, hsubset, hcontrol, ?_⟩
  intro s hs y hy
  rw [abs_of_nonneg (show 0 ≤ (F.connection s).curvatureTensorNorm y from
    Real.sqrt_nonneg _)]
  exact (hnorm s hs y).trans ((hmono s hs y).trans (hcontrol y hy))

theorem exists_escaping_backward_controlled_sequence_of_m23_predecessors
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : MetricComplete (F.metric b))
    (hop : ∀ s ≤ b, ∀ y, (F.connection s).NonnegativeCurvatureOperator y)
    (hmono : ∀ s ≤ b, ∀ y,
      (F.connection s).scalarCurvature y ≤ (F.connection b).scalarCurvature y)
    (p : M) (hunbounded : ¬ BddAbove (range (F.connection b).scalarCurvature)) :
    let g := F.metric b
    let R := (F.connection b).scalarCurvature
    ∃ (q : ℕ → M) (r : ℕ → ℝ),
      (∀ i, 0 < R (q i) ∧ 0 < r i ∧
        (∀ y ∈ g.ball (q i) (r i), R y ≤ 4 * R (q i)) ∧
        ∀ s ≤ b, ∀ y ∈ g.ball (q i) (r i),
          |(F.connection s).curvatureTensorNorm y| ≤ 4 * R (q i)) ∧
      Tendsto (fun i => (g.edist p (q i)).toReal) atTop atTop ∧
      Tendsto (fun i => R (q i)) atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => (g.edist p (q i)).toReal * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => r i / (g.edist p (q i)).toReal) atTop (𝓝 0) := by
  classical
  let g := F.metric b
  let R := (F.connection b).scalarCurvature
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hc
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  have hchoose (i : ℕ) : ∃ q : M, ∃ r : ℝ,
      0 < R q ∧ 0 < r ∧
      (∀ y ∈ g.ball q r, R y ≤ 4 * R q) ∧
      (∀ s ≤ b, ∀ y ∈ g.ball q r,
        |(F.connection s).curvatureTensorNorm y| ≤ 4 * R q) ∧
      (i : ℝ) ≤ (g.edist p q).toReal ∧ (i : ℝ) ≤ R q ∧
      (i : ℝ) ≤ r * Real.sqrt (R q) ∧
      (i : ℝ) ≤ (g.edist p q).toReal * Real.sqrt (R q) ∧
      r / (g.edist p q).toReal ≤ 1 / ((i : ℝ) + 1) := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall p (2 * ((i : ℝ) + 1) ^ 2)).bddAbove_image
      (F.continuous_terminal_scalar P).continuousOn
    obtain ⟨v, ⟨x, rfl⟩, hx⟩ := not_bddAbove_iff.mp hunbounded (max B (max (i : ℝ) 16))
    have hxB : B < R x := lt_of_le_of_lt (le_max_left _ _) hx
    have hxi : (i : ℝ) < R x :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hx
    have hx16 : 16 < R x :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hx
    have hxoutside : x ∉ Metric.closedBall p (2 * ((i : ℝ) + 1) ^ 2) := by
      intro hxmem
      exact (not_le_of_gt hxB) (hB (mem_image_of_mem _ hxmem))
    have hdlarge : 2 * ((i : ℝ) + 1) ^ 2 < (g.edist p x).toReal := by
      simpa only [Metric.mem_closedBall, dist_comm x p, hdist, not_le] using hxoutside
    have hd : 0 < (g.edist p x).toReal := by
      nlinarith [sq_nonneg ((i : ℝ) + 1)]
    have hxpos : 0 < (F.connection b).scalarCurvature x := by
      change 0 < R x
      linarith
    obtain ⟨q, r, _, hr, hRxq, hdistq, hscale, _, hcontrol, hpast⟩ :=
      F.exists_backward_controlled_point_of_m23_predecessors P hc hop hmono p x hd hxpos
    have hqx : 0 < R q := hxpos.trans_le hRxq
    have hrootx : 4 < Real.sqrt (R x) := by
      have hs := Real.sq_sqrt (show 0 ≤ R x by linarith)
      nlinarith [Real.sqrt_nonneg (R x)]
    have hrootq : 1 ≤ Real.sqrt (R q) := by
      have hs := Real.sqrt_le_sqrt hRxq
      linarith
    have hi : 0 < (i : ℝ) + 1 := by positivity
    have hi1 : 1 ≤ (i : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have hqdist : (i : ℝ) ≤ (g.edist p q).toReal := by nlinarith
    have hdqpos : 0 < (g.edist p q).toReal := by linarith
    have hrupper : r ≤ (g.edist p q).toReal := by
      have hsxq := Real.sqrt_le_sqrt hRxq
      have hmul := mul_le_mul_of_nonneg_left hsxq hd.le
      have hsqpos : 0 < Real.sqrt (R q) := Real.sqrt_pos.mpr hqx
      nlinarith [hscale]
    let a := r / ((i : ℝ) + 1)
    have ha : 0 < a := div_pos hr hi
    have har : a ≤ r := div_le_self hr.le hi1
    refine ⟨q, a, hqx, ha, ?_, ?_, hqdist, hxi.le.trans hRxq, ?_, ?_, ?_⟩
    · intro y hy
      exact hcontrol y (lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal har))
    · intro s hs y hy
      exact hpast s hs y (lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal har))
    · have hmul := mul_le_mul_of_nonneg_left hrootx.le hd.le
      have hscaleLarge : ((i : ℝ) + 1) ^ 2 ≤ r * Real.sqrt (R q) := by
        linarith
      have hdiv := div_le_div_of_nonneg_right hscaleLarge hi.le
      have hcancel : ((i : ℝ) + 1) ^ 2 / ((i : ℝ) + 1) = (i : ℝ) + 1 := by
        field_simp
      rw [hcancel] at hdiv
      calc
        (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
        _ ≤ r * Real.sqrt (R q) / ((i : ℝ) + 1) := hdiv
        _ = a * Real.sqrt (R q) := by dsimp [a]; ring
    · exact hqdist.trans (le_mul_of_one_le_right ENNReal.toReal_nonneg hrootq)
    · apply (div_le_iff₀ hdqpos).mpr
      calc
        a ≤ (g.edist p q).toReal / ((i : ℝ) + 1) :=
          div_le_div_of_nonneg_right hrupper hi.le
        _ = (1 / ((i : ℝ) + 1)) * (g.edist p q).toReal := by ring
  choose q r hpos hr hcontrol hpast hdistq hscalar hscale hscaledDist hratio using hchoose
  refine ⟨q, r, fun i => ⟨hpos i, hr i, hcontrol i, hpast i⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono hdistq tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscalar tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscale tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscaledDist tendsto_natCast_atTop_atTop
  · apply squeeze_zero (fun i => div_nonneg (hr i).le ENNReal.toReal_nonneg) hratio
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun i => show (i : ℝ) ≤ (i : ℝ) + 1 by linarith) tendsto_natCast_atTop_atTop)

end PoincareConjecture.RicciFlow
