import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.PointPicking
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field























set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace Poincare.AncientVolume


theorem exists_curvature_controlled_point
    {X : Type*} [PseudoMetricSpace X]
    (R : X → ℝ) (hR : ∀ y, 0 ≤ R y) (hbounded : BddAbove (range R))
    (p x : X) (hd : 0 < dist p x) (hx : 0 < R x) :
    ∃ q : X, ∃ r : ℝ, q ∈ Metric.ball x (dist p x / 2) ∧
      0 < r ∧ R x ≤ R q ∧ dist p x / 2 ≤ dist p q ∧
      r * Real.sqrt (R q) = dist p x * Real.sqrt (R x) / 4 ∧
      Metric.ball q r ⊆ Metric.ball x (dist p x / 2) ∧
      ∀ y ∈ Metric.ball q r, R y ≤ 4 * R q := by
  let f : X → ℝ := fun y => Real.sqrt (R y)
  let L : ℝ := dist p x * f x / 4
  have hfx : 0 < f x := Real.sqrt_pos.mpr hx
  have hL : 0 < L := by dsimp [L]; positivity
  have hbound : BddAbove (f '' (univ : Set X)) := by
    obtain ⟨B, hB⟩ := hbounded
    refine ⟨Real.sqrt B, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact Real.sqrt_le_sqrt (hB (mem_range_self y))
  obtain ⟨q, _, _, hscore, hmargin, hcontrol⟩ :=
    Poincare.Parabolic.exists_point_with_doubling_bound univ f (dist x)
      (fun _ => 0) hbound hL.le (mem_univ x) hfx
  have hfq : 0 < f q := hfx.trans_le hscore
  let r : ℝ := L / f q
  have hr : 0 < r := div_pos hL hfq
  have hbudget : dist x q + 2 * r ≤ dist p x / 2 := by
    have hcancel : 2 * L / f x = dist p x / 2 := by
      dsimp [L]
      field_simp
      ring
    simpa only [dist_self, zero_add, hcancel, mul_div_assoc] using hmargin
  have hq : q ∈ Metric.ball x (dist p x / 2) := by
    rw [Metric.mem_ball, dist_comm]
    linarith
  refine ⟨q, r, hq, hr, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.sqrt_le_sqrt_iff (hR q)).mp hscore
  · have htri := dist_triangle p q x
    have hqx := Metric.mem_ball.mp hq
    linarith
  · dsimp [r, L]
    rw [div_mul_cancel₀ _ hfq.ne']
  · intro y hy
    have hqy : dist q y < r := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have htri := dist_triangle x q y
    rw [Metric.mem_ball, dist_comm]
    linarith
  · intro y hy
    have hqy : dist q y < r := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have hfy : f y ≤ 2 * f q := hcontrol y (mem_univ y) le_rfl (by
      have htri := dist_triangle x q y
      dsimp [r] at hqy
      linarith)
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg (R y)) hfy
    dsimp [f] at hsq
    nlinarith [Real.sq_sqrt (hR y), Real.sq_sqrt (hR q)]




theorem exists_escaping_curvature_controlled_sequence
    {X : Type*} [PseudoMetricSpace X]
    (R : X → ℝ) (hR : ∀ y, 0 ≤ R y) (hbounded : BddAbove (range R))
    (p : X) (hunbounded : ¬ BddAbove (range (fun x => dist p x ^ 2 * R x))) :
    ∃ q : ℕ → X, ∃ r : ℕ → ℝ,
      (∀ i, 0 < R (q i) ∧ 0 < r i ∧
        ∀ y ∈ Metric.ball (q i) (r i), R y ≤ 4 * R (q i)) ∧
      Tendsto (fun i => dist p (q i)) atTop atTop ∧
      Tendsto r atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => dist p (q i) * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => r i / dist p (q i)) atTop (𝓝 0) ∧
      BddAbove (range (fun i => R (q i))) := by
  classical
  obtain ⟨B, hB⟩ := hbounded
  let C : ℝ := max B 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCpos
  have hsC1 : 1 ≤ Real.sqrt C := by
    simpa using Real.sqrt_le_sqrt hC
  have hbound (x : X) : R x ≤ C := (hB (mem_range_self x)).trans (le_max_left _ _)
  have hchoose (i : ℕ) : ∃ q : X, ∃ r : ℝ,
      0 < R q ∧ 0 < r ∧
      (∀ y ∈ Metric.ball q r, R y ≤ 4 * R q) ∧
      (i : ℝ) ≤ dist p q ∧ (i : ℝ) ≤ r ∧ (i : ℝ) ≤ r * Real.sqrt (R q) ∧
      (i : ℝ) ≤ dist p q * Real.sqrt (R q) ∧ r / dist p q ≤ 1 / ((i : ℝ) + 1) := by
    have hi : 0 < (i : ℝ) + 1 := by positivity
    have hi1 : 1 ≤ (i : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    let A : ℝ := ((i : ℝ) + 1) ^ 2
    have hA : (i : ℝ) + 1 ≤ A := by dsimp [A]; nlinarith
    obtain ⟨v, ⟨x, rfl⟩, hxlarge⟩ := not_bddAbove_iff.mp hunbounded
      ((4 * A * Real.sqrt C) ^ 2)
    have hxprod : 0 < dist p x ^ 2 * R x := lt_of_le_of_lt (sq_nonneg _) hxlarge
    have hx : 0 < R x := pos_of_mul_pos_right hxprod (sq_nonneg _)
    have hd : 0 < dist p x := by
      by_contra hn
      have hz : dist p x = 0 := le_antisymm (not_lt.mp hn) dist_nonneg
      simp [hz] at hxprod
    have hscore : 4 * A * Real.sqrt C < dist p x * Real.sqrt (R x) := by
      apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
      simpa only [mul_pow, Real.sq_sqrt (hR x)] using hxlarge
    obtain ⟨q, r, _, hr, hRx, hdist, hscale, _, hcontrol⟩ :=
      exists_curvature_controlled_point R hR ⟨B, hB⟩ p x hd hx
    have hRq : 0 < R q := hx.trans_le hRx
    have hsr : Real.sqrt (R q) ≤ Real.sqrt C := Real.sqrt_le_sqrt (hbound q)
    have hsx : Real.sqrt (R x) ≤ Real.sqrt C := Real.sqrt_le_sqrt (hbound x)
    have hrlarge : A < r := by
      have hmul := mul_le_mul_of_nonneg_left hsr hr.le
      have hscaled : A * Real.sqrt C < r * Real.sqrt C := by
        linarith [hscale]
      exact (mul_lt_mul_iff_left₀ hsC).mp hscaled
    have hdlarge : 4 * A < dist p x := by
      have hmul := mul_le_mul_of_nonneg_left hsx hd.le
      exact (mul_lt_mul_iff_left₀ hsC).mp (hscore.trans_le hmul)
    have hscaleLarge : A ≤ r * Real.sqrt (R q) := by
      have hm := mul_le_mul_of_nonneg_left hsC1 (show 0 ≤ A by positivity)
      nlinarith [hscale]
    have hrupper : r ≤ dist p q := by
      have hsxq := Real.sqrt_le_sqrt hRx
      have hmul := mul_le_mul_of_nonneg_left hsxq hd.le
      have hsqpos : 0 < Real.sqrt (R q) := Real.sqrt_pos.mpr hRq
      nlinarith [hscale]
    let s : ℝ := r / ((i : ℝ) + 1)
    have hs : 0 < s := div_pos hr hi
    have hsr : s ≤ r := (div_le_self hr.le hi1)
    have hslarge : (i : ℝ) + 1 < s := by
      apply (lt_div_iff₀ hi).mpr
      dsimp [A] at hrlarge
      nlinarith
    have hsscale : (i : ℝ) ≤ s * Real.sqrt (R q) := by
      have h := (div_le_div_of_nonneg_right hscaleLarge hi.le)
      have hAdiv : A / ((i : ℝ) + 1) = (i : ℝ) + 1 := by
        dsimp [A]
        field_simp
      rw [hAdiv] at h
      calc
        (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
        _ ≤ r * Real.sqrt (R q) / ((i : ℝ) + 1) := h
        _ = s * Real.sqrt (R q) := by dsimp [s]; ring
    have hdqpos : 0 < dist p q := by linarith
    refine ⟨q, s, hRq, hs, ?_, by linarith, by linarith, hsscale, ?_, ?_⟩
    · intro y hy
      exact hcontrol y (Metric.ball_subset_ball hsr hy)
    · exact hsscale.trans (mul_le_mul_of_nonneg_right (hsr.trans hrupper)
        (Real.sqrt_nonneg _))
    · apply (div_le_iff₀ hdqpos).mpr
      calc
        s ≤ dist p q / ((i : ℝ) + 1) := div_le_div_of_nonneg_right hrupper hi.le
        _ = (1 / ((i : ℝ) + 1)) * dist p q := by ring
  choose q r hpos hr hcontrol hdist hrlarge hscale hscaledDist hratio using hchoose
  refine ⟨q, r, fun i => ⟨hpos i, hr i, hcontrol i⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono hdist tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hrlarge tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscale tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscaledDist tendsto_natCast_atTop_atTop
  · apply squeeze_zero (fun i => div_nonneg (hr i).le dist_nonneg) hratio
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun i => show (i : ℝ) ≤ (i : ℝ) + 1 by linarith) tendsto_natCast_atTop_atTop)
  · refine ⟨B, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hB (mem_range_self (q i))

end Poincare.AncientVolume

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]



theorem exists_curvature_controlled_point
    (g : RiemannianMetric n M) (R : M → ℝ) (hR : ∀ y, 0 ≤ R y)
    (hbounded : BddAbove (range R)) (p x : M)
    (hd : 0 < (g.edist p x).toReal) (hx : 0 < R x) :
    ∃ q : M, ∃ r : ℝ, q ∈ g.ball x ((g.edist p x).toReal / 2) ∧
      0 < r ∧ R x ≤ R q ∧ (g.edist p x).toReal / 2 ≤ (g.edist p q).toReal ∧
      r * Real.sqrt (R q) = (g.edist p x).toReal * Real.sqrt (R x) / 4 ∧
      g.ball q r ⊆ g.ball x ((g.edist p x).toReal / 2) ∧
      ∀ y ∈ g.ball q r, R y ≤ 4 * R q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace (g.edist_ne_top)
  have hdist (a b : M) : dist a b = (g.edist a b).toReal := rfl
  have hball (z : M) (s : ℝ) : Metric.ball z s = g.ball z s := by
    ext y
    change dist y z < s ↔ g.edist z y < ENNReal.ofReal s
    rw [dist_comm]
    exact edist_lt_ofReal.symm
  simpa only [hball, hdist] using
    Poincare.AncientVolume.exists_curvature_controlled_point R hR hbounded p x hd hx



theorem exists_escaping_curvature_controlled_sequence
    (g : RiemannianMetric n M) (R : M → ℝ) (hR : ∀ y, 0 ≤ R y)
    (hbounded : BddAbove (range R)) (p : M)
    (hunbounded : ¬ BddAbove (range (fun x => (g.edist p x).toReal ^ 2 * R x))) :
    ∃ q : ℕ → M, ∃ r : ℕ → ℝ,
      (∀ i, 0 < R (q i) ∧ 0 < r i ∧
        ∀ y ∈ g.ball (q i) (r i), R y ≤ 4 * R (q i)) ∧
      Tendsto (fun i => (g.edist p (q i)).toReal) atTop atTop ∧
      Tendsto r atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => (g.edist p (q i)).toReal * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => r i / (g.edist p (q i)).toReal) atTop (𝓝 0) ∧
      BddAbove (range (fun i => R (q i))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace (g.edist_ne_top)
  have hdist (a b : M) : dist a b = (g.edist a b).toReal := rfl
  have hball (z : M) (s : ℝ) : Metric.ball z s = g.ball z s := by
    ext y
    change dist y z < s ↔ g.edist z y < ENNReal.ofReal s
    rw [dist_comm]
    exact edist_lt_ofReal.symm
  simpa only [hball, hdist] using
    Poincare.AncientVolume.exists_escaping_curvature_controlled_sequence
      R hR hbounded p hunbounded

end PoincareConjecture.RiemannianMetric
