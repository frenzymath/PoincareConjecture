import PoincareConjecture.Proofs.M35.Thm12_28.CapCompactness










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M35

private theorem continuousOn_closedBall_sup {X : Type*} [MetricSpace X]
    [ProperSpace X] (x : X) (f : X → ℝ) (hf : Continuous f)
    (hproject : ∀ (R r e : ℝ), 0 ≤ r → r ≤ R → 0 < e →
      closedBall x R ⊆ thickening (R - r + e) (closedBall x r)) :
    ContinuousOn (fun r => sSup (f '' closedBall x r)) (Ici 0) := by
  have hbounded (r : ℝ) : BddAbove (f '' closedBall x r) :=
    (isCompact_closedBall x r).bddAbove_image hf.continuousOn
  have hnonempty (r : ℝ) (hr : 0 ≤ r) : (f '' closedBall x r).Nonempty :=
    (nonempty_closedBall.mpr hr).image f
  intro r hr
  apply Metric.continuousWithinAt_iff.mpr
  intro e he
  obtain ⟨d, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall x (r + 1)).uniformContinuousOn_of_continuous hf.continuousOn)
    (e / 2) (half_pos he)
  let a := min 1 (d / 4)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have had : a ≤ d / 4 := min_le_right _ _
  refine ⟨a, ha, ?_⟩
  intro s hs hsr
  have hsr' : |s - r| < a := by simpa only [Real.dist_eq] using hsr
  have hsR : s ≤ r + 1 := by linarith [(abs_lt.mp hsr').2]
  have hcompare (R q : ℝ) (hq : 0 ≤ q) (hqR : q ≤ R)
      (hR : R ≤ r + 1) (hgap : R - q < a) :
      sSup (f '' closedBall x R) ≤ sSup (f '' closedBall x q) + e / 2 := by
    apply csSup_le (hnonempty R (hq.trans hqR))
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp
      (hproject R q a hq hqR ha hy)
    have hyK : y ∈ closedBall x (r + 1) := closedBall_subset_closedBall hR hy
    have hzK : z ∈ closedBall x (r + 1) :=
      closedBall_subset_closedBall (hqR.trans hR) hz
    have hyzd : dist y z < d := by linarith
    have hfv := hclose y hyK z hzK hyzd
    have hvalue : f z ≤ sSup (f '' closedBall x q) :=
      le_csSup (hbounded q) (mem_image_of_mem f hz)
    rw [Real.dist_eq] at hfv
    linarith [(abs_lt.mp hfv).2]
  have hmono (R q : ℝ) (hq : 0 ≤ q) (hqR : q ≤ R) :
      sSup (f '' closedBall x q) ≤ sSup (f '' closedBall x R) :=
    csSup_le_csSup (hbounded R) (hnonempty q hq)
      (image_mono (closedBall_subset_closedBall hqR))
  rw [Real.dist_eq]
  apply abs_lt.mpr
  rcases le_total s r with h | h
  · have hc := hcompare r s hs h (by linarith) (by linarith [(abs_lt.mp hsr').1])
    have hm := hmono r s hs h
    constructor <;> linarith
  · have hc := hcompare s r hr h hsR (by linarith [(abs_lt.mp hsr').2])
    have hm := hmono s r hr h
    constructor <;> linarith

private theorem closure_ball_eq_of_radial_projection {X : Type*} [MetricSpace X]
    (x : X) {r : ℝ} (hr : 0 < r)
    (hproject : ∀ (R q e : ℝ), 0 ≤ q → q ≤ R → 0 < e →
      closedBall x R ⊆ thickening (R - q + e) (closedBall x q)) :
    closure (ball x r) = closedBall x r := by
  apply Subset.antisymm closure_ball_subset_closedBall
  intro y hy
  apply Metric.mem_closure_iff.mpr
  intro e he
  let a := min (r / 2) (e / 4)
  have ha : 0 < a := lt_min (half_pos hr) (by positivity)
  have har : a ≤ r / 2 := min_le_left _ _
  have hae : a ≤ e / 4 := min_le_right _ _
  obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp
    (hproject r (r - a) a (by linarith) (by linarith) ha hy)
  refine ⟨z, ?_, ?_⟩
  · exact lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)
  · simpa only [dist_comm] using (show dist y z < e by linarith)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [ConnectedSpace M]



theorem riemannian_closure_ball (g : RiemannianMetric 3 M) (x : M)
    {r : ℝ} (hr : 0 < r) :
    letI : MetricSpace M := Proofs.M09.selectedMetricSpace g
    closure (g.ball x r) = Metric.closedBall x r := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have hball : g.ball x r = Metric.ball x r := by
    ext y
    change g.edist x y < ENNReal.ofReal r ↔ dist y x < r
    rw [← Proofs.M09.selectedMetricSpace_edist g, edist_dist, dist_comm]
    exact ENNReal.ofReal_lt_ofReal_iff hr
  rw [hball]
  exact closure_ball_eq_of_radial_projection x hr
    (Proofs.M09.selectedMetricSpace_radial_projection g x)



theorem continuousOn_scalar_closedBall_sup (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hR : Continuous D.scalarCurvature) (x : M) :
    letI : MetricSpace M := Proofs.M09.selectedMetricSpace g
    ContinuousOn (fun r => sSup (D.scalarCurvature '' Metric.closedBall x r)) (Ici 0) := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have : ProperSpace M := Proofs.M09.selectedMetricSpace_proper g hcomplete
  exact continuousOn_closedBall_sup x D.scalarCurvature hR
    (Proofs.M09.selectedMetricSpace_radial_projection g x)



theorem scalar_ball_sup_eq_closedBall (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hR : Continuous D.scalarCurvature) (x : M) {r : ℝ} (hr : 0 < r) :
    letI : MetricSpace M := Proofs.M09.selectedMetricSpace g
    scalarCurvatureSupOn g D (g.ball x r) =
      sSup (D.scalarCurvature '' Metric.closedBall x r) := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have : ProperSpace M := Proofs.M09.selectedMetricSpace_proper g hcomplete
  have hclosure := riemannian_closure_ball g x hr
  have hsub : g.ball x r ⊆ Metric.closedBall x r := by
    rw [← hclosure]
    exact subset_closure
  have hclosed : BddAbove (D.scalarCurvature '' Metric.closedBall x r) :=
    (isCompact_closedBall x r).bddAbove_image hR.continuousOn
  have hbounded : BddAbove (D.scalarCurvature '' g.ball x r) :=
    hclosed.mono (image_mono hsub)
  have hx : x ∈ g.ball x r := by
    change g.edist x x < ENNReal.ofReal r
    rw [← Proofs.M09.selectedMetricSpace_edist g, edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hnonempty : (D.scalarCurvature '' g.ball x r).Nonempty :=
    (show (g.ball x r).Nonempty from ⟨x, hx⟩).image _
  have hbound : ∀ y ∈ g.ball x r,
      D.scalarCurvature y ≤ sSup (D.scalarCurvature '' g.ball x r) :=
    fun y hy => le_csSup hbounded (mem_image_of_mem _ hy)
  have hboundClosure : ∀ y ∈ closure (g.ball x r),
      D.scalarCurvature y ≤ sSup (D.scalarCurvature '' g.ball x r) :=
    closure_minimal hbound (isClosed_le hR continuous_const)
  change sSup (range fun z : g.ball x r => D.scalarCurvature z.1) = _
  rw [← image_eq_range]
  apply le_antisymm (csSup_le_csSup hclosed hnonempty (image_mono hsub))
  apply csSup_le ((nonempty_closedBall.mpr hr.le).image _)
  rintro _ ⟨y, hy, rfl⟩
  exact hboundClosure y (hclosure.symm ▸ hy)




theorem exists_scalar_curvature_radius_le (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hR : Continuous D.scalarCurvature) (x : M) {b : ℝ} (hb : 0 < b)
    (hcross : 1 ≤ b ^ 2 * scalarCurvatureSupOn g D (g.ball x b)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ b ∧
      scalarCurvatureSupOn g D (g.ball x r) = r⁻¹ ^ 2 ∧
        IsCompact (closure (g.ball x r)) := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  let S (r : ℝ) := sSup (D.scalarCurvature '' Metric.closedBall x r)
  have hS : ContinuousOn S (Ici 0) :=
    continuousOn_scalar_closedBall_sup g D hcomplete hR x
  have hF : ContinuousOn (fun r => r ^ 2 * S r) (Icc 0 b) :=
    (continuousOn_id.pow 2).mul (hS.mono Icc_subset_Ici_self)
  have htarget : (1 : ℝ) ∈ Icc ((0 : ℝ) ^ 2 * S 0) (b ^ 2 * S b) := by
    constructor
    · norm_num
    · simpa only [S, ← scalar_ball_sup_eq_closedBall g D hcomplete hR x hb] using hcross
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc hb.le hF htarget
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr.1
    intro h
    simp only [← h, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul] at heq
    norm_num at heq
  refine ⟨r, hrpos, hr.2, ?_, Proofs.M09.isCompact_closure_metric_ball g hcomplete x r⟩
  rw [scalar_ball_sup_eq_closedBall g D hcomplete hR x hrpos]
  change S r = r⁻¹ ^ 2
  have hmul : r ^ 2 * S r = 1 := heq
  apply (mul_left_cancel₀ (pow_ne_zero 2 hrpos.ne'))
  rw [hmul, ← mul_pow, mul_inv_cancel₀ hrpos.ne', one_pow]

end PoincareConjecture.M35
