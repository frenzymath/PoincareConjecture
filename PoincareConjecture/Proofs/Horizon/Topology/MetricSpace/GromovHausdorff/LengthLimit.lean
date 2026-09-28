import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.Curves.Midpoints
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.Assembly
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.Transitions
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Extraction.Radial

open Set Metric Filter Topology

noncomputable section

namespace Poincare.GromovHausdorff

universe u

private theorem exact_split_of_compact_approximation
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] (x y : Y) (r : ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ z : Y,
      dist x z < r + ε ∧ dist z y < dist x y - r + ε) :
    ∃ z : Y, dist x z = r ∧ dist z y = dist x y - r := by
  let f : Y → ℝ := fun z => max (dist x z - r) (dist z y - (dist x y - r))
  have hf : Continuous f :=
    ((continuous_const.dist continuous_id).sub continuous_const).max
      ((continuous_id.dist continuous_const).sub continuous_const)
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set Y).Nonempty from ⟨x, mem_univ x⟩) hf.continuousOn
  have hz0 : f z ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨w, hw₁, hw₂⟩ := happrox ε hε
    have hfw : f w < ε := max_lt (by linarith) (by linarith)
    simpa only [zero_add] using (hz (mem_univ w)).trans hfw.le
  have h₁ := (le_max_left (dist x z - r) (dist z y - (dist x y - r))).trans hz0
  have h₂ := (le_max_right (dist x z - r) (dist z y - (dist x y - r))).trans hz0
  have htri := dist_triangle x z y
  exact ⟨z, by linarith, by linarith⟩

private theorem realization_dist_error
    {A B : FiniteDiameterBasedMetricSpace.{u}} (R : PointedGHRealization A B)
    {a b : A.carrier} {x y : B.carrier} {δ : ℝ}
    (ha : dist (R.left a) (R.right x) < δ)
    (hb : dist (R.left b) (R.right y) < δ) :
    |dist a b - dist x y| < 2 * δ := by
  have h := dist_dist_dist_le (R.left a) (R.left b) (R.right x) (R.right y)
  rw [R.left_isometry.dist_eq, R.right_isometry.dist_eq, Real.dist_eq] at h
  linarith

private theorem exists_near_mem_ball_of_approximate_splits
    {Y : Type*} [MetricSpace Y]
    (hsplit : ∀ x y : Y, ∀ r ε : ℝ, 0 < r → 0 < ε → r < dist x y →
      ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε)
    (p a : Y) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (ha : dist p a < r + δ) :
    ∃ z ∈ Metric.ball p r, dist a z < 3 * δ := by
  by_cases har : dist p a < r
  · exact ⟨a, mem_ball'.mpr har, by rw [dist_self]; positivity⟩
  let s := max (r - δ) (r / 2)
  have hs : 0 < s := (by positivity : 0 < r / 2).trans_le (le_max_right _ _)
  have hsr : s < r := max_lt (by linarith) (by linarith)
  obtain ⟨z, hz, hza⟩ := hsplit p a s δ hs hδ (hsr.trans_le (le_of_not_gt har))
  refine ⟨z, mem_ball'.mpr (hz.trans_lt hsr), ?_⟩
  rw [dist_comm]
  have : r - δ ≤ s := le_max_left _ _
  linarith

private theorem compact_stage_exact_split
    (X : ℕ → BasedMetricSpaceBundle.{u}) [∀ j, CompleteSpace (X j).carrier]
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ j m,
      m ∈ packingAdmissible (X j).base δ R → m ≤ N)
    (hsplit : ∀ j, ∀ x y : (X j).carrier, ∀ r ε : ℝ,
      0 < r → 0 < ε → r < dist x y →
        ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε)
    (phi : ℕ → ℕ) (n : ℕ) (Y : PointedCompactMetricSpace.{u})
    (R : VaryingRealizationSequence
      (fun j => ((uniformPackingBoundedClosedBall X hpack (phi j) n)
        |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
      Y.toFiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle)
    (x y : Y.carrier) (r : ℝ) (hr : 0 < r) (hry : r < dist x y)
    (hroom : dist Y.base x + r + 1 < n) :
    ∃ z : Y.carrier, dist x z = r ∧ dist z y = dist x y - r := by
  apply exact_split_of_compact_approximation x y r
  intro ε hε
  let δ := min (min (ε / 8) ((dist x y - r) / 4)) (1 / 2)
  have hδ : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hδε : δ ≤ ε / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hδr : δ ≤ (dist x y - r) / 4 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hδone : δ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨j, hj⟩ := (R.hausdorff_tendsto_zero.eventually_lt_const hδ).exists
  let A := (uniformPackingBoundedClosedBall X hpack (phi j) n).toFiniteDiameterBasedMetricSpace
  let Q : PointedGHRealization A Y.toFiniteDiameterBasedMetricSpace :=
    { ambient := { carrier := (R.ambient j).carrier
                   metric := (R.ambient j).metric
                   base := R.right j Y.base }
      left := R.left j
      right := R.right j
      left_isometry := R.left_isometry j
      right_isometry := R.right_isometry j
      left_base := R.base_agree j
      right_base := rfl }
  have hQ : pointedHausdorffDist Q < δ := hj
  obtain ⟨a, ha⟩ := exists_left_point_lt_of_pointedHausdorffDist_lt Q hQ x
  obtain ⟨b, hb⟩ := exists_left_point_lt_of_pointedHausdorffDist_lt Q hQ y
  have hab := abs_lt.mp (realization_dist_error Q ha hb)
  have hrab : r < dist a b := by linarith!
  obtain ⟨z, haz, hzb⟩ := hsplit (phi j) a.val b.val r δ hr hδ hrab
  have ha_base := (abs_lt.mp (abs_dist_base_sub_dist_base_lt_of_corresponding Q a x ha)).2
  have hzball : z ∈ Metric.closedBall (X (phi j)).base (n : ℝ) := by
    rw [Metric.mem_closedBall, dist_comm]
    have htri := dist_triangle (X (phi j)).base a.val z
    change dist (X (phi j)).base a.val - dist Y.base x < δ at ha_base
    linarith
  let zA : A.carrier := ⟨z, hzball⟩
  obtain ⟨w, hw⟩ := exists_right_point_lt_of_pointedHausdorffDist_lt Q hQ zA
  have haw := (abs_lt.mp (realization_dist_error Q ha hw)).1
  have hwb := (abs_lt.mp (realization_dist_error Q hw hb)).1
  change - (2 * δ) < dist a.val z - dist x w at haw
  change - (2 * δ) < dist z b.val - dist w y at hwb
  refine ⟨w, ?_, ?_⟩
  · linarith
  · have hab_upper : dist a.val b.val - dist x y < 2 * δ := hab.2
    linarith!

namespace CompatiblePointedCompactSystem

theorem completedLimit_exact_split_of_approximate_splits
    (X : ℕ → BasedMetricSpaceBundle.{u}) [∀ j, CompleteSpace (X j).carrier]
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ j m,
      m ∈ packingAdmissible (X j).base δ R → m ≤ N)
    (hsplit : ∀ j, ∀ x y : (X j).carrier, ∀ r ε : ℝ,
      0 < r → 0 < ε → r < dist x y →
        ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε)
    (phi : ℕ → ℕ) (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆ Set.range (S.stageEmbedding n))
    (hreal : ∀ i, Nonempty (VaryingRealizationSequence
      (fun j => ((uniformPackingBoundedClosedBall X hpack (phi j) i)
        |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
      (S.stage i).toFiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle))
    (x y : S.completedLimit.carrier) (r : ℝ) (hr : 0 ≤ r) (hry : r ≤ dist x y) :
    ∃ z : S.completedLimit.carrier, dist x z = r ∧ dist z y = dist x y - r := by
  rcases hr.eq_or_lt with hr | hr
  · exact ⟨x, by simp [← hr], by simp [← hr]⟩
  rcases hry.eq_or_lt with hry | hry
  · exact ⟨y, hry.symm, by simp [hry]⟩
  obtain ⟨i, hi⟩ := hcover (max (dist x S.completedLimit.base) (dist y S.completedLimit.base))
  have hx : x ∈ Set.range (S.stageEmbedding i) := hi (mem_closedBall.mpr (le_max_left _ _))
  have hy : y ∈ Set.range (S.stageEmbedding i) := hi (mem_closedBall.mpr (le_max_right _ _))
  obtain ⟨N, hN⟩ := exists_nat_gt (dist S.completedLimit.base x + r + 1)
  let n := max i N
  obtain ⟨a, ha⟩ := S.range_stageEmbedding_mono (Nat.le_max_left i N) hx
  obtain ⟨b, hb⟩ := S.range_stageEmbedding_mono (Nat.le_max_left i N) hy
  have hd : dist a b = dist x y := by
    rw [← (S.stageEmbedding_isometry n).dist_eq, ha, hb]
  have hbase : dist (S.stage n).base a = dist S.completedLimit.base x := by
    rw [← (S.stageEmbedding_isometry n).dist_eq, S.stageEmbedding_base, ha]
  obtain ⟨z, hza, hzb⟩ := compact_stage_exact_split X hpack hsplit phi n (S.stage n)
    (Classical.choice (hreal n)) a b r hr (by rwa [hd]) (by
      rw [hbase]
      exact hN.trans_le (by exact_mod_cast Nat.le_max_right i N))
  refine ⟨S.stageEmbedding n z, ?_, ?_⟩
  · rw [← ha, (S.stageEmbedding_isometry n).dist_eq, hza]
  · calc
      dist (S.stageEmbedding n z) y = dist z b := by
        rw [← hb, (S.stageEmbedding_isometry n).dist_eq]
      _ = dist x y - r := by rw [hzb, hd]

theorem pointedGHConvergesUnbounded_of_approximate_splits
    (X : ℕ → BasedMetricSpaceBundle.{u}) [∀ j, CompleteSpace (X j).carrier]
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ j m,
      m ∈ packingAdmissible (X j).base δ R → m ≤ N)
    (hsplit : ∀ j, ∀ x y : (X j).carrier, ∀ r ε : ℝ,
      0 < r → 0 < ε → r < dist x y →
        ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε)
    (phi : ℕ → ℕ) (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆ Set.range (S.stageEmbedding n))
    (hreal : ∀ i, Nonempty (VaryingRealizationSequence
      (fun j => ((uniformPackingBoundedClosedBall X hpack (phi j) i)
        |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
      (S.stage i).toFiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle)) :
    PointedGHConvergesUnbounded (fun j => X (phi j)) S.completedLimit := by
  classical
  have hlimsplit := completedLimit_exact_split_of_approximate_splits
    X hpack hsplit phi S hcover hreal
  have hlimapprox (x y : S.completedLimit.carrier) (r ε : ℝ)
      (hr : 0 < r) (hε : 0 < ε) (hry : r < dist x y) :
      ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε := by
    obtain ⟨z, hz, hzy⟩ := hlimsplit x y r hr.le hry.le
    exact ⟨z, hz, by linarith⟩
  intro r hr
  refine ⟨fun _ => 0, tendsto_const_nhds, fun _ => by simpa using hr, ?_⟩
  simp only [add_zero]
  obtain ⟨i, hi⟩ := hcover r
  obtain ⟨N, hN⟩ := exists_nat_gt r
  let n := max i N
  have hrn : r < (n : ℝ) := hN.trans_le (by exact_mod_cast Nat.le_max_right i N)
  have hcov : Metric.closedBall S.completedLimit.base r ⊆ Set.range (S.stageEmbedding n) :=
    hi.trans (S.range_stageEmbedding_mono (Nat.le_max_left i N))
  let B := ballModel S.completedLimit r hr
  have hex (y : B.carrier) : ∃ a, S.stageEmbedding n a = y.val :=
    hcov (Metric.ball_subset_closedBall y.property)
  choose f hf using hex
  have hfiso : Isometry f := by
    apply Isometry.of_dist_eq
    intro a b
    rw [← (S.stageEmbedding_isometry n).dist_eq, hf, hf]
    rfl
  have hfbase : f B.base = (S.stage n).base := by
    apply (S.stageEmbedding_isometry n).injective
    rw [hf, S.stageEmbedding_base]
    rfl
  let R := Classical.choice (hreal n)
  constructor
  · refine ⟨2 * r, ?_⟩
    intro j a b
    change dist a.val b.val ≤ 2 * r
    have ha := mem_ball.mp a.property
    have hb := mem_ball'.mp b.property
    have ht := dist_triangle a.val (X (phi j)).base b.val
    linarith
  change Tendsto (fun j => pointedGHDistance (ballModel (X (phi j)) r hr) B) atTop (𝓝 0)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j => ha.trans_le (pointedGHDistance_nonneg _ _))
  · intro ε hε
    let δ := ε / 8
    have hδ : 0 < δ := by positivity
    filter_upwards [R.hausdorff_tendsto_zero.eventually_lt_const hδ] with j hj
    let A := (uniformPackingBoundedClosedBall X hpack (phi j) n).toFiniteDiameterBasedMetricSpace
    let Q : PointedGHRealization A (S.stage n).toFiniteDiameterBasedMetricSpace :=
      { ambient := { carrier := (R.ambient j).carrier
                     metric := (R.ambient j).metric
                     base := R.right j (S.stage n).base }
        left := R.left j
        right := R.right j
        left_isometry := R.left_isometry j
        right_isometry := R.right_isometry j
        left_base := R.base_agree j
        right_base := rfl }
    have hQ : pointedHausdorffDist Q < δ := hj
    let A₀ := ballModel (X (phi j)) r hr
    let e : A₀.carrier → A.carrier := fun a =>
      ⟨a.val, mem_closedBall.mpr ((mem_ball.mp a.property).le.trans hrn.le)⟩
    have he : Isometry e := Isometry.of_dist_eq (fun _ _ => rfl)
    let Q₀ : PointedGHRealization A₀ B :=
      { ambient := Q.ambient
        left := Q.left ∘ e
        right := Q.right ∘ f
        left_isometry := Q.left_isometry.comp he
        right_isometry := Q.right_isometry.comp hfiso
        left_base := Q.left_base
        right_base := by
          change Q.right (f B.base) = Q.ambient.base
          exact (congrArg Q.right hfbase).trans Q.right_base }
    have hbound : pointedHausdorffDist Q₀ ≤ 4 * δ := by
      apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
      · rintro _ ⟨a, rfl⟩
        obtain ⟨w, hw⟩ := exists_right_point_lt_of_pointedHausdorffDist_lt Q hQ (e a)
        have hrad := (abs_lt.mp
          (abs_dist_base_sub_dist_base_lt_of_corresponding Q (e a) w hw)).1
        have hwa : dist S.completedLimit.base (S.stageEmbedding n w) < r + δ := by
          rw [← S.stageEmbedding_base n,
            (S.stageEmbedding_isometry n).dist_eq (S.stage n).base w]
          have ha : dist (X (phi j)).base a.val < r := mem_ball'.mp a.property
          change -δ < dist (X (phi j)).base a.val - dist (S.stage n).base w at hrad
          linarith!
        obtain ⟨z, hz, hwz⟩ := exists_near_mem_ball_of_approximate_splits
          hlimapprox S.completedLimit.base (S.stageEmbedding n w) hr hδ hwa
        let zB : B.carrier := ⟨z, hz⟩
        refine ⟨Q₀.right zB, ⟨zB, rfl⟩, ?_⟩
        have hwf : dist (Q.right w) (Q.right (f zB)) < 3 * δ := by
          calc
            dist (Q.right w) (Q.right (f zB)) = dist w (f zB) :=
              Q.right_isometry.dist_eq w (f zB)
            _ = dist (S.stageEmbedding n w) (S.stageEmbedding n (f zB)) :=
              ((S.stageEmbedding_isometry n).dist_eq w (f zB)).symm
            _ < 3 * δ := by rw [hf]; exact hwz
        have ht := dist_triangle (Q.left (e a)) (Q.right w) (Q.right (f zB))
        change dist (Q.left (e a)) (Q.right (f zB)) ≤ 4 * δ
        linarith
      · rintro _ ⟨b, rfl⟩
        obtain ⟨a, ha⟩ := exists_left_point_lt_of_pointedHausdorffDist_lt Q hQ (f b)
        have hrad := (abs_lt.mp
          (abs_dist_base_sub_dist_base_lt_of_corresponding Q a (f b) ha)).2
        have habase : dist (X (phi j)).base a.val < r + δ := by
          have hb : dist S.completedLimit.base b.val < r := mem_ball'.mp b.property
          have hfb : dist (S.stage n).base (f b) = dist S.completedLimit.base b.val := by
            rw [← (S.stageEmbedding_isometry n).dist_eq, S.stageEmbedding_base, hf]
          change dist (X (phi j)).base a.val - dist (S.stage n).base (f b) < δ at hrad
          rw [hfb] at hrad
          linarith
        obtain ⟨z, hz, haz⟩ := exists_near_mem_ball_of_approximate_splits
          (hsplit (phi j)) (X (phi j)).base a.val hr hδ habase
        let zA : A₀.carrier := ⟨z, hz⟩
        refine ⟨Q₀.left zA, ⟨zA, rfl⟩, ?_⟩
        have haz' : dist (Q.left a) (Q.left (e zA)) < 3 * δ := by
          rw [Q.left_isometry.dist_eq]
          exact haz
        have ht := dist_triangle (Q.right (f b)) (Q.left a) (Q.left (e zA))
        rw [dist_comm (Q.right (f b)) (Q.left a)] at ht
        change dist (Q.right (f b)) (Q.left (e zA)) ≤ 4 * δ
        linarith
    exact ((pointedGHDistance_le_realization Q₀).trans hbound).trans_lt (by dsimp [δ]; linarith)

theorem completedLimit_exact_split_of_stage_exact_split
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (hstage : ∀ n, ∀ x y : (S.stage n).carrier, ∀ r : ℝ,
      0 ≤ r → r ≤ dist x y →
        ∃ z : (S.stage n).carrier,
          dist x z = r ∧ dist z y = dist x y - r) :
    ∀ x y : S.completedLimit.carrier, ∀ r : ℝ,
      0 ≤ r → r ≤ dist x y →
        ∃ z : S.completedLimit.carrier,
          dist x z = r ∧ dist z y = dist x y - r := by
  intro x y r hr hrd
  let R : ℝ := max (dist S.completedLimit.base x) (dist S.completedLimit.base y)
  obtain ⟨n, hn⟩ := hcover R
  have hxmem : x ∈ Metric.closedBall S.completedLimit.base
      R := by
    rw [Metric.mem_closedBall]
    simp only [R]
    calc
      dist x S.completedLimit.base = dist S.completedLimit.base x :=
        dist_comm _ _
      _ ≤ max (dist S.completedLimit.base x) (dist S.completedLimit.base y) :=
        le_max_left _ _
  have hymem : y ∈ Metric.closedBall S.completedLimit.base
      R := by
    rw [Metric.mem_closedBall]
    simp only [R]
    calc
      dist y S.completedLimit.base = dist S.completedLimit.base y :=
        dist_comm _ _
      _ ≤ max (dist S.completedLimit.base x) (dist S.completedLimit.base y) :=
        le_max_right _ _
  obtain ⟨xn, hx⟩ := hn hxmem
  obtain ⟨yn, hy⟩ := hn hymem
  obtain ⟨z, hzx, hzy⟩ := hstage n xn yn r hr (by
    rw [← (S.stageEmbedding_isometry n).dist_eq xn yn, hx, hy]
    exact hrd)
  refine ⟨S.stageEmbedding n z, ?_, ?_⟩
  · rw [← hx]
    calc
      dist (S.stageEmbedding n xn) (S.stageEmbedding n z) = dist xn z :=
        (S.stageEmbedding_isometry n).dist_eq _ _
      _ = r := hzx
  · rw [← hy, ← hx]
    calc
      dist (S.stageEmbedding n z) (S.stageEmbedding n yn) = dist z yn :=
        (S.stageEmbedding_isometry n).dist_eq _ _
      _ = dist xn yn - r := hzy
      _ = dist (S.stageEmbedding n xn) (S.stageEmbedding n yn) - r := by
        rw [(S.stageEmbedding_isometry n).dist_eq]

theorem exists_completedLimit_metric_segment_of_exact_splitting
    (S : CompatiblePointedCompactSystem.{u})
    [ProperSpace S.completedLimit.carrier]
    (hsplit : ∀ x y : S.completedLimit.carrier, ∀ r : ℝ,
      0 ≤ r → r ≤ dist x y →
        ∃ z : S.completedLimit.carrier,
          dist x z = r ∧ dist z y = dist x y - r)
    (x y : S.completedLimit.carrier) :
    ∃ γ : ℝ → S.completedLimit.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y := by
  exact Poincare.MetricCurves.exists_metric_segment_of_splitting hsplit x y

theorem completedLimit_is_geodesic_of_exact_splitting
    (S : CompatiblePointedCompactSystem.{u})
    [ProperSpace S.completedLimit.carrier]
    (hsplit : ∀ x y : S.completedLimit.carrier, ∀ r : ℝ,
      0 ≤ r → r ≤ dist x y →
        ∃ z : S.completedLimit.carrier,
          dist x z = r ∧ dist z y = dist x y - r) :
    ∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
      γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y := by
  intro x y
  exact exists_completedLimit_metric_segment_of_exact_splitting S hsplit x y

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff

end
