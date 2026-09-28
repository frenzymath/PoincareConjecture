import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.MarkedRealization
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.Cover
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.ExpandingRealizations

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
namespace Poincare.GromovHausdorff

private theorem exists_near_mem_ball_of_geodesic
    {W : Type*} [MetricSpace W]
    (hgeo : ∀ x y : W, ∃ γ : ℝ → W, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (p a : W) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (ha : dist p a < r + ε) :
    ∃ z : W, dist p z < r ∧ dist a z < 3 * ε := by
  by_cases har : dist p a < r
  · exact ⟨a, har, by rw [dist_self]; positivity⟩
  have hd : 0 < dist p a := hr.trans_le (le_of_not_gt har)
  let s := max (r - ε) (r / 2)
  have hs : 0 < s := (half_pos hr).trans_le (le_max_right _ _)
  have hsr : s < r := max_lt (by linarith) (by linarith)
  have hsd : s / dist p a ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.le hd.le, (div_le_one hd).mpr (hsr.le.trans (le_of_not_gt har))⟩
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := hgeo p a
  refine ⟨γ (s / dist p a), ?_, ?_⟩
  · have h := hγ 0 (by simp) (s / dist p a) hsd
    rw [hγ0, zero_sub, abs_neg, abs_of_nonneg hsd.1, div_mul_cancel₀ _ hd.ne'] at h
    exact h.trans_lt hsr
  · have h := hγ 1 (by simp) (s / dist p a) hsd
    rw [hγ1, abs_of_nonneg (sub_nonneg.mpr hsd.2), sub_mul, one_mul,
      div_mul_cancel₀ _ hd.ne'] at h
    rw [h]
    have hrs : r - ε ≤ s := le_max_left _ _
    linarith

private theorem pointedGHDistance_le_of_near
    {A B : FiniteDiameterBasedMetricSpace.{0}}
    [TopologicalSpace.SeparableSpace A.carrier]
    [TopologicalSpace.SeparableSpace B.carrier]
    {W : Type} [MetricSpace W]
    (f : A.carrier → W) (g : B.carrier → W)
    (hf : Isometry f) (hg : Isometry g)
    {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hbase : dist (f A.base) (g B.base) ≤ ε)
    (hfg : ∀ x, ∃ y, dist (f x) (g y) ≤ η)
    (hgf : ∀ y, ∃ x, dist (f x) (g y) ≤ η) :
    pointedGHDistance A B ≤ η + ε := by
  let U : Set W := range f ∪ range g
  let : TopologicalSpace.SeparableSpace U :=
    ((TopologicalSpace.isSeparable_range hf.continuous).union
      (TopologicalSpace.isSeparable_range hg.continuous)).separableSpace
  let f' : A.carrier → U := fun x => ⟨f x, Or.inl (mem_range_self x)⟩
  let g' : B.carrier → U := fun y => ⟨g y, Or.inr (mem_range_self y)⟩
  have hf' : Isometry f' := Isometry.of_dist_eq fun x y => hf.dist_eq x y
  have hg' : Isometry g' := Isometry.of_dist_eq fun x y => hg.dist_eq x y
  let R := centeredPointedGHRealization f' g' hf' hg'
  refine (pointedGHDistance_le_realization R).trans ?_
  change Metric.hausdorffDist (range R.left) (range R.right) ≤ η + ε
  apply Metric.hausdorffDist_le_of_mem_dist (add_nonneg hη hε)
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hfg x
    refine ⟨R.right y, mem_range_self y, ?_⟩
    have hb := dist_sub_sub_le_additive
      (kuratowskiEmbedding U (f' x))
      (kuratowskiEmbedding U (f' A.base))
      (kuratowskiEmbedding U (g' y))
      (kuratowskiEmbedding U (g' B.base))
    simp only [(kuratowskiEmbedding.isometry U).dist_eq] at hb
    exact hb.trans (add_le_add hy hbase)
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hgf y
    refine ⟨R.left x, mem_range_self x, ?_⟩
    rw [dist_comm]
    have hb := dist_sub_sub_le_additive
      (kuratowskiEmbedding U (f' x))
      (kuratowskiEmbedding U (f' A.base))
      (kuratowskiEmbedding U (g' y))
      (kuratowskiEmbedding U (g' B.base))
    simp only [(kuratowskiEmbedding.isometry U).dist_eq] at hb
    exact hb.trans (add_le_add hx hbase)

def BasedMetricSpaceBundle.rebase (X : BasedMetricSpaceBundle.{0}) (p : X.carrier) :
    BasedMetricSpaceBundle.{0} := { X with base := p }

theorem pointedGHDistance_rebased_balls_le
    {X Y : BasedMetricSpaceBundle.{0}}
    [ProperSpace X.carrier] [ProperSpace Y.carrier]
    (hXgeo : ∀ x y : X.carrier, ∃ γ : ℝ → X.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (Q : PointedGHRealization (ballModel X s hs) (ballModel Y t ht))
    (a : (ballModel X s hs).carrier) (b : (ballModel Y t ht).carrier)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hQ : pointedHausdorffDist Q < ε)
    (hab : dist (Q.left a) (Q.right b) < ε)
    (ha : dist X.base a.val + r < s)
    (hb : dist Y.base b.val + r < t) :
    pointedGHDistance (ballModel (X.rebase a.val) r hr)
      (ballModel (Y.rebase b.val) r hr) ≤ 8 * ε := by
  let A := ballModel (X.rebase a.val) r hr
  let B := ballModel (Y.rebase b.val) r hr
  let e : A.carrier → (ballModel X s hs).carrier := fun x =>
    ⟨x.val, Metric.mem_ball'.mpr (by
      have hx : dist a.val x.val < r := Metric.mem_ball'.mp x.property
      have htr := dist_triangle X.base a.val x.val
      linarith)⟩
  let f : B.carrier → (ballModel Y t ht).carrier := fun y =>
    ⟨y.val, Metric.mem_ball'.mpr (by
      have hy : dist b.val y.val < r := Metric.mem_ball'.mp y.property
      have htr := dist_triangle Y.base b.val y.val
      linarith)⟩
  let : TopologicalSpace.SeparableSpace A.carrier :=
    (inferInstance : TopologicalSpace.SeparableSpace (Metric.ball a.val r))
  let : TopologicalSpace.SeparableSpace B.carrier :=
    (inferInstance : TopologicalSpace.SeparableSpace (Metric.ball b.val r))
  have he : Isometry e := Isometry.of_dist_eq fun _ _ => rfl
  have hf : Isometry f := Isometry.of_dist_eq fun _ _ => rfl
  have hnear : pointedGHDistance A B ≤ 7 * ε + ε := by
    apply pointedGHDistance_le_of_near (Q.left ∘ e) (Q.right ∘ f)
      (Q.left_isometry.comp he) (Q.right_isometry.comp hf)
      (by positivity) hε.le hab.le
    · intro x
      obtain ⟨w, hw⟩ := exists_right_point_lt_of_pointedHausdorffDist_lt Q hQ (e x)
      have hbw : dist b.val w.val < r + 2 * ε := by
        have h1 := dist_triangle (Q.right b) (Q.left a) (Q.right w)
        have h2 := dist_triangle (Q.left a) (Q.left (e x)) (Q.right w)
        rw [dist_comm (Q.right b) (Q.left a)] at h1
        rw [Q.right_isometry.dist_eq] at h1
        rw [Q.left_isometry.dist_eq] at h2
        have hx : dist a.val x.val < r := Metric.mem_ball'.mp x.property
        change dist b.val w.val ≤ _ at h1
        change dist (Q.left a) (Q.right w) ≤ dist a.val x.val + _ at h2
        linarith
      obtain ⟨z, hz, hwz⟩ := exists_near_mem_ball_of_geodesic
        hYgeo b.val w.val hr (by positivity : 0 < 2 * ε) hbw
      let zB : B.carrier := ⟨z, Metric.mem_ball'.mpr hz⟩
      refine ⟨zB, ?_⟩
      have hwf : dist (Q.right w) (Q.right (f zB)) < 6 * ε := by
        rw [Q.right_isometry.dist_eq]
        change dist w.val z < 6 * ε
        linarith
      have htr := dist_triangle (Q.left (e x)) (Q.right w) (Q.right (f zB))
      change dist (Q.left (e x)) (Q.right (f zB)) ≤ 7 * ε
      linarith
    · intro y
      obtain ⟨w, hw⟩ := exists_left_point_lt_of_pointedHausdorffDist_lt Q hQ (f y)
      have haw : dist a.val w.val < r + 2 * ε := by
        have h1 := dist_triangle (Q.left a) (Q.right b) (Q.left w)
        have h2 := dist_triangle (Q.right b) (Q.right (f y)) (Q.left w)
        rw [Q.left_isometry.dist_eq] at h1
        rw [Q.right_isometry.dist_eq, dist_comm (Q.right (f y)) (Q.left w)] at h2
        have hy : dist b.val y.val < r := Metric.mem_ball'.mp y.property
        change dist a.val w.val ≤ _ at h1
        change dist (Q.right b) (Q.left w) ≤ dist b.val y.val + _ at h2
        linarith
      obtain ⟨z, hz, hwz⟩ := exists_near_mem_ball_of_geodesic
        hXgeo a.val w.val hr (by positivity : 0 < 2 * ε) haw
      let zA : A.carrier := ⟨z, Metric.mem_ball'.mpr hz⟩
      refine ⟨zA, ?_⟩
      have hwe : dist (Q.left (e zA)) (Q.left w) < 6 * ε := by
        rw [Q.left_isometry.dist_eq]
        change dist z w.val < 6 * ε
        rw [dist_comm]
        linarith
      have htr := dist_triangle (Q.left (e zA)) (Q.left w) (Q.right (f y))
      change dist (Q.left (e zA)) (Q.right (f y)) ≤ 7 * ε
      linarith
  linarith

theorem exists_subseq_rebased_pointedGHConvergesUnbounded_with_ball_covers
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    (hXgeo : ∀ j, ∀ x y : (X j).carrier,
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded X Y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : ∀ j, Y.carrier → (X (φ j)).carrier,
        (∀ y z : Y.carrier,
          Tendsto (fun j => dist (f j y) (f j z)) atTop (𝓝 (dist y z))) ∧
        (∀ y : Y.carrier,
          Tendsto (fun j => dist (X (φ j)).base (f j y))
            atTop (𝓝 (dist Y.base y))) ∧
        (∀ y : Y.carrier,
          PointedGHConvergesUnbounded
            (fun j => (X (φ j)).rebase (f j y)) (Y.rebase y)) ∧
        ∀ {ι : Type} [Finite ι] (y : ι → Y.carrier) (r : ι → ℝ)
          {R : ℝ}, 1 < R →
          Metric.closedBall Y.base R ⊆ ⋃ i, Metric.ball (y i) (r i) →
          ∀ q : ∀ j, ι → (X (φ j)).carrier,
            (∀ i, Tendsto (fun j => dist (f j (y i)) (q j i)) atTop (𝓝 0)) →
            ∀ η : ℝ, 0 < η →
              ∀ᶠ j in atTop, Metric.ball (X (φ j)).base 1 ⊆
                ⋃ i, Metric.ball (q j i) (r i + η) := by
  classical
  let R : ℕ → ℝ := fun j => (j : ℝ) + 2
  have hR (j : ℕ) : 0 < R j := by dsimp [R]; positivity
  let ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  obtain ⟨φ, hφ, s, hjs, hs, Q, hQ'⟩ :=
    exists_subseq_expanding_pointed_realizations hconv
  have hQ (j : ℕ) : pointedHausdorffDist (Q j) < ε j := by
    simpa only [ε, one_div] using hQ' j
  have happrox (j : ℕ) (y : (ballModel Y (R j) (hR j)).carrier) :
      ∃ x : (ballModel (X (φ j)) (s j) (hs j)).carrier,
        dist ((Q j).left x) ((Q j).right y) < ε j :=
    exists_left_point_lt_of_pointedHausdorffDist_lt (Q j) (hQ j) y
  choose a ha using happrox
  let f : ∀ j, Y.carrier → (X (φ j)).carrier := fun j y =>
    if hy : dist Y.base y < R j then (a j ⟨y, Metric.mem_ball'.mpr hy⟩).val
    else (X (φ j)).base
  have hRtop : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinside (y : Y.carrier) : ∀ᶠ j in atTop, dist Y.base y < R j :=
    hRtop.eventually (eventually_gt_atTop _)
  have hfrad (y : Y.carrier) :
      Tendsto (fun j => dist (X (φ j)).base (f j y)) atTop
        (𝓝 (dist Y.base y)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hinside y, hε0.eventually_lt_const hη] with j hj hεj
    dsimp [f]
    rw [dif_pos hj, Real.dist_eq]
    exact (abs_dist_base_sub_dist_base_lt_of_corresponding
      (Q j) (a j ⟨y, Metric.mem_ball'.mpr hj⟩) ⟨y, Metric.mem_ball'.mpr hj⟩
      (ha j ⟨y, Metric.mem_ball'.mpr hj⟩)).trans hεj
  refine ⟨φ, hφ, f, ?_, hfrad, ?_, ?_⟩
  · intro y z
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hinside y, hinside z,
      hε0.eventually_lt_const (show 0 < η / 2 by positivity)] with j hy hz hεj
    let yj : (ballModel Y (R j) (hR j)).carrier := ⟨y, Metric.mem_ball'.mpr hy⟩
    let zj : (ballModel Y (R j) (hR j)).carrier := ⟨z, Metric.mem_ball'.mpr hz⟩
    have h := dist_dist_dist_le ((Q j).left (a j yj)) ((Q j).left (a j zj))
      ((Q j).right yj) ((Q j).right zj)
    rw [(Q j).left_isometry.dist_eq, (Q j).right_isometry.dist_eq] at h
    have hay := ha j yj
    have haz := ha j zj
    dsimp [f]
    rw [dif_pos hy, dif_pos hz]
    change dist (dist (a j yj).val (a j zj).val) (dist yj.val zj.val) < η
    change dist (dist (a j yj).val (a j zj).val) (dist yj.val zj.val) ≤ _ at h
    linarith
  · intro y r hr
    refine ⟨fun _ => 0, tendsto_const_nhds, fun _ => by simpa using hr, ?_⟩
    simp only [add_zero]
    constructor
    · refine ⟨2 * r, ?_⟩
      intro j x z
      change dist x.val z.val ≤ 2 * r
      have hx : dist x.val (f j y) < r := Metric.mem_ball.mp x.property
      have hz : dist (f j y) z.val < r := Metric.mem_ball'.mp z.property
      have ht := dist_triangle x.val (f j y) z.val
      linarith
    · apply tendsto_order.mpr
      constructor
      · intro η hη
        exact Eventually.of_forall fun j => hη.trans_le (pointedGHDistance_nonneg _ _)
      · intro η hη
        have hnat : ∀ᶠ j : ℕ in atTop, dist Y.base y + r + 1 < (j : ℝ) :=
          tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
        filter_upwards [hnat,
          (hfrad y).eventually_lt_const (show dist Y.base y < dist Y.base y + 1 by linarith),
          hε0.eventually_lt_const (show 0 < η / 8 by positivity)] with j hj hfj hεj
        have hy : dist Y.base y < R j := by dsimp [R]; linarith
        let yj : (ballModel Y (R j) (hR j)).carrier := ⟨y, Metric.mem_ball'.mpr hy⟩
        have hfval : f j y = (a j yj).val := dif_pos hy
        have hmarginX : dist (X (φ j)).base (a j yj).val + r < s j := by
          rw [hfval] at hfj
          have hsj := hjs j
          linarith
        have hmarginY : dist Y.base yj.val + r < R j := by
          dsimp [yj, R]
          linarith
        have hbound := pointedGHDistance_rebased_balls_le
          (hXgeo (φ j)) hYgeo (hs j) (hR j) (Q j) (a j yj) yj
          hr (hε j) (hQ j) (ha j yj) hmarginX hmarginY
        change pointedGHDistance (ballModel ((X (φ j)).rebase (f j y)) r hr)
          (ballModel (Y.rebase y) r hr) < η
        rw [hfval]
        exact hbound.trans_lt (by linarith)
  · intro ι _ y r R₀ hR₀ hcover q hq η hη
    let ζ : ℝ := min (η / 4) ((R₀ - 1) / 2)
    have hζ : 0 < ζ := lt_min (by positivity) (by linarith)
    have hζR : 1 + ζ ≤ R₀ := by
      have h := min_le_right (η / 4) ((R₀ - 1) / 2)
      dsimp [ζ]
      linarith
    have hζη : 3 * ζ < η := by
      have h := min_le_left (η / 4) ((R₀ - 1) / 2)
      dsimp [ζ]
      linarith
    have hiy : ∀ᶠ j in atTop, ∀ i, dist Y.base (y i) < R j :=
      eventually_all.mpr fun i => hinside (y i)
    have hqclose : ∀ᶠ j in atTop, ∀ i, dist (f j (y i)) (q j i) < ζ :=
      eventually_all.mpr fun i => (hq i).eventually_lt_const hζ
    filter_upwards [hiy, hqclose, hε0.eventually_lt_const hζ] with j hyj hqj hεj
    let yj : ι → (ballModel Y (R j) (hR j)).carrier :=
      fun i => ⟨y i, Metric.mem_ball'.mpr (hyj i)⟩
    have hfval (i : ι) : f j (y i) = (a j (yj i)).val := dif_pos (hyj i)
    have hsone : 1 ≤ s j := by
      have hj := hjs j
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith
    have hc := ball_one_subset_iUnion_of_near_realization
      (hs j) (hR j) (Q j) hsone hζR yj r (fun i => a j (yj i)) (q j)
      (fun i => (ha j (yj i)).trans hεj)
      (fun i => by rw [← hfval i]; exact hqj i)
      ((hQ j).trans hεj) hcover
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hc hx)
    refine mem_iUnion.mpr ⟨i, Metric.mem_ball.mpr ?_⟩
    have hxi := Metric.mem_ball.mp hi
    linarith

theorem exists_subseq_rebased_pointedGHConvergesUnbounded
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    (hXgeo : ∀ j, ∀ x y : (X j).carrier,
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded X Y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : ∀ j, Y.carrier → (X (φ j)).carrier,
        (∀ y z : Y.carrier,
          Tendsto (fun j => dist (f j y) (f j z)) atTop (𝓝 (dist y z))) ∧
        (∀ y : Y.carrier,
          Tendsto (fun j => dist (X (φ j)).base (f j y))
            atTop (𝓝 (dist Y.base y))) ∧
        ∀ y : Y.carrier,
          PointedGHConvergesUnbounded
            (fun j => (X (φ j)).rebase (f j y)) (Y.rebase y) := by
  obtain ⟨φ, hφ, f, hpair, hrad, hrebase, _⟩ :=
    exists_subseq_rebased_pointedGHConvergesUnbounded_with_ball_covers hXgeo hYgeo hconv
  exact ⟨φ, hφ, f, hpair, hrad, hrebase⟩

end Poincare.GromovHausdorff
