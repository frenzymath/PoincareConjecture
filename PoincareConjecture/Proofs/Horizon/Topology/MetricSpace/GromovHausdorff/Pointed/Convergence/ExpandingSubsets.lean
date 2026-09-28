import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints
import Mathlib.Topology.MetricSpace.Closeds








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open TopologicalSpace
universe u
namespace Poincare.GromovHausdorff



theorem exists_subseq_nonempty_compact_limit_of_expanding_bounded_subsets
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [ProperSpace Y.carrier]
    (s t : ℕ → ℝ) (hs : ∀ j, 0 < s j) (ht : ∀ j, 0 < t j)
    (hs_top : Tendsto s atTop atTop) (ht_top : Tendsto t atTop atTop)
    (Q : ∀ j, PointedGHRealization (ballModel (X j) (s j) (hs j))
      (ballModel Y (t j) (ht j)))
    (hQ : Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0))
    {ρ : ℝ} (E : ∀ j, Set (X j).carrier) (hne : ∀ j, (E j).Nonempty)
    (hbound : ∀ j x, x ∈ E j → dist (X j).base x ≤ ρ) :
    ∃ φ : ℕ → ℕ, ∃ K : NonemptyCompacts Y.carrier, ∃ ε : ℕ → ℝ,
      StrictMono φ ∧ (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ hρs : ∀ j, ρ < s (φ j), ∃ hρt : ∀ j, ρ < t (φ j),
      ∃ hK : (K : Set Y.carrier) ⊆ Metric.closedBall Y.base ρ,
      (∀ j (x : E (φ j)), ∃ y : K,
        dist ((Q (φ j)).left
          ⟨x.val, Metric.mem_ball'.mpr ((hbound (φ j) x.val x.property).trans_lt (hρs j))⟩)
          ((Q (φ j)).right
          ⟨y.val, Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hK y.property)).trans_lt
            (hρt j))⟩) < ε j) ∧
      (∀ j (y : K), ∃ x : E (φ j),
        dist ((Q (φ j)).left
          ⟨x.val, Metric.mem_ball'.mpr ((hbound (φ j) x.val x.property).trans_lt (hρs j))⟩)
          ((Q (φ j)).right
          ⟨y.val, Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hK y.property)).trans_lt
            (hρt j))⟩) < ε j) := by
  classical
  let e : ℕ → ℝ := fun j => pointedHausdorffDist (Q j) + 1 / ((j : ℝ) + 1)
  have hQe (j : ℕ) : pointedHausdorffDist (Q j) < e j :=
    lt_add_of_pos_right _ (by positivity)
  have hepos (j : ℕ) : 0 < e j :=
    (pointedHausdorffDist_nonneg (Q j)).trans_lt (hQe j)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, add_zero] using
      hQ.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (((hs_top.eventually_gt_atTop (ρ + 2)).and
      (ht_top.eventually_gt_atTop (ρ + 2))).and
      (he.eventually_lt_const (by norm_num : (0 : ℝ) < 1)))
  have hJs (j : ℕ) : ρ + 2 < s (j + J) := (hJ (j + J) (by omega)).1.1
  have hJt (j : ℕ) : ρ + 2 < t (j + J) := (hJ (j + J) (by omega)).1.2
  have hJe (j : ℕ) : e (j + J) < 1 := (hJ (j + J) (by omega)).2
  let src (j : ℕ) (x : E (j + J)) : (ballModel (X (j + J)) (s (j + J)) (hs _)).carrier :=
    ⟨x.val, Metric.mem_ball'.mpr ((hbound _ x.val x.property).trans_lt (by linarith [hJs j]))⟩
  choose near hnear using fun j (x : E (j + J)) =>
    exists_right_point_lt_of_pointedHausdorffDist_lt (Q (j + J)) (hQe _) (src j x)
  have hrad (j : ℕ) (x : E (j + J)) :
      dist Y.base (near j x).val ≤ ρ + e (j + J) := by
    have hh := (abs_lt.mp (abs_dist_base_sub_dist_base_lt_of_corresponding
      (Q (j + J)) (src j x) (near j x) (hnear j x))).1
    change -e (j + J) < dist (X (j + J)).base x.val - dist Y.base (near j x).val at hh
    linarith [hbound (j + J) x.val x.property]
  let C := Metric.closedBall Y.base (ρ + 1)
  let : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let nearC (j : ℕ) (x : E (j + J)) : C :=
    ⟨(near j x).val, by
      rw [Metric.mem_closedBall, dist_comm]
      linarith [hrad j x, hJe j]⟩
  let target (j : ℕ) (y : C) : (ballModel Y (t (j + J)) (ht _)).carrier :=
    ⟨y.val, Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp y.property).trans_lt (by linarith [hJt j]))⟩
  let : ∀ j, Nonempty (E (j + J)) := fun j => (hne (j + J)).to_subtype
  let Kseq (j : ℕ) : NonemptyCompacts C :=
    ⟨⟨closure (Set.range (nearC j)), isClosed_closure.isCompact⟩,
      (Set.range_nonempty (nearC j)).closure⟩
  obtain ⟨K₀, _, ψ, hψ, hψconv⟩ := isCompact_univ.tendsto_subseq
    (x := Kseq) (fun _ => mem_univ _)
  let φ := fun j => ψ j + J
  have hφ : StrictMono φ := fun x y hxy => Nat.add_lt_add_right (hψ hxy) J
  let K : NonemptyCompacts Y.carrier := K₀.map Subtype.val continuous_subtype_val
  let d (j : ℕ) := dist (Kseq (ψ j)) K₀ + 1 / ((j : ℝ) + 1)
  have hdpos (j : ℕ) : 0 < d j := by dsimp [d]; positivity
  have hlt (j : ℕ) : Metric.hausdorffDist (Kseq (ψ j) : Set C) K₀ < d j :=
    lt_add_of_pos_right _ (by positivity)
  have hfinite (j : ℕ) : Metric.hausdorffEDist (Kseq (ψ j) : Set C) K₀ ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (Kseq (ψ j)).nonempty K₀.nonempty (Kseq (ψ j)).isCompact.isBounded K₀.isCompact.isBounded
  have hd : Tendsto d atTop (𝓝 0) := by
    have hh := tendsto_iff_dist_tendsto_zero.mp hψconv
    simpa only [d, Function.comp_def, add_zero] using
      hh.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let ε (j : ℕ) := 2 * e (φ j) + d j
  have hεpos (j : ℕ) : 0 < ε j :=
    add_pos (mul_pos (by norm_num) (hepos _)) (hdpos _)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, mul_zero, add_zero] using
      ((he.comp hφ.tendsto_atTop).const_mul 2).add hd
  have hforward (j : ℕ) (x : E (φ j)) :
      ∃ y ∈ K₀, dist ((Q (φ j)).left (src (ψ j) x))
        ((Q (φ j)).right (target (ψ j) y)) < ε j := by
    have hnmem : nearC (ψ j) x ∈ Kseq (ψ j) :=
      subset_closure (Set.mem_range_self _)
    obtain ⟨y, hy, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hnmem (hlt j) (hfinite j)
    refine ⟨y, hy, ?_⟩
    have hn := hnear (ψ j) x
    have ht' : dist (near (ψ j) x).val y.val < d j := hxy
    have hh := dist_triangle ((Q (φ j)).left (src (ψ j) x))
      ((Q (φ j)).right (near (ψ j) x)) ((Q (φ j)).right (target (ψ j) y))
    rw [(Q (φ j)).right_isometry.dist_eq] at hh
    change dist ((Q (φ j)).left (src (ψ j) x)) ((Q (φ j)).right (target (ψ j) y)) ≤
      _ + dist (near (ψ j) x).val y.val at hh
    dsimp only [ε]
    linarith [hepos (φ j)]
  have hback (j : ℕ) (y : C) (hy : y ∈ K₀) :
      ∃ x : E (φ j), dist ((Q (φ j)).left (src (ψ j) x))
        ((Q (φ j)).right (target (ψ j) y)) < ε j := by
    obtain ⟨z, hz, hzy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hy (hlt j) (hfinite j)
    obtain ⟨z', ⟨x, rfl⟩, hzx⟩ := Metric.mem_closure_iff.mp hz (e (φ j)) (hepos (φ j))
    refine ⟨x, ?_⟩
    have hn := hnear (ψ j) x
    have hz' : dist z.val (near (ψ j) x).val < e (φ j) := hzx
    have hy' : dist z.val y.val < d j := hzy
    have hh := dist_triangle ((Q (φ j)).left (src (ψ j) x))
      ((Q (φ j)).right (near (ψ j) x)) ((Q (φ j)).right (target (ψ j) y))
    rw [(Q (φ j)).right_isometry.dist_eq] at hh
    change dist ((Q (φ j)).left (src (ψ j) x)) ((Q (φ j)).right (target (ψ j) y)) ≤
      _ + dist (near (ψ j) x).val y.val at hh
    have htri := dist_triangle (near (ψ j) x).val z.val y.val
    rw [dist_comm (near (ψ j) x).val z.val] at htri
    dsimp only [ε]
    linarith
  have hK : (K : Set Y.carrier) ⊆ Metric.closedBall Y.base ρ := by
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hle (j : ℕ) : dist Y.base y₀.val ≤ ρ + ε j := by
      obtain ⟨x, hx⟩ := hback j y₀ hy₀
      have hh := (abs_lt.mp (abs_dist_base_sub_dist_base_lt_of_corresponding
        (Q (φ j)) (src (ψ j) x) (target (ψ j) y₀) hx)).1
      change -ε j < dist (X (φ j)).base x.val - dist Y.base y₀.val at hh
      linarith [hbound (φ j) x.val x.property]
    rw [Metric.mem_closedBall, dist_comm]
    exact ge_of_tendsto (by simpa only [add_zero] using tendsto_const_nhds.add hε)
      (Eventually.of_forall hle)
  have hρs (j : ℕ) : ρ < s (φ j) := by linarith [hJs (ψ j)]
  have hρt (j : ℕ) : ρ < t (φ j) := by linarith [hJt (ψ j)]
  refine ⟨φ, K, ε, hφ, hεpos, hε, hρs, hρt, hK, ?_, ?_⟩
  · intro j x
    obtain ⟨y, hy, hxy⟩ := hforward j x
    exact ⟨⟨y.val, ⟨y, hy, rfl⟩⟩, hxy⟩
  · intro j y
    obtain ⟨y₀, hy₀, hval⟩ := y.property
    obtain ⟨x, hx⟩ := hback j y₀ hy₀
    refine ⟨x, ?_⟩
    convert hx using 1
    congr 2
    exact Subtype.ext hval.symm

end Poincare.GromovHausdorff
