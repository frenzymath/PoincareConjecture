import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints
import Mathlib.Topology.MetricSpace.Closeds



open Set Filter Topology
open TopologicalSpace
open Poincare.GromovHausdorff
universe u
set_option backward.isDefEq.respectTransparency false

theorem Poincare.GromovHausdorff.exists_subseq_nonempty_compact_limit_of_bounded_subsets
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (S : VaryingRealizationSequence
      (fun j => (X j).toBasedMetricSpaceBundle) Y.toBasedMetricSpaceBundle)
    {ρ σ : ℝ} (hρσ : ρ < σ) (hcompact : IsCompact (Metric.closedBall Y.base σ))
    (E : ∀ j, Set (X j).carrier) (hne : ∀ j, (E j).Nonempty)
    (hbound : ∀ j x, x ∈ E j → dist (X j).base x ≤ ρ) :
    ∃ φ : ℕ → ℕ, ∃ K : TopologicalSpace.NonemptyCompacts Y.carrier,
      ∃ ε : ℕ → ℝ, StrictMono φ ∧
      (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      (K : Set Y.carrier) ⊆ Metric.closedBall Y.base ρ ∧
      (∀ j x, x ∈ E (φ j) → ∃ y ∈ K,
        dist (S.left (φ j) x) (S.right (φ j) y) < ε j) ∧
      (∀ j y, y ∈ K → ∃ x ∈ E (φ j),
        dist (S.left (φ j) x) (S.right (φ j) y) < ε j) := by
  classical
  let R : ∀ j, PointedGHRealization (X j) Y := fun j =>
    { ambient := { carrier := (S.ambient j).carrier
                   metric := (S.ambient j).metric
                   base := S.left j (X j).base }
      left := S.left j
      right := S.right j
      left_isometry := S.left_isometry j
      right_isometry := S.right_isometry j
      left_base := rfl
      right_base := (S.base_agree j).symm }
  let e : ℕ → ℝ := fun j => pointedHausdorffDist (R j) + 1 / ((j : ℝ) + 1)
  have hR (j : ℕ) : pointedHausdorffDist (R j) < e j :=
    lt_add_of_pos_right _ (by positivity)
  have hepos (j : ℕ) : 0 < e j := (pointedHausdorffDist_nonneg (R j)).trans_lt (hR j)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, R, pointedHausdorffDist, add_zero] using
      S.hausdorff_tendsto_zero.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose near hnear using fun j x =>
    exists_right_point_lt_of_pointedHausdorffDist_lt (R j) (hR j) x
  have hrad (j : ℕ) (x : (X j).carrier) (hx : x ∈ E j) :
      dist Y.base (near j x) ≤ ρ + e j := by
    have hh := abs_dist_base_sub_dist_base_lt_of_corresponding (R j) x (near j x) (hnear j x)
    have hlow := (abs_lt.mp hh).1
    linarith [hbound j x hx]
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (he.eventually_lt_const (sub_pos.mpr hρσ))
  let C := Metric.closedBall Y.base σ
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let nearC (j : ℕ) (x : E (j+J)) : C :=
    ⟨near (j+J) x, by
      rw [Metric.mem_closedBall, dist_comm]
      have hh := hrad (j+J) x x.2
      have hj := hJ (j+J) (by omega)
      linarith⟩
  let : ∀ j, Nonempty (E (j+J)) := fun j => (hne (j+J)).to_subtype
  let Kseq (j : ℕ) : NonemptyCompacts C :=
    ⟨⟨closure (Set.range (nearC j)), isClosed_closure.isCompact⟩,
      (Set.range_nonempty (nearC j)).closure⟩
  obtain ⟨K₀, _, ψ, hψ, hψconv⟩ := isCompact_univ.tendsto_subseq
    (x := Kseq) (fun _ => mem_univ _)
  let φ := fun j => ψ j + J
  have hφ : StrictMono φ := fun x y hxy => Nat.add_lt_add_right (hψ hxy) J
  let K : NonemptyCompacts Y.carrier :=
    K₀.map Subtype.val continuous_subtype_val
  let t (j : ℕ) := dist (Kseq (ψ j)) K₀ + 1/((j : ℝ)+1)
  have htpos (j : ℕ) : 0 < t j := by dsimp [t]; positivity
  have hlt (j : ℕ) : Metric.hausdorffDist (Kseq (ψ j) : Set C) K₀ < t j :=
    lt_add_of_pos_right _ (by positivity)
  have hfinite (j : ℕ) : Metric.hausdorffEDist (Kseq (ψ j) : Set C) K₀ ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (Kseq (ψ j)).nonempty K₀.nonempty (Kseq (ψ j)).isCompact.isBounded K₀.isCompact.isBounded
  have ht : Tendsto t atTop (𝓝 0) := by
    have hh := tendsto_iff_dist_tendsto_zero.mp hψconv
    simpa only [t, Function.comp_def, add_zero] using
      hh.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let ε (j : ℕ) := 2 * e (φ j) + t j
  have hεpos (j : ℕ) : 0 < ε j :=
    add_pos (mul_pos (by norm_num) (hepos _)) (htpos _)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, mul_zero, add_zero] using
      ((he.comp hφ.tendsto_atTop).const_mul 2).add ht
  have hforward (j : ℕ) (x : (X (φ j)).carrier) (hx : x ∈ E (φ j)) :
      ∃ y ∈ K, dist (S.left (φ j) x) (S.right (φ j) y) < ε j := by
    have hnmem : nearC (ψ j) ⟨x,hx⟩ ∈ Kseq (ψ j) :=
      subset_closure (Set.mem_range_self _)
    obtain ⟨y, hy, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hnmem (hlt j) (hfinite j)
    refine ⟨y.val, ⟨y, hy, rfl⟩, ?_⟩
    have hn := hnear (φ j) x
    have ht' : dist (near (φ j) x) y.val < t j := hxy
    have hh := dist_triangle (S.left (φ j) x) (S.right (φ j) (near (φ j) x))
      (S.right (φ j) y.val)
    rw [(S.right_isometry (φ j)).dist_eq] at hh
    change dist (S.left (φ j) x) (S.right (φ j) (near (φ j) x)) < e (φ j) at hn
    dsimp only [ε]
    linarith [hepos (φ j)]
  have hback (j : ℕ) (y : Y.carrier) (hy : y ∈ K) :
      ∃ x ∈ E (φ j), dist (S.left (φ j) x) (S.right (φ j) y) < ε j := by
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨z, hz, hzy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hy₀ (hlt j) (hfinite j)
    obtain ⟨z', ⟨x, rfl⟩, hzx⟩ := Metric.mem_closure_iff.mp hz (e (φ j)) (hepos (φ j))
    refine ⟨x.val, x.2, ?_⟩
    have hn := hnear (φ j) x.val
    have hz' : dist z.val (near (φ j) x.val) < e (φ j) := hzx
    have hy' : dist z.val y₀.val < t j := hzy
    have hh := dist_triangle (S.left (φ j) x.val)
      (S.right (φ j) (near (φ j) x.val)) (S.right (φ j) y₀.val)
    rw [(S.right_isometry (φ j)).dist_eq] at hh
    have htri := dist_triangle (near (φ j) x.val) z.val y₀.val
    rw [dist_comm (near (φ j) x.val) z.val] at htri
    change dist (S.left (φ j) x.val) (S.right (φ j) (near (φ j) x.val)) < e (φ j) at hn
    dsimp only [ε]
    linarith
  refine ⟨φ,K,ε,hφ,hεpos,hε,?_,hforward,hback⟩
  intro y hy
  choose x hx hxy using fun j => hback j y hy
  have hconv : (S.comp φ hφ.tendsto_atTop).PointConverges x y :=
    squeeze_zero (fun _ => dist_nonneg) (fun j => (hxy j).le) hε
  rw [Metric.mem_closedBall, dist_comm]
  exact le_of_tendsto ((S.comp φ hφ.tendsto_atTop).tendsto_dist_base x y hconv)
    (Eventually.of_forall (fun j => hbound (φ j) (x j) (hx j)))

namespace Poincare.GromovHausdorff.VaryingRealizationSequence
theorem exists_pointConverges_in_subsets_of_approximation
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    (E : ∀ j, Set (X j).carrier) (K : Set Y.carrier)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hback : ∀ j y, y ∈ K → ∃ x ∈ E j,
      dist (S.left j x) (S.right j y) < ε j) :
    ∀ y ∈ K, ∃ x : ∀ j, (X j).carrier,
      (∀ j, x j ∈ E j) ∧ S.PointConverges x y := by
  classical
  intro y hy
  choose x hx hxy using fun j => hback j y hy
  exact ⟨x,hx,squeeze_zero (fun _ => dist_nonneg) (fun j => (hxy j).le) hε⟩

theorem mem_of_pointConverges_of_subsets_approximation
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    (E : ∀ j, Set (X j).carrier) {K : Set Y.carrier} (hK : IsClosed K)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hfwd : ∀ j x, x ∈ E j → ∃ y ∈ K,
      dist (S.left j x) (S.right j y) < ε j)
    (x : ∀ j, (X j).carrier) (hx : ∀ j, x j ∈ E j)
    (y : Y.carrier) (hxy : S.PointConverges x y) :
    y ∈ K := by
  classical
  choose q hq hxq using fun j => hfwd j (x j) (hx j)
  have hqconv : Tendsto q atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (show Tendsto (fun j => ε j + dist (S.left j (x j)) (S.right j y))
        atTop (𝓝 0) by simpa only [add_zero] using hε.add hxy)
    calc
      dist (q j) y = dist (S.right j (q j)) (S.right j y) :=
        ((S.right_isometry j).dist_eq _ _).symm
      _ ≤ dist (S.right j (q j)) (S.left j (x j)) +
        dist (S.left j (x j)) (S.right j y) := dist_triangle _ _ _
      _ ≤ ε j + dist (S.left j (x j)) (S.right j y) := by
        rw [dist_comm (S.right j (q j)) (S.left j (x j))]
        exact add_le_add (hxq j).le le_rfl
  exact hK.mem_of_tendsto hqconv (Eventually.of_forall hq)



theorem eventually_subsets_subset_iUnion_of_pointConverges
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    (E : ∀ j, Set (X j).carrier) (K : Set Y.carrier)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hfwd : ∀ j x, x ∈ E j → ∃ y ∈ K,
      dist (S.left j x) (S.right j y) < ε j)
    {ι : Type*} [Finite ι] (y : ι → Y.carrier) (r : ι → ℝ)
    (q : ∀ j, ι → (X j).carrier)
    (hq : ∀ i, S.PointConverges (fun j => q j i) (y i))
    (hcover : K ⊆ ⋃ i, Metric.ball (y i) (r i))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, E j ⊆ ⋃ i, Metric.ball (q j i) (r i + η) := by
  have hqnear : ∀ᶠ j in atTop, ∀ i,
      dist (S.left j (q j i)) (S.right j (y i)) < η / 2 :=
    Filter.eventually_all.mpr (fun i => (hq i).eventually_lt_const (half_pos hη))
  filter_upwards [hε.eventually_lt_const (half_pos hη), hqnear] with j hj hqj
  intro x hx
  obtain ⟨z, hz, hxz⟩ := hfwd j x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz)
  refine mem_iUnion.mpr ⟨i, Metric.mem_ball.mpr ?_⟩
  have hzi : dist z (y i) < r i := hi
  have htri := dist_triangle4 (S.left j x) (S.right j z)
    (S.right j (y i)) (S.left j (q j i))
  rw [(S.left_isometry j).dist_eq, (S.right_isometry j).dist_eq,
    dist_comm (S.right j (y i)) (S.left j (q j i))] at htri
  linarith [hqj i]

end Poincare.GromovHausdorff.VaryingRealizationSequence
