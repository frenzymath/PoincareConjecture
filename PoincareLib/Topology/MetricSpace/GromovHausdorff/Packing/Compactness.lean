/-
Adapted from AxelWorkspace, revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source: MorganTianLib/Foundations/Precompactness.lean.
Apache-2.0; see references/analysis/axel-workspace/LICENSE.Apache-2.0.txt.
-/

import PoincareLib.Topology.MetricSpace.GromovHausdorff.Packing.Bounds
import PoincareLib.Topology.MetricSpace.GromovHausdorff.Pointed.Distance
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# compact GH precompactness adapter

This module isolates the compact-carrier part of the packing argument.  The
source theorem is pointed and unbounded; the present producer only assembles a
subsequence in Mathlib's (unpointed) complete GH space.  The basepoint and the
ballwise diagonal assembly remain separate contracts in `PointedGH.lean`.
-/

open Set Filter Topology
open scoped Topology

namespace Poincare.GromovHausdorff

universe u

private theorem exists_isometryEquiv_to_ghRep
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    Nonempty (X ≃ᵢ (_root_.GromovHausdorff.toGHSpace X).Rep) := by
  apply (_root_.GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv).mp
  exact (_root_.GromovHausdorff.GHSpace.toGHSpace_rep
    (_root_.GromovHausdorff.toGHSpace X)).symm

private noncomputable def ghRepEquiv
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    X ≃ᵢ (_root_.GromovHausdorff.toGHSpace X).Rep :=
  (exists_isometryEquiv_to_ghRep X).some

private theorem ghRep_diam_eq
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    Metric.diam (Set.univ : Set (_root_.GromovHausdorff.toGHSpace X).Rep) =
      Metric.diam (Set.univ : Set X) := by
  obtain ⟨e⟩ := exists_isometryEquiv_to_ghRep X
  exact e.diam_univ.symm

private theorem ghRep_cover_of_cover
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    {s : Set X} {r : ℝ}
    (hcover : (Set.univ : Set X) ⊆ ⋃ x ∈ s, Metric.ball x r) :
    (Set.univ : Set (_root_.GromovHausdorff.toGHSpace X).Rep) ⊆
      ⋃ x ∈ (ghRepEquiv X) '' s,
        Metric.ball x r := by
  let e := ghRepEquiv X
  intro y hy
  obtain ⟨x, hx⟩ := e.surjective y
  obtain ⟨z, hz, hdist⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ x))
  refine Set.mem_iUnion₂.mpr ⟨e z, ⟨z, hz, rfl⟩, ?_⟩
  rw [Metric.mem_ball] at hdist ⊢
  rw [← hx, e.isometry.dist_eq]
  exact hdist

private theorem ghRep_cover_card_le
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (s : Set X) (N : ℕ) (hs : s.Finite) (hN : s.ncard ≤ N) :
    Cardinal.mk (ghRepEquiv X '' s) ≤ N := by
  have hsi : (ghRepEquiv X '' s).Finite := hs.image _
  rw [← Set.cast_ncard hsi, Set.ncard_image_of_injective s
    (ghRepEquiv X).injective]
  exact_mod_cast hN

/-! ## Compact ambient basepoint extraction -/

/-- **Math.** Basepoints from varying pointed compact carriers converge along a
strictly monotone subsequence whenever chosen ambient images lie in one compact
set.  This is the finite-radius/basepoint extraction step; it does not assert
compatibility of the ambient maps away from the distinguished points. -/
theorem exists_subseq_tendsto_mapped_basepoints_of_compact_ambient
    (X : ℕ → PointedCompactMetricSpace)
    {Y : Type*} [MetricSpace Y] {K : Set Y} (hK : IsCompact K)
    (f : ∀ n, (X n).carrier → Y)
    (hbase : ∀ n, f n (X n).base ∈ K) :
    ∃ y : Y, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => f (φ n) (X (φ n)).base) atTop (𝓝 y) := by
  let b : ℕ → Y := fun n => f n (X n).base
  obtain ⟨y, hy, φ, hφ, hconv⟩ := hK.tendsto_subseq (fun n => hbase n)
  exact ⟨y, φ, hφ, by simpa [b, Function.comp_def] using hconv⟩

/-- **Math.** A convergent compact-carrier GH sequence retains its limit after
passing to a subsequence on which chosen ambient images of the basepoints
converge.  This is the product-extraction adapter needed before imposing any
pointed compatibility condition on the limiting realization. -/
theorem exists_subseq_tendsto_unpointedGHSpace_and_mapped_basepoints
    (X : ℕ → PointedCompactMetricSpace)
    {Y : Type*} [MetricSpace Y] {K : Set Y} (hK : IsCompact K)
    (f : ∀ n, (X n).carrier → Y)
    (hbase : ∀ n, f n (X n).base ∈ K)
    {p : _root_.GromovHausdorff.GHSpace}
    (hconv : Tendsto (fun n => _root_.GromovHausdorff.toGHSpace (X n).carrier)
      atTop (𝓝 p)) :
    ∃ y : Y, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => f (φ n) (X (φ n)).base) atTop (𝓝 y) ∧
      Tendsto (fun n => _root_.GromovHausdorff.toGHSpace (X (φ n)).carrier)
        atTop (𝓝 p) := by
  obtain ⟨y, φ, hφ, hbaseconv⟩ :=
    exists_subseq_tendsto_mapped_basepoints_of_compact_ambient
      X hK f hbase
  refine ⟨y, φ, hφ, hbaseconv, ?_⟩
  exact hconv.comp hφ.tendsto_atTop

/-! The compact-carrier GH subsequence interface. -/

/-- **Math.** Uniform diameter and finite-cover bounds make the closure of a
sequence of compact carriers compact in Mathlib's Gromov--Hausdorff space.  This
compact-closure form is the input needed for simultaneous diagonal extraction
over countably many radii. -/
theorem isCompact_closure_range_toGHSpace_of_uniform_covers
    (X : ℕ → Type u) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)]
    [∀ n, Nonempty (X n)]
    {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiam : ∀ n, Metric.diam (Set.univ : Set (X n)) ≤ C)
    (hcover : ∀ n m, ∃ s : Set (X n), Cardinal.mk s ≤ K m ∧
      (Set.univ : Set (X n)) ⊆ ⋃ x ∈ s, Metric.ball x (u m)) :
    IsCompact (closure (Set.range (fun n => _root_.GromovHausdorff.toGHSpace (X n)))) := by
  let t : Set _root_.GromovHausdorff.GHSpace :=
    Set.range (fun n => _root_.GromovHausdorff.toGHSpace (X n))
  have ht : TotallyBounded t := by
    apply _root_.GromovHausdorff.totallyBounded (t := t) hu
    · intro p hp
      rcases hp with ⟨n, rfl⟩
      simpa [ghRep_diam_eq] using hdiam n
    · intro p hp m
      rcases hp with ⟨n, rfl⟩
      obtain ⟨s, hs_card, hs_cover⟩ := hcover n m
      have hs_fin : s.Finite := by
        apply Cardinal.mk_lt_aleph0_iff.mp
        exact hs_card.trans_lt Cardinal.natCast_lt_aleph0
      have hs_ncard : s.ncard ≤ K m := by
        have hc : (s.ncard : Cardinal) ≤ (K m : Cardinal) := by
          rw [Set.cast_ncard hs_fin]
          exact hs_card
        exact_mod_cast hc
      refine ⟨ghRepEquiv (X n) '' s, ?_, ?_⟩
      · exact ghRep_cover_card_le (X n) s (K m) hs_fin hs_ncard
      · exact ghRep_cover_of_cover (X n) hs_cover
  exact ht.closure.isCompact_of_isClosed isClosed_closure

/-- **Math.** Uniform diameter and finite-cover bounds for a sequence of
nonempty compact metric carriers make its image in Mathlib's GH space
totally bounded, hence yield a convergent subsequence.  This is the compact,
unpointed assembly step behind the packing argument; it does not
assert basepoint preservation or the unbounded pointed limit. -/
theorem exists_subseq_tendsto_unpointedGHSpace_of_uniform_covers
    (X : ℕ → Type u) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)]
    [∀ n, Nonempty (X n)]
    {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiam : ∀ n, Metric.diam (Set.univ : Set (X n)) ≤ C)
    (hcover : ∀ n m, ∃ s : Set (X n), Cardinal.mk s ≤ K m ∧
      (Set.univ : Set (X n)) ⊆ ⋃ x ∈ s, Metric.ball x (u m)) :
    ∃ p : _root_.GromovHausdorff.GHSpace, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => _root_.GromovHausdorff.toGHSpace (X (φ n))) atTop (𝓝 p) := by
  let t : Set _root_.GromovHausdorff.GHSpace :=
    Set.range (fun n => _root_.GromovHausdorff.toGHSpace (X n))
  have hcompact : IsCompact (closure t) :=
    isCompact_closure_range_toGHSpace_of_uniform_covers X hu hdiam hcover
  obtain ⟨p, hp, φ, hφ, hconv⟩ :=
    hcompact.tendsto_subseq
      (x := fun n => _root_.GromovHausdorff.toGHSpace (X n))
      (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨p, φ, hφ, by simpa [Function.comp_def] using hconv⟩

/-- **Math.** The preceding compact GH-space subsequence can be represented by
a pointed compact carrier, but this corollary deliberately retains the
unpointed convergence predicate.  No claim about convergence of the chosen
basepoints is made. -/
theorem exists_subseq_unpointedGHConverges_of_uniform_covers
    (X : ℕ → PointedCompactMetricSpace)
    {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiam : ∀ n, Metric.diam (Set.univ : Set (X n).carrier) ≤ C)
    (hcover : ∀ n m, ∃ s : Set (X n).carrier, Cardinal.mk s ≤ K m ∧
      (Set.univ : Set (X n).carrier) ⊆
        ⋃ x ∈ s, Metric.ball x (u m)) :
    ∃ Y : PointedCompactMetricSpace.{0}, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ UnpointedGHConverges (fun n => X (φ n)) Y := by
  obtain ⟨p, φ, hφ, hconv⟩ :=
    exists_subseq_tendsto_unpointedGHSpace_of_uniform_covers
      (fun n => (X n).carrier) hu hdiam hcover
  let Y : PointedCompactMetricSpace :=
    { carrier := p.Rep
      metric := inferInstance
      compact := inferInstance
      nonempty := inferInstance
      base := Classical.choice (inferInstance : Nonempty p.Rep) }
  refine ⟨Y, φ, hφ, ?_⟩
  unfold UnpointedGHConverges
  simpa [PointedCompactMetricSpace.unpointedGH, _root_.GromovHausdorff.ghDist,
    Y, Function.comp_def, _root_.GromovHausdorff.GHSpace.toGHSpace_rep] using
    (tendsto_iff_dist_tendsto_zero.mp hconv)

/-- **Math.** Uniform basepoint-centered packing bounds for a sequence of
compact carriers produce one finite-cover cardinal function for every scale.
The exact net separation exposed by `exists_isDeltaNet_separated` is what makes
the bound uniform across the varying carriers. -/
theorem exists_uniform_covers_of_uniform_basepoint_packing_bounds
    (X : ℕ → PointedCompactMetricSpace.{u})
    {C : ℝ} {v : ℕ → ℝ}
    (hv_pos : ∀ m, 0 < v m)
    (hdiam : ∀ k, Metric.diam (Set.univ : Set (X k).carrier) ≤ C)
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ k q,
      q ∈ packingAdmissible (X k).base δ R → q ≤ N) :
    ∃ K : ℕ → ℕ, ∀ k m, ∃ s : Set (X k).carrier,
      Cardinal.mk s ≤ K m ∧
      (Set.univ : Set (X k).carrier) ⊆
        ⋃ y ∈ s, Metric.ball y (v m) := by
  have hC : 0 ≤ C := by
    have hdist : dist (X 0).base (X 0).base ≤
        Metric.diam (Set.univ : Set (X 0).carrier) :=
      Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace
        (Set.mem_univ _) (Set.mem_univ _)
    exact le_trans (by simp) (hdist.trans (hdiam 0))
  choose K hK using fun m =>
    hpack (v m / 2) ((C + 1) + 1 + v m / 2) (by linarith [hv_pos m])
  refine ⟨K, ?_⟩
  intro k m
  have hR : 0 < C + 1 := by linarith
  obtain ⟨L, hLfin, hLncard, hLcover⟩ :=
    exists_finite_ball_cover_of_uniform_packing_bound_with_card
      (X k).base hR (hv_pos m) (hK m k)
  refine ⟨L, ?_, ?_⟩
  · rw [← Set.cast_ncard hLfin]
    exact_mod_cast hLncard
  · intro y hy
    have hyball : y ∈ Metric.ball (X k).base (C + 1) := by
      rw [Metric.mem_ball]
      have hdist : dist y (X k).base ≤
          Metric.diam (Set.univ : Set (X k).carrier) :=
        Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace
          (Set.mem_univ y) (Set.mem_univ _)
      exact lt_of_le_of_lt (hdist.trans (hdiam k)) (by linarith)
    obtain ⟨z, hz, hdist⟩ := hLcover y hyball
    exact Set.mem_iUnion₂.mpr ⟨z, hz, hdist⟩

/-- **Math.** Uniform basepoint packing bounds and diameter control yield a
convergent subsequence in Mathlib's complete, unpointed GH space.  The theorem
still deliberately stops before the source's basepoint-preserving unbounded
assembly. -/
theorem exists_subseq_tendsto_unpointedGHSpace_of_uniform_basepoint_packing_bounds
    (X : ℕ → PointedCompactMetricSpace.{u})
    {C : ℝ} {v : ℕ → ℝ}
    (hv : Tendsto v atTop (𝓝 0))
    (hv_pos : ∀ m, 0 < v m)
    (hdiam : ∀ k, Metric.diam (Set.univ : Set (X k).carrier) ≤ C)
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ k q,
      q ∈ packingAdmissible (X k).base δ R → q ≤ N) :
    ∃ p : _root_.GromovHausdorff.GHSpace, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => _root_.GromovHausdorff.toGHSpace (X (φ n)).carrier) atTop
        (𝓝 p) := by
  obtain ⟨K, hcover⟩ :=
    exists_uniform_covers_of_uniform_basepoint_packing_bounds
      X hv_pos hdiam hpack
  apply exists_subseq_tendsto_unpointedGHSpace_of_uniform_covers
    (fun n => (X n).carrier) hv hdiam
  intro n m
  exact hcover n m

/-- **Math.** The preceding packing-to-GH extraction has an unpointed compact
carrier wrapper.  The chosen basepoints are retained in the bundle but are not
asserted to converge or to identify a pointed limit. -/
theorem exists_subseq_unpointedGHConverges_of_uniform_basepoint_packing_bounds
    (X : ℕ → PointedCompactMetricSpace.{u})
    {C : ℝ} {v : ℕ → ℝ}
    (hv : Tendsto v atTop (𝓝 0))
    (hv_pos : ∀ m, 0 < v m)
    (hdiam : ∀ k, Metric.diam (Set.univ : Set (X k).carrier) ≤ C)
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ k q,
      q ∈ packingAdmissible (X k).base δ R → q ≤ N) :
    ∃ Y : PointedCompactMetricSpace.{0}, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ UnpointedGHConverges (fun n => X (φ n)) Y := by
  obtain ⟨K, hcover⟩ :=
    exists_uniform_covers_of_uniform_basepoint_packing_bounds
      X hv_pos hdiam hpack
  apply exists_subseq_unpointedGHConverges_of_uniform_covers X hv hdiam
  intro n m
  exact hcover n m

/-! ## Compact closed-ball models -/

/-- **Math.** A complete based metric space with uniform all-scale packing
bounds has a compact pointed closed ball at every nonnegative radius.  This is
the finite-radius compact carrier used in the unbounded diagonal argument. -/
noncomputable def packingBoundedClosedBall
    (X : BasedMetricSpaceBundle.{u}) [CompleteSpace X.carrier]
    (R : ℝ) (hR : 0 ≤ R)
    (hpack : ∀ (δ S : ℝ), 0 < δ → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible X.base δ S → n ≤ N) :
    PointedCompactMetricSpace := by
  have hcompact : IsCompact (Metric.closedBall X.base R) :=
    (totallyBounded_closedBall_of_uniform_packing_bound X.base hR hpack)
      |>.isCompact_of_isClosed Metric.isClosed_closedBall
  exact
    { carrier := Metric.closedBall X.base R
      metric := inferInstance
      compact := isCompact_iff_compactSpace.mp hcompact
      nonempty := ⟨⟨X.base, Metric.mem_closedBall_self hR⟩⟩
      base := ⟨X.base, Metric.mem_closedBall_self hR⟩ }

/-- **Math.** The compact closed-ball model has the elementary diameter bound
needed by Mathlib's compact Gromov--Hausdorff criterion. -/
theorem packingBoundedClosedBall_diam_le
    (X : BasedMetricSpaceBundle.{u}) [CompleteSpace X.carrier]
    (R : ℝ) (hR : 0 ≤ R)
    (hpack : ∀ (δ S : ℝ), 0 < δ → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible X.base δ S → n ≤ N) :
    Metric.diam
      (Set.univ : Set (packingBoundedClosedBall X R hR hpack).carrier) ≤
        2 * R := by
  change Metric.diam (Set.univ : Set (Metric.closedBall X.base R)) ≤ 2 * R
  apply Metric.diam_le_of_forall_dist_le_of_nonempty
    ⟨⟨X.base, Metric.mem_closedBall_self hR⟩, Set.mem_univ _⟩
  intro a ha b hb
  rw [Subtype.dist_eq]
  calc
    dist (a : X.carrier) (b : X.carrier) ≤
        dist (a : X.carrier) X.base + dist X.base (b : X.carrier) :=
      dist_triangle _ _ _
    _ ≤ R + R := by
      apply add_le_add
      · exact Metric.mem_closedBall.mp a.property
      · simpa [dist_comm] using Metric.mem_closedBall.mp b.property
    _ = 2 * R := by ring

/-- **Math.** A uniform packing bound for a varying family specializes to each
individual member without changing its scale or radius. -/
theorem packingBound_at_of_uniform_packing_bounds
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (hpack : ∀ δ S, 0 < δ → ∃ N : ℕ, ∀ k n,
      n ∈ packingAdmissible (X k).base δ S → n ≤ N)
    (k : ℕ) :
    ∀ δ S, 0 < δ → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible (X k).base δ S → n ≤ N := by
  intro δ S hδ
  obtain ⟨N, hN⟩ := hpack δ S hδ
  exact ⟨N, hN k⟩

/-- **Math.** The integer-radius compact closed ball of one member of a family
with uniform packing bounds. -/
noncomputable def uniformPackingBoundedClosedBall
    (X : ℕ → BasedMetricSpaceBundle.{u})
    [∀ k, CompleteSpace (X k).carrier]
    (hpack : ∀ δ S, 0 < δ → ∃ N : ℕ, ∀ k n,
      n ∈ packingAdmissible (X k).base δ S → n ≤ N)
    (k i : ℕ) : PointedCompactMetricSpace :=
  packingBoundedClosedBall (X k) (i : ℝ) (Nat.cast_nonneg i)
    (packingBound_at_of_uniform_packing_bounds X hpack k)

/-! ## Packing bounds inherited from compact pointed limits -/

private theorem packing_bound_of_realization_and_target_cover
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    {δ R₀ : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hHaus : pointedHausdorffDist R < min (δ / 8) 1)
    (L : Set Y.carrier) (hLfin : L.Finite) (hLncard : L.ncard ≤ N)
    (hLcover : ∀ y ∈ Metric.ball Y.base (R₀ + 1),
      ∃ z ∈ L, dist y z < δ / 4) :
    ∀ n, n ∈ packingAdmissible X.base δ R₀ → n ≤ N := by
  intro n hn
  rcases hn with ⟨w⟩
  choose y hy using fun i =>
    exists_right_point_lt_of_pointedHausdorffDist_lt R hHaus (w.center i)
  have hyball : ∀ i, y i ∈ Metric.ball Y.base (R₀ + 1) := by
    intro i
    rw [Metric.mem_ball]
    have hcenter := Metric.mem_ball.mp (w.center_mem i)
    have hcenter' : dist X.base (w.center i) < R₀ := by
      simpa [dist_comm] using hcenter
    have hrad := abs_dist_base_sub_dist_base_lt_of_corresponding
      R (w.center i) (y i) (hy i)
    have hupper_comm : -min (δ / 8) 1 <
        dist X.base (w.center i) - dist (y i) Y.base := by
      simpa [dist_comm] using (abs_lt.mp hrad).1
    have hupper' : dist (y i) Y.base <
        dist X.base (w.center i) + min (δ / 8) 1 := by
      linarith
    have hmin1 : min (δ / 8) 1 ≤ 1 := min_le_right _ _
    linarith
  choose z hzL hzy using fun i => hLcover (y i) (hyball i)
  let zfun : Fin n → L := fun i => ⟨z i, hzL i⟩
  have hzsep : Function.Injective zfun := by
    intro i j hij
    by_contra hne
    have hsep := w.center_separated hδ hne
    have hzij : z i = z j := congrArg Subtype.val hij
    have htri :
        dist (R.left (w.center i)) (R.left (w.center j)) ≤
          dist (R.left (w.center i)) (R.right (y i)) +
          dist (R.right (y i)) (R.right (z i)) +
          dist (R.right (z j)) (R.right (y j)) +
          dist (R.right (y j)) (R.left (w.center j)) := by
      calc
        dist (R.left (w.center i)) (R.left (w.center j)) ≤
            dist (R.left (w.center i)) (R.right (y i)) +
              dist (R.right (y i)) (R.right (z i)) +
              dist (R.right (z i)) (R.left (w.center j)) :=
          dist_triangle4 _ _ _ _
        _ ≤
            dist (R.left (w.center i)) (R.right (y i)) +
              dist (R.right (y i)) (R.right (z i)) +
              (dist (R.right (z i)) (R.right (y j)) +
                dist (R.right (y j)) (R.left (w.center j))) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by rw [hzij]; ring
    have hleft : dist (R.left (w.center i)) (R.left (w.center j)) =
        dist (w.center i) (w.center j) := R.left_isometry.dist_eq _ _
    have hyi : dist (R.left (w.center i)) (R.right (y i)) < δ / 8 :=
      lt_of_lt_of_le (hy i) (min_le_left _ _)
    have hyj : dist (R.right (y j)) (R.left (w.center j)) < δ / 8 := by
      exact lt_of_lt_of_le (by simpa [dist_comm] using hy j)
        (min_le_left _ _)
    have hzi : dist (R.right (y i)) (R.right (z i)) < δ / 4 := by
      simpa [R.right_isometry.dist_eq] using hzy i
    have hzj : dist (R.right (z j)) (R.right (y j)) < δ / 4 := by
      rw [R.right_isometry.dist_eq]
      simpa [dist_comm] using hzy j
    rw [hleft] at htri
    have hlt : dist (w.center i) (w.center j) < δ := by
      linarith
    exact (not_lt_of_ge hsep) hlt
  have hz_inj : Function.Injective z := by
    intro i j hij
    apply hzsep
    exact Subtype.ext hij
  have hrange : (Set.range z).ncard = n := by
    simpa using Set.ncard_range_of_injective hz_inj
  have hsub : Set.range z ⊆ L := by
    rintro z' ⟨i, rfl⟩
    exact hzL i
  have hcard : n ≤ L.ncard := by
    rw [← hrange]
    exact Set.ncard_le_ncard hsub hLfin
  exact hcard.trans hLncard

/-- **Math.** A pointed realization sufficiently close to a compact target
forces a finite packing bound on the source ball.  The target cover controls
the bound; no compactness or properness assumption is imposed on the source. -/
theorem exists_packing_bound_of_pointedGHRealization_compact_target
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace Y.carrier]
    (R : PointedGHRealization X Y)
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀ : 0 ≤ R₀)
    (hHaus : pointedHausdorffDist R < min (δ / 8) 1) :
    ∃ N : ℕ, ∀ n, n ∈ packingAdmissible X.base δ R₀ → n ≤ N := by
  let η : ℝ := δ / 4
  have hη : 0 < η := by
    dsimp [η]
    linarith
  obtain ⟨N, hN⟩ :=
    exists_packing_bound_of_totallyBounded_closedBall
      Y.base (by linarith : 0 < η / 2)
      (ProperSpace.isCompact_closedBall Y.base
        ((R₀ + 1) + 1 + η / 2)).totallyBounded
  obtain ⟨L, hLfin, hLncard, hLcover⟩ :=
    exists_finite_ball_cover_of_uniform_packing_bound_with_card
      Y.base (R := R₀ + 1) (η := η) (by linarith) hη hN
  refine ⟨N, packing_bound_of_realization_and_target_cover
    R hδ hHaus L hLfin hLncard ?_⟩
  simpa [η] using hLcover

/-! The preceding producer transfers a finite cover of the target to a packing
bound on the source.  Swapping the two realization legs gives the converse
packing transfer.  We first expose the exact buffered scale used by the proof,
then provide the all-scale convenience form below. -/

/-- **Math.** A small pointed realization transfers a packing bound on one
buffered scale of its left-hand space to a fixed-scale packing bound on its
right-hand space.  The source bound is taken at `δ / 8` and radius
`R₀ + 2 + δ / 8`; these are precisely the margins needed to build a finite
`δ / 4`-cover before swapping the realization legs. -/
theorem exists_packing_bound_of_pointedGHRealization_source_packing_at
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀ : 0 ≤ R₀)
    (hpack : ∃ N : ℕ, ∀ n,
      n ∈ packingAdmissible X.base (δ / 8) (R₀ + 2 + δ / 8) → n ≤ N)
    (hHaus : pointedHausdorffDist R < min (δ / 8) 1) :
    ∃ N : ℕ, ∀ n, n ∈ packingAdmissible Y.base δ R₀ → n ≤ N := by
  obtain ⟨N, hN⟩ := hpack
  let η : ℝ := δ / 4
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hscale : η / 2 = δ / 8 := by
    dsimp [η]
    ring
  have hN' : ∀ n,
      n ∈ packingAdmissible X.base (η / 2)
        ((R₀ + 1) + 1 + η / 2) → n ≤ N := by
    intro n hn
    apply hN n
    rw [hscale] at hn
    have hrad : (R₀ + 1) + 1 + δ / 8 = R₀ + 2 + δ / 8 := by ring
    rw [hrad] at hn
    exact hn
  obtain ⟨L, hLfin, hLncard, hLcover⟩ :=
    exists_finite_ball_cover_of_uniform_packing_bound_with_card
      X.base (R := R₀ + 1) (η := η) (by linarith) hη hN'
  let R' : PointedGHRealization Y X :=
    { ambient := R.ambient
      left := R.right
      right := R.left
      left_isometry := R.right_isometry
      right_isometry := R.left_isometry
      left_base := R.right_base
      right_base := R.left_base }
  have hHaus' : pointedHausdorffDist R' < min (δ / 8) 1 := by
    simpa [R', pointedHausdorffDist, Metric.hausdorffDist_comm] using hHaus
  refine ⟨N, packing_bound_of_realization_and_target_cover
    R' hδ hHaus' L hLfin hLncard ?_⟩
  simpa [η] using hLcover

/-- **Math.** A small pointed realization transfers an all-scale packing bound
on its left-hand space to a fixed-scale packing bound on its right-hand space.
The proof constructs a finite buffered cover on the left at scale `δ / 4`,
then applies the compact-target packing argument to the swapped realization.
No compactness assumption is made on either carrier. -/
theorem exists_packing_bound_of_pointedGHRealization_source_packing
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀ : 0 ≤ R₀)
    (hpack : ∀ (δ' R' : ℝ), 0 < δ' → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible X.base δ' R' → n ≤ N)
    (hHaus : pointedHausdorffDist R < min (δ / 8) 1) :
    ∃ N : ℕ, ∀ n, n ∈ packingAdmissible Y.base δ R₀ → n ≤ N := by
  obtain ⟨N, hN⟩ := hpack (δ / 8) (R₀ + 2 + δ / 8) (by linarith)
  exact exists_packing_bound_of_pointedGHRealization_source_packing_at
    R hδ hR₀ ⟨N, hN⟩ hHaus

/-- **Math.** An eventual buffered packing bound on a pointed-GH convergent
sequence transfers to the limit target.  Only the scale `δ / 8` and radius
`R₀ + 2 + δ / 8` are needed on the approximating spaces; one late index is
chosen simultaneously with a realization whose Hausdorff error is below
`min (δ / 8) 1`. -/
theorem exists_packing_bound_of_pointedGHConverges_source_packing
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (hconv : PointedGHConverges X Y)
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀ : 0 ≤ R₀)
    (hpack : ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ n, n ∈ packingAdmissible (X k).base (δ / 8)
        (R₀ + 2 + δ / 8) → n ≤ N) :
    ∃ N : ℕ, ∀ n, n ∈ packingAdmissible Y.base δ R₀ → n ≤ N := by
  obtain ⟨N, hN⟩ := hpack
  let ε : ℝ := min (δ / 16) (1 / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by norm_num)
  obtain ⟨Kdist, hKdist⟩ := (Metric.tendsto_atTop.1 hconv.2) ε hε
  obtain ⟨Kpack, hKpack⟩ := Filter.eventually_atTop.1 hN
  let k : ℕ := max Kdist Kpack
  have hKdist_le : Kdist ≤ k := Nat.le_max_left _ _
  have hKpack_le : Kpack ≤ k := Nat.le_max_right _ _
  have hdist : dist (pointedGHDistance (X k) Y) 0 < ε :=
    hKdist k hKdist_le
  have hgh : pointedGHDistance (X k) Y < ε := by
    simpa [Real.dist_eq, abs_of_nonneg
      (pointedGHDistance_nonneg (X k) Y)] using hdist
  obtain ⟨R, hR⟩ := exists_pointedGHRealization_lt_add
    (X k) Y hε
  have hε_le_δ : ε ≤ δ / 16 := min_le_left _ _
  have hε_le_one : ε ≤ 1 / 2 := min_le_right _ _
  have htwice : 2 * ε ≤ min (δ / 8) 1 := by
    apply le_min
    · linarith
    · linarith
  have hHaus : pointedHausdorffDist R < min (δ / 8) 1 := by
    calc
      pointedHausdorffDist R < pointedGHDistance (X k) Y + ε := hR
      _ < ε + ε := by linarith
      _ = 2 * ε := by ring
      _ ≤ min (δ / 8) 1 := htwice
  have hpack_k : ∀ n,
      n ∈ packingAdmissible (X k).base (δ / 8)
        (R₀ + 2 + δ / 8) → n ≤ N := hKpack k hKpack_le
  exact exists_packing_bound_of_pointedGHRealization_source_packing_at
    R hδ hR₀ ⟨N, hpack_k⟩ hHaus

/-- **Math.** A sequence converging in pointed Gromov--Hausdorff distance to a
compact target eventually has one uniform packing bound at every fixed
positive scale and nonnegative radius.  Finite prefixes are intentionally not
included: pointed convergence alone imposes no total-boundedness condition on
those terms. -/
theorem eventually_uniform_packing_bound_of_pointedGHConverges_compact_target
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}} [CompactSpace Y.carrier]
    (hconv : PointedGHConverges X Y)
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀ : 0 ≤ R₀) :
    ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ n, n ∈ packingAdmissible (X k).base δ R₀ → n ≤ N := by
  let η : ℝ := δ / 4
  have hη : 0 < η := by
    dsimp [η]
    linarith
  obtain ⟨N, hN⟩ :=
    exists_packing_bound_of_totallyBounded_closedBall
      Y.base (by linarith : 0 < η / 2)
      (ProperSpace.isCompact_closedBall Y.base
        ((R₀ + 1) + 1 + η / 2)).totallyBounded
  obtain ⟨L, hLfin, hLncard, hLcover⟩ :=
    exists_finite_ball_cover_of_uniform_packing_bound_with_card
      Y.base (R := R₀ + 1) (η := η) (by linarith) hη hN
  let ε : ℝ := min (δ / 16) (1 / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by norm_num)
  obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.1 hconv.2) ε hε
  have hevent : ∀ᶠ k in atTop,
      dist (pointedGHDistance (X k) Y) 0 < ε :=
    eventually_atTop.2 ⟨K₀, hK₀⟩
  refine ⟨N, ?_⟩
  filter_upwards [hevent] with k hk
  have hgh : pointedGHDistance (X k) Y < ε := by
    simpa [Real.dist_eq, abs_of_nonneg
      (pointedGHDistance_nonneg (X k) Y)] using hk
  obtain ⟨R, hR⟩ := exists_pointedGHRealization_lt_add
    (X k) Y hε
  have hε_le_δ : ε ≤ δ / 16 := min_le_left _ _
  have hε_le_one : ε ≤ 1 / 2 := min_le_right _ _
  have htwice : 2 * ε ≤ min (δ / 8) 1 := by
    apply le_min
    · linarith
    · linarith
  have hHaus : pointedHausdorffDist R < min (δ / 8) 1 := by
    calc
      pointedHausdorffDist R < pointedGHDistance (X k) Y + ε := hR
      _ < ε + ε := by linarith
      _ = 2 * ε := by ring
      _ ≤ min (δ / 8) 1 := htwice
  exact packing_bound_of_realization_and_target_cover
    R hδ hHaus L hLfin hLncard (by simpa [η] using hLcover)

/-! ## Countable finite-radius diagonalization -/

/-- **Math.** A countable family of sequences whose individual ranges have
compact closures admits one common subsequence along which every coordinate
converges.  This is the diagonal extraction interface used for expanding
finite-radius pointed approximations: each radius may have its own compact
carrier or compact closure, while the extracted index map is shared by all
radii. -/
theorem exists_subseq_tendsto_countable_compact_family
    {X : Type u} [TopologicalSpace X] [FirstCountableTopology X]
    (f : ℕ → ℕ → X)
    (hcompact : ∀ i, IsCompact (closure (Set.range (fun n => f n i)))) :
    ∃ a : ℕ → X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀ i, Tendsto (fun n => f (φ n) i) atTop (𝓝 (a i))) := by
  let S : Set (ℕ → X) :=
    Set.univ.pi (fun i => closure (Set.range (fun n => f n i)))
  have hS : IsCompact S := isCompact_univ_pi (fun i => hcompact i)
  let g : ℕ → (ℕ → X) := fun n i => f n i
  have hg : ∀ n, g n ∈ S := by
    intro n i hi
    exact subset_closure (Set.mem_range_self n)
  obtain ⟨a, ha, φ, hφ, hconv⟩ := hS.tendsto_subseq hg
  refine ⟨a, φ, hφ, ?_⟩
  intro i
  have happly : Tendsto (fun q : (ℕ → X) => q i) (𝓝 a) (𝓝 (a i)) :=
    (continuous_apply i).tendsto a
  have hcoord := happly.comp hconv
  simpa [g, Function.comp_def] using hcoord

/-- **Math.** Uniform packing bounds on a sequence of complete based metric
spaces yield one strictly monotone subsequence along which the compact closed
balls converge in Gromov--Hausdorff space at every integer radius
simultaneously.  The theorem supplies the common diagonal subsequence; it does
not yet identify compatible inclusions, basepoints, or an unbounded pointed
limit. -/
theorem exists_subseq_tendsto_closedBallGHSpace_of_uniform_packing_bounds
    (X : ℕ → BasedMetricSpaceBundle.{u})
    [∀ k, CompleteSpace (X k).carrier]
    (hpack : ∀ δ S, 0 < δ → ∃ N : ℕ, ∀ k n,
      n ∈ packingAdmissible (X k).base δ S → n ≤ N) :
    ∃ p : ℕ → _root_.GromovHausdorff.GHSpace, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      ∀ i, Tendsto
        (fun n => _root_.GromovHausdorff.toGHSpace
          (uniformPackingBoundedClosedBall X hpack (φ n) i).carrier)
        atTop (𝓝 (p i)) := by
  let v : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hv : Tendsto v atTop (𝓝 0) := by
    simpa [v] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hv_pos : ∀ m, 0 < v m := by
    intro m
    dsimp [v]
    positivity
  have hcompact : ∀ i, IsCompact
      (closure (Set.range (fun n => _root_.GromovHausdorff.toGHSpace
        (uniformPackingBoundedClosedBall X hpack n i).carrier))) := by
    intro i
    choose K hK using fun m =>
      hpack (v m / 2) ((i : ℝ) + 1 + v m / 2) (by
        have := hv_pos m
        linarith)
    apply isCompact_closure_range_toGHSpace_of_uniform_covers
      (X := fun n => (uniformPackingBoundedClosedBall X hpack n i).carrier)
      (C := 2 * (i : ℝ)) (u := v) (K := K) hv
    · intro n
      exact packingBoundedClosedBall_diam_le
        (X n) (i : ℝ) (Nat.cast_nonneg i)
          (packingBound_at_of_uniform_packing_bounds X hpack n)
    · intro n m
      change ∃ s : Set (Metric.closedBall (X n).base (i : ℝ)),
        Cardinal.mk s ≤ K m ∧
          (Set.univ : Set (Metric.closedBall (X n).base (i : ℝ))) ⊆
            ⋃ x ∈ s, Metric.ball x (v m)
      obtain ⟨L, hLfin, hLncard, hLcover⟩ :=
        exists_finite_closedBall_cover_of_uniform_packing_bound_with_card
          (X n).base (R := (i : ℝ)) (η := v m) (Nat.cast_nonneg i)
            (hv_pos m) (hK m n)
      refine ⟨L, ?_, hLcover⟩
      rw [← Set.cast_ncard hLfin]
      exact_mod_cast hLncard
  exact exists_subseq_tendsto_countable_compact_family
    (fun n i => _root_.GromovHausdorff.toGHSpace
      (uniformPackingBoundedClosedBall X hpack n i).carrier) hcompact

#print axioms Poincare.GromovHausdorff.exists_packing_bound_of_pointedGHRealization_source_packing_at
#print axioms Poincare.GromovHausdorff.exists_packing_bound_of_pointedGHRealization_source_packing
#print axioms Poincare.GromovHausdorff.exists_packing_bound_of_pointedGHConverges_source_packing

end Poincare.GromovHausdorff
