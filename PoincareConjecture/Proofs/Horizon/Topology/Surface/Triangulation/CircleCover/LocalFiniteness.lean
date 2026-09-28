import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Locality
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartLevel.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Finiteness

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

omit [T2Space M] [IsManifold (𝓡 2) ∞ M] in

theorem exists_finite_complement_chartCircle (x : M) {r : ℝ} (hr : 0 < r)
    (htarget : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    {p : M} (hp : p ∈ chartCircle x r) {s : Set M} (hs : s ∈ 𝓝 p) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ s ∧
      Finite (ConnectedComponents ((W \ chartCircle x r) : Set M)) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hps := chartCircle_subset_chart_source x htarget hp
  obtain ⟨hf, hdf⟩ := chartCircle_coordinateSquaredRadius_regular x hr htarget hp
  have hlevel := (mem_chartCircle_iff_norm_sq x hr htarget hps).mp hp
  apply exists_finite_complement_chart_regular_level c hps hf hdf
    (c.open_target.mem_nhds (c.map_source hps)) _ hs
  intro z hz
  have h := mem_chartCircle_iff_norm_sq x hr htarget (c.map_target hz)
  change c.symm z ∈ chartCircle x r ↔ ‖c (c.symm z) - c x‖ ^ 2 = r ^ 2 at h
  rw [c.right_inv hz] at h
  change c.symm z ∈ chartCircle x r ↔ ‖z - c x‖ ^ 2 = ‖c p - c x‖ ^ 2
  rw [show ‖c p - c x‖ ^ 2 = r ^ 2 from hlevel]
  exact h

omit [T2Space M] in

theorem exists_finite_complement_chartCircle_pair (x y : M) {rx ry : ℝ}
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) rx ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hysub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) y y) ry ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) y).target)
    {p : M} (hpx : p ∈ chartCircle x rx) (hpy : p ∈ chartCircle y ry)
    (hregular : ChartCircleRegularAlong x rx y ry)
    {s : Set M} (hs : s ∈ 𝓝 p) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ s ∧
      Finite (ConnectedComponents ((W \ (chartCircle x rx ∪ chartCircle y ry)) : Set M)) := by
  obtain ⟨hfval, hgval, hf, hg, hdf, v, hvf, hvg⟩ :=
    chartCircle_pair_coordinate_derivatives x y hrx hry hxsub hysub hpx hpy hregular
  obtain ⟨N, hN, hpN, _, hly, hlx⟩ :=
    chartCircle_pair_local_level_sets x y hrx hry hxsub hysub hpx hpy
  apply exists_finite_complement_chart_transverse_levels
    (chartAt (EuclideanSpace ℝ (Fin 2)) y)
    (chartCircle_subset_chart_source y hysub hpy) hf hg hdf hvf hvg
    (hN.mem_nhds hpN) _ hs
  intro z hz
  simp only [mem_union, hlx z hz, hly z hz, hfval, hgval, or_comm]

theorem exists_finite_complement_chartCircle_arrangement
    (s : Finset M) (r : M → ℝ) (hpos : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (htriple : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
      ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) →
        p ∉ chartCircle z (r z))
    (hregular : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ChartCircleRegularAlong x (r x) y (r y) ∨
        ChartCircleRegularAlong y (r y) x (r x))
    {p : M} (hp : p ∈ ⋃ x ∈ s, chartCircle x (r x)) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      Finite (ConnectedComponents ((W \ (⋃ x ∈ s, chartCircle x (r x))) : Set M)) := by
  obtain ⟨N, hN, hpN, hlocal | hlocal⟩ :=
    exists_open_chartCircle_locality s r htarget htriple hp
  · obtain ⟨i, hi, hpi, hlocal⟩ := hlocal
    obtain ⟨W, hW, hpW, hWN, hfin⟩ := exists_finite_complement_chartCircle i
      (hpos i hi) (htarget i hi) hpi (hN.mem_nhds hpN)
    refine ⟨W, hW, hpW, ?_⟩
    have heq : W \ (⋃ x ∈ s, chartCircle x (r x)) = W \ chartCircle i (r i) := by
      ext q
      have hq : q ∈ N → (q ∈ ⋃ x ∈ s, chartCircle x (r x) ↔ q ∈ chartCircle i (r i)) := by
        intro hqN
        simpa only [mem_inter_iff, hqN, true_and] using Iff.of_eq (congrArg (q ∈ ·) hlocal)
      simp only [mem_sdiff]
      exact and_congr_right fun hqW => not_congr (hq (hWN hqW))
    rwa [heq]
  · obtain ⟨i, hi, j, hj, hij, hpi, hlocal⟩ := hlocal
    have hex : ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ N ∧
        Finite (ConnectedComponents ((W \ (chartCircle i (r i) ∪ chartCircle j (r j))) : Set M)) := by
      rcases hregular i hi j hj hij with hreg | hreg
      · exact exists_finite_complement_chartCircle_pair i j (hpos i hi) (hpos j hj)
          (htarget i hi) (htarget j hj) hpi.1 hpi.2 hreg (hN.mem_nhds hpN)
      · rw [union_comm (chartCircle i (r i))]
        exact exists_finite_complement_chartCircle_pair j i
          (hpos j hj) (hpos i hi) (htarget j hj) (htarget i hi) hpi.2 hpi.1 hreg
          (hN.mem_nhds hpN)
    obtain ⟨W, hW, hpW, hWN, hfin⟩ := hex
    refine ⟨W, hW, hpW, ?_⟩
    have heq : W \ (⋃ x ∈ s, chartCircle x (r x)) =
        W \ (chartCircle i (r i) ∪ chartCircle j (r j)) := by
      ext q
      have hq : q ∈ N → (q ∈ ⋃ x ∈ s, chartCircle x (r x) ↔
          q ∈ chartCircle i (r i) ∪ chartCircle j (r j)) := by
        intro hqN
        simpa only [mem_inter_iff, hqN, true_and] using Iff.of_eq (congrArg (q ∈ ·) hlocal)
      simp only [mem_sdiff]
      exact and_congr_right fun hqW => not_congr (hq (hWN hqW))
    rwa [heq]

theorem finite_regions_of_chart_circle_general_position
    (s : Finset M) (r : M → ℝ) (hpos : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hcover : (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)) = (univ : Set M))
    (htriple : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
      ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) →
        p ∉ chartCircle z (r z))
    (hregular : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ChartCircleRegularAlong x (r x) y (r y) ∨
        ChartCircleRegularAlong y (r y) x (r x)) :
    Finite (ConnectedComponents ((chartDiskBoundaryUnion s r)ᶜ : Set M)) := by
  apply finite_regions_of_finite_local_complements s r hpos htarget hcover
  rw [chartDiskBoundaryUnion_eq_iUnion_chartCircle s r hpos htarget]
  exact fun p hp => exists_finite_complement_chartCircle_arrangement
    s r hpos htarget htriple hregular hp

theorem exists_finite_chart_disk_cover_finite_regions [CompactSpace M] :
    ∃ (s : Finset M) (r : M → ℝ),
      (∀ x ∈ s, 0 < r x) ∧
      (∀ x ∈ s, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)) = (univ : Set M) ∧
      Finite (ConnectedComponents ((⋃ x ∈ s,
        frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)))ᶜ : Set M)) := by
  obtain ⟨s, r, hpos, htarget, hcover, _, htriple, hregular⟩ :=
    exists_finite_chart_ball_cover_general_position (M := M)
  exact ⟨s, r, hpos, htarget, hcover,
    finite_regions_of_chart_circle_general_position s r hpos htarget hcover htriple hregular⟩

end PoincareConjecture.Topology.Surface
