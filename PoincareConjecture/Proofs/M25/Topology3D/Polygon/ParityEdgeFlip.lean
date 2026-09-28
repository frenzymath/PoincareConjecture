import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CrossingShift
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CrossingParity
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.BoundaryBasics











set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

namespace PoincareConjecture.M25.Topology3D



theorem polygonCrossingParity_flip_near_edge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (p : Polygon E n) (X H : E →ₗ[ℝ] ℝ) (hX : Continuous X) (hH : Continuous H)
    (hcoords : Function.Injective (fun x => (X x, H x)))
    (he : ∀ j, H (p j) ≠ H (p (finRotate n j))) (i : Fin n) {q v : E}
    (hq : q ∈ p.edgeSet ℝ i) (hother : ∀ j, j ≠ i → q ∉ p.edgeSet ℝ j)
    (hverts : ∀ j, H (p j) ≠ H q) (hvX : X v = 1) (hvH : H v = 0)
    {U : Set E} (hU : U ∈ 𝓝 q) :
    ∃ t : ℝ, 0 < t ∧ q - t • v ∈ U ∧ q + t • v ∈ U ∧
      q - t • v ∉ p.boundary ℝ ∧ q + t • v ∉ p.boundary ℝ ∧
      polygonCrossingParity p X H (q - t • v) +
        polygonCrossingParity p X H (q + t • v) = 1 := by
  classical
  have hqseg : q ∈ segment ℝ (p i) (p (finRotate n i)) := by
    rwa [← polygon_edgeSet_eq_segment]
  have hqlevel := lineLevelPoint_eq_of_mem_segment H (he i) hqseg
  have hbounds : H q ∈ uIcc (H (p i)) (H (p (finRotate n i))) :=
    (lineLevelPoint_mem_segment_iff H (he i) (H q)).mp (by rwa [hqlevel])
  have hband : heightCrossing (H (p i)) (H (p (finRotate n i))) (H q) := by
    refine ⟨hbounds.1, ?_⟩
    rcases le_total (H (p i)) (H (p (finRotate n i))) with hle | hle
    · rw [max_eq_right hle]
      exact lt_of_le_of_ne (by simpa only [max_eq_right hle] using hbounds.2)
        (hverts (finRotate n i)).symm
    · rw [max_eq_left hle]
      exact lt_of_le_of_ne (by simpa only [max_eq_left hle] using hbounds.2) (hverts i).symm
  have hothers : ∀ᶠ z in 𝓝 q, ∀ j, j ≠ i → z ∉ p.edgeSet ℝ j ∧
      segmentRayParity X H (p j) (p (finRotate n j)) z =
        segmentRayParity X H (p j) (p (finRotate n j)) q := by
    apply eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ hj => (hj hji).elim
    · have havoid : ∀ᶠ z in 𝓝 q, z ∉ p.edgeSet ℝ j :=
        (polygon_edgeSet_isCompact p j).isClosed.isOpen_compl.mem_nhds (hother j hji)
      have hconst := segmentRayParity_eventually_eq X H hX hH hcoords (he j)
        (by simpa only [polygon_edgeSet_eq_segment] using hother j hji)
        (hverts j) (hverts (finRotate n j))
      filter_upwards [havoid, hconst] with z hz hc
      exact fun _ => ⟨hz, hc⟩
  have hnear := (show ∀ᶠ z in 𝓝 q, z ∈ U from hU).and hothers
  have hleft : Tendsto (fun t : ℝ => q - t • v) (𝓝 0) (𝓝 q) := by
    simpa only [zero_smul, sub_zero] using
      (continuous_const.fun_sub (continuous_id.smul continuous_const) :
        Continuous (fun t : ℝ => q - t • v)).tendsto 0
  have hright : Tendsto (fun t : ℝ => q + t • v) (𝓝 0) (𝓝 q) := by
    simpa only [zero_smul, add_zero] using
      (continuous_const.fun_add (continuous_id.smul continuous_const) :
        Continuous (fun t : ℝ => q + t • v)).tendsto 0
  have hparam := (hleft.eventually hnear).and (hright.eventually hnear)
  obtain ⟨r, hr, hrN⟩ := Metric.eventually_nhds_iff.mp hparam
  have ht : 0 < r / 2 := half_pos hr
  have hd : dist (r / 2) (0 : ℝ) < r := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using half_lt_self hr
  have hgood := hrN hd

  have hmiss (t : ℝ) (ht : t ≠ 0) : q + t • v ∉ p.edgeSet ℝ i := by
    intro hmem
    rw [polygon_edgeSet_eq_segment] at hmem
    have hrecover := lineLevelPoint_eq_of_mem_segment H (he i) hmem
    rw [map_add, map_smul, hvH, smul_zero, add_zero, hqlevel] at hrecover
    have hforward := congrArg X hrecover
    simp only [map_add, map_smul, hvX, smul_eq_mul, mul_one] at hforward
    exact ht (by linarith)
  refine ⟨r / 2, ht, hgood.1.1, hgood.2.1, ?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨j, hj⟩ := (polygon_mem_boundary_iff p _).mp hmem
    by_cases hji : j = i
    · subst j
      apply hmiss (-(r / 2)) (neg_ne_zero.mpr ht.ne')
      simpa only [neg_smul, sub_eq_add_neg] using hj
    · exact (hgood.1.2 j hji).1 hj
  · intro hmem
    obtain ⟨j, hj⟩ := (polygon_mem_boundary_iff p _).mp hmem
    by_cases hji : j = i
    · subst j
      exact hmiss (r / 2) ht.ne' hj
    · exact (hgood.2.2 j hji).1 hj
  · calc
      polygonCrossingParity p X H (q - (r / 2) • v) +
          polygonCrossingParity p X H (q + (r / 2) • v) =
          ∑ j, (segmentRayParity X H (p j) (p (finRotate n j)) (q - (r / 2) • v) +
            segmentRayParity X H (p j) (p (finRotate n j)) (q + (r / 2) • v)) :=
        Finset.sum_add_distrib.symm
      _ = segmentRayParity X H (p i) (p (finRotate n i)) (q - (r / 2) • v) +
          segmentRayParity X H (p i) (p (finRotate n i)) (q + (r / 2) • v) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [(hgood.1.2 j hji).2, (hgood.2.2 j hji).2]
          exact CharTwo.add_self_eq_zero _
        · simp
      _ = 1 := by
        rw [segmentRayParity_eq_one_horizontal_left X H hqseg hband hvX hvH ht,
          segmentRayParity_eq_zero_horizontal_right X H (he i) hqseg hvX hvH ht.le, add_zero]

end PoincareConjecture.M25.Topology3D
