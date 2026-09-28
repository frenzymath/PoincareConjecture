import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarIntegerCoverArea

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Cover" => ℝ × ℝ

theorem scalar_integer_translate_no_overlap {E : Set Cover} (hE : IsOpen E)
    (hcover : ∀ᵐ z : Cover ∂volume,
      z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 → ∃ n : ℤ, z + (0, (n : ℝ)) ∈ E)
    (hmass : volume E ≤ 1) {x : Cover} (hx : x ∈ E) {k : ℤ} (hk : k ≠ 0) :
    x + (0, (k : ℝ)) ∉ E := by
  intro hxshift
  let v : Cover := (0, (k : ℝ))
  have hv : v ≠ 0 := by
    intro h
    have hcast : (k : ℝ) = 0 := congrArg Prod.snd h
    exact hk (by exact_mod_cast hcast)
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hS : IsOpen (E ∩ (fun y : Cover => y + v) ⁻¹' E) :=
    hE.inter (hE.preimage (continuous_id.add continuous_const))
  obtain ⟨s, hs, hsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hS.mem_nhds (show x ∈ E ∩ (fun y : Cover => y + v) ⁻¹' E from ⟨hx, hxshift⟩))
  let r := min s (‖v‖ / 3)
  let K := Metric.closedBall x r
  have hr : 0 < r := lt_min hs (div_pos hnorm (by norm_num))
  have hrle : r ≤ ‖v‖ / 3 := min_le_right _ _
  have hKS : K ⊆ E ∩ (fun y : Cover => y + v) ⁻¹' E :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hsmall
  have hKE : K ⊆ E := fun y hy => (hKS hy).1
  have hKm : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hshift_out (a : Cover) (ha : a ∈ K) : a + v ∉ K := by
    intro has
    have htriangle := dist_triangle (a + v) x a
    have heq : dist (a + v) a = ‖v‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    rw [heq, dist_comm x a] at htriangle
    have hdist1 : dist a x ≤ r := Metric.mem_closedBall.mp ha
    have hdist2 : dist (a + v) x ≤ r := Metric.mem_closedBall.mp has
    linarith
  have hmodified : ∀ᵐ z : Cover ∂volume,
      z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 →
        ∃ n : ℤ, z + (0, (n : ℝ)) ∈ E \ K := by
    filter_upwards [hcover] with z hz hzQ
    obtain ⟨n, hn⟩ := hz hzQ
    by_cases hnK : z + (0, (n : ℝ)) ∈ K
    · refine ⟨n + k, ?_⟩
      have heq : z + (0, ((n + k : ℤ) : ℝ)) = (z + (0, (n : ℝ))) + v := by
        ext <;> simp [v, add_assoc]
      rw [heq]
      exact ⟨(hKS hnK).2, hshift_out _ hnK⟩
    · exact ⟨n, hn, hnK⟩
  have hlower := scalar_area_ge_one_of_integer_cover (hE.measurableSet.diff hKm) hmodified
  have hpositive : 0 < volume K :=
    (Metric.isOpen_ball.measure_pos volume ⟨x, Metric.mem_ball_self hr⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  have hpartition : volume K + volume (E \ K) = volume E := by
    simpa only [inter_eq_right.mpr hKE] using measure_inter_add_sdiff E hKm
  have hsum : (1 : ℝ≥0∞) + volume K ≤ 1 + 0 := by
    simpa only [add_zero] using calc
      (1 : ℝ≥0∞) + volume K ≤ volume (E \ K) + volume K := add_le_add hlower le_rfl
      _ = volume E := by rw [add_comm, hpartition]
      _ ≤ 1 := hmass
  have hzero : volume K ≤ 0 := (ENNReal.add_le_add_iff_left (by norm_num)).mp hsum
  exact hpositive.not_ge hzero

end PoincareConjecture.M64Uniformization
