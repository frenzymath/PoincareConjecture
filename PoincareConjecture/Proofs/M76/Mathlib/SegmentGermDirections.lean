import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalize_sub_ne_of_segment_inter {p u v : E}
    (hu : u ≠ p) (hv : v ≠ p)
    (hinter : segment ℝ p u ∩ segment ℝ p v ⊆ {p}) :
    normalize (u - p) ≠ normalize (v - p) := by
  apply normalize_ne_of_segment_inter (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hv)
  intro x hx
  have huadd : p + (u - p) = u := by abel
  have hvadd : p + (v - p) = v := by abel
  have hxu : p + x ∈ segment ℝ p u := by
    simpa only [add_zero, huadd] using (mem_segment_translate ℝ p).mpr hx.1
  have hxv : p + x ∈ segment ℝ p v := by
    simpa only [add_zero, hvadd] using (mem_segment_translate ℝ p).mpr hx.2
  have hpx : p + x = p := hinter ⟨hxu, hxv⟩
  exact add_left_cancel (hpx.trans (add_zero p).symm)

theorem normalize_sub_mem_pair_of_segment_local
    {S : Set E} {p u a b : E} (hu : u ≠ p)
    (hsegment : segment ℝ p u ⊆ S)
    (hlocal : ∀ᶠ x in 𝓝 p, x ∈ S → x ∈ segment ℝ p a ∪ segment ℝ p b) :
    normalize (u - p) ∈ ({normalize (a - p), normalize (b - p)} : Set E) := by
  have htend : Tendsto (fun z : E => p + z) (𝓝 0) (𝓝 p) := by
    have h : Tendsto (fun z : E => p + z) (𝓝 0) (𝓝 (p + 0)) :=
      (continuous_const.add continuous_id).continuousAt
    simpa only [add_zero] using h
  have hN : {z : E | p + z ∈ S → p + z ∈ segment ℝ p a ∪ segment ℝ p b} ∈ 𝓝 0 :=
    htend.eventually hlocal
  obtain ⟨r, hr, hNr⟩ := Set.exists_pos_smul_mem_of_mem_nhds hN (u - p)
  let x := p + r • (u - p)
  have hxu : x ∈ segment ℝ p u := by
    have huadd : p + (u - p) = u := by abel
    have hru : r • (u - p) ∈ segment ℝ 0 (u - p) :=
      (convex_segment (0 : E) (u - p)).smul_mem_of_zero_mem
        (left_mem_segment ℝ 0 (u - p)) (right_mem_segment ℝ 0 (u - p))
        ⟨hr.1.le, hr.2⟩
    simpa only [add_zero, huadd] using (mem_segment_translate ℝ p).mpr hru
  have hxp : x - p = r • (u - p) := by dsimp only [x]; abel
  have hxne : x - p ≠ 0 := by
    rw [hxp]
    exact smul_ne_zero hr.1.ne' (sub_ne_zero.mpr hu)
  have hxdir : normalize (x - p) = normalize (u - p) := by
    rw [hxp]
    exact normalize_smul_of_pos hr.1 (u - p)
  have hdir (v : E) (hxv : x ∈ segment ℝ p v) :
      normalize (u - p) = normalize (v - p) := by
    have hsub : x - p ∈ segment ℝ 0 (v - p) := by
      simpa only [neg_add_cancel, ← sub_eq_neg_add] using
        (mem_segment_translate ℝ (-p)).mpr hxv
    exact hxdir.symm.trans (normalize_eq_of_mem_segment_zero hsub hxne)
  rcases hNr (hsegment hxu) with hxa | hxb
  · exact Or.inl (hdir a hxa)
  · exact Or.inr (hdir b hxb)

theorem not_three_segments_in_two_segment_germ
    {S : Set E} {p u v w a b : E}
    (hu : u ≠ p) (hv : v ≠ p) (hw : w ≠ p)
    (huv : segment ℝ p u ∩ segment ℝ p v ⊆ {p})
    (huw : segment ℝ p u ∩ segment ℝ p w ⊆ {p})
    (hvw : segment ℝ p v ∩ segment ℝ p w ⊆ {p})
    (huS : segment ℝ p u ⊆ S) (hvS : segment ℝ p v ⊆ S)
    (hwS : segment ℝ p w ⊆ S)
    (hlocal : ∀ᶠ x in 𝓝 p, x ∈ S → x ∈ segment ℝ p a ∪ segment ℝ p b) : False := by
  have hunev := normalize_sub_ne_of_segment_inter hu hv huv
  have hunew := normalize_sub_ne_of_segment_inter hu hw huw
  have hvnew := normalize_sub_ne_of_segment_inter hv hw hvw
  have hdu := normalize_sub_mem_pair_of_segment_local hu huS hlocal
  have hdv := normalize_sub_mem_pair_of_segment_local hv hvS hlocal
  have hdw := normalize_sub_mem_pair_of_segment_local hw hwS hlocal
  rcases hdu with hu | hu <;> rcases hdv with hv | hv <;> rcases hdw with hw | hw
  all_goals first
    | exact hunev (hu.trans hv.symm)
    | exact hunew (hu.trans hw.symm)
    | exact hvnew (hv.trans hw.symm)

end NormedSpace
