import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineCutOrientation










set_option autoImplicit false

open Set AffineMap CoordinateHalfBoxes

namespace ContinuousAffineEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem original_endpoint_signs_of_forward_tail
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) {a b : E} (hab : a ≠ b)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hf0 : f 0 = lineMap a b t)
    {r : ℝ} (hr : 0 < r)
    (hforward : ∀ x ∈ box r, f x ∈ lineMap a b '' Icc t 1 →
      x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) :
    (f.symm a).1.1 = 0 ∧ (f.symm a).2 = 0 ∧
      (f.symm b).1.1 = 0 ∧ (f.symm b).2 = 0 ∧
      (f.symm a).1.2 < 0 ∧ 0 < (f.symm b).1.2 ∧
      0 < (f.symm b).1.2 - (f.symm a).1.2 := by
  have hzero : f.symm (lineMap a b t) = 0 := by
    rw [← hf0, f.symm_apply_apply]
  let V : Set ℝ := (fun u => f.symm (lineMap a b u)) ⁻¹' interior (box r)
  have hV : IsOpen V := isOpen_interior.preimage
    (f.symm.continuous.comp (ContinuousAffineMap.lineMap a b).continuous)
  have htV : t ∈ V := by
    change f.symm (lineMap a b t) ∈ interior (box r)
    rw [hzero]
    exact zero_mem_interior_box hr
  have htclosure : t ∈ closure (Ioo t 1) := by
    rw [closure_Ioo ht.2.ne]
    exact ⟨le_rfl, ht.2.le⟩
  obtain ⟨u, huV, hu⟩ := mem_closure_iff.mp htclosure V hV htV
  have huB : f.symm (lineMap a b u) ∈ box r := interior_subset huV
  have haxis := hforward (f.symm (lineMap a b u)) huB
    (by rw [f.apply_symm_apply]; exact ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩)
  have hne : f.symm (lineMap a b u) ≠ 0 := by
    intro h
    have heq : lineMap a b u = lineMap a b t := by
      calc
        lineMap a b u = f (f.symm (lineMap a b u)) := (f.apply_symm_apply _).symm
        _ = f 0 := congrArg f h
        _ = lineMap a b t := hf0
    exact hu.1.ne' (lineMap_injective ℝ hab heq)
  have hpositive : 0 < (f.symm (lineMap a b u)).1.2 := by
    apply lt_of_le_of_ne haxis.2.2
    intro h
    exact hne (Prod.ext (Prod.ext haxis.1 h.symm) haxis.2.1)
  have hfirst (v : ℝ) : (f.symm (lineMap a b v)).1.1 =
      v * ((f.symm b).1.1 - (f.symm a).1.1) + (f.symm a).1.1 := by
    have h := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.1)
      (f.symm.toAffineEquiv.apply_lineMap a b v)
    simpa only [fst_lineMap, snd_lineMap, lineMap_apply_ring',
      ContinuousAffineEquiv.coe_coe] using h
  have hsecond (v : ℝ) : (f.symm (lineMap a b v)).1.2 =
      v * ((f.symm b).1.2 - (f.symm a).1.2) + (f.symm a).1.2 := by
    have h := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2)
      (f.symm.toAffineEquiv.apply_lineMap a b v)
    simpa only [fst_lineMap, snd_lineMap, lineMap_apply_ring',
      ContinuousAffineEquiv.coe_coe] using h
  have hlast (v : ℝ) : (f.symm (lineMap a b v)).2 =
      v * ((f.symm b).2 - (f.symm a).2) + (f.symm a).2 := by
    have h := congrArg (fun x : (ℝ × ℝ) × ℝ => x.2)
      (f.symm.toAffineEquiv.apply_lineMap a b v)
    simpa only [fst_lineMap, snd_lineMap, lineMap_apply_ring',
      ContinuousAffineEquiv.coe_coe] using h
  have hscalar_zero {c d : ℝ} (ht0 : 0 = t * (d - c) + c)
      (hu0 : 0 = u * (d - c) + c) : c = 0 ∧ d = 0 := by
    have hmul : (u - t) * (d - c) = 0 := by nlinarith
    have hd : d - c = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hu.1.ne')
    rw [hd, mul_zero, zero_add] at ht0
    exact ⟨ht0.symm, (sub_eq_zero.mp hd).trans ht0.symm⟩
  have htf := hfirst t
  have huf := hfirst u
  rw [hzero] at htf
  rw [haxis.1] at huf
  change 0 = t * ((f.symm b).1.1 - (f.symm a).1.1) + (f.symm a).1.1 at htf
  obtain ⟨haf, hbf⟩ := hscalar_zero htf huf
  have htl := hlast t
  have hul := hlast u
  rw [hzero] at htl
  rw [haxis.2.1] at hul
  change 0 = t * ((f.symm b).2 - (f.symm a).2) + (f.symm a).2 at htl
  obtain ⟨hal, hbl⟩ := hscalar_zero htl hul
  have hts := hsecond t
  have hus := hsecond u
  rw [hzero] at hts
  change 0 = t * ((f.symm b).1.2 - (f.symm a).1.2) + (f.symm a).1.2 at hts
  have hproduct : 0 < (u - t) * ((f.symm b).1.2 - (f.symm a).1.2) := by
    nlinarith
  have hslope : 0 < (f.symm b).1.2 - (f.symm a).1.2 :=
    (mul_pos_iff_of_pos_left (sub_pos.mpr hu.1)).mp hproduct
  refine ⟨haf, hal, hbf, hbl, ?_, ?_, hslope⟩
  · nlinarith [mul_pos ht.1 hslope]
  · nlinarith [mul_pos (sub_pos.mpr ht.2) hslope]

end ContinuousAffineEquiv

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}





theorem original_endpoint_signs_of_oriented_cut
    (P : Polygon E (n + 3)) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (i : Fin (n + 3)) (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hf0 : f 0 = P.edgeCut t i) {r : ℝ} (hr : 0 < r)
    (harc : ∀ x ∈ box r, f x ∈ P.cutArc t i ↔
      x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) :
    (f.symm (P i)).1.1 = 0 ∧ (f.symm (P i)).2 = 0 ∧
      (f.symm (P (finRotate (n + 3) i))).1.1 = 0 ∧
      (f.symm (P (finRotate (n + 3) i))).2 = 0 ∧
      (f.symm (P i)).1.2 < 0 ∧ 0 < (f.symm (P (finRotate (n + 3) i))).1.2 ∧
      0 < (f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2 := by
  apply f.original_endpoint_signs_of_forward_tail
    (P.edge_endpoints_ne_of_injective hinj i) (ht i) hf0 hr
  intro x hx htail
  exact (harc x hx).mp (Or.inl htail)

end Polygon
