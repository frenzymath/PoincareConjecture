import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.CoordinateRescaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem exists_signed_square_coordinates_of_factors
    {U : Set E2} (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    {a b H : E2 → Real} {c : Real}
    (ha : ContDiffOn Real ∞ a U) (hb : ContDiffOn Real ∞ b U)
    (ha0 : a 0 ≠ 0) (hb0 : b 0 ≠ 0)
    (hform : ∀ q ∈ U, H q = c + a q * (q 0)^2 + b q * (q 1)^2) :
    ∃ e : OpenPartialHomeomorph E2 E2, ∃ s t : Real,
      (s = -1 ∨ s = 1) ∧ (t = -1 ∨ t = 1) ∧
      0 ∈ e.source ∧ e 0 = 0 ∧ MapsTo e e.source U ∧
      ContDiffOn Real ∞ e e.source ∧ ContDiffOn Real ∞ e.symm e.target ∧
      ∀ x ∈ e.source, H (e x) = c + s * (x 0)^2 + t * (x 1)^2 := by
  obtain ⟨s, hs, hsa⟩ : ∃ s : Real, (s = -1 ∨ s = 1) ∧ 0 < s * a 0 := by
    rcases lt_or_gt_of_ne ha0 with hn | hp
    · exact ⟨-1, Or.inl rfl, by nlinarith⟩
    · exact ⟨1, Or.inr rfl, by nlinarith⟩
  obtain ⟨t, ht, htb⟩ : ∃ t : Real, (t = -1 ∨ t = 1) ∧ 0 < t * b 0 := by
    rcases lt_or_gt_of_ne hb0 with hn | hp
    · exact ⟨-1, Or.inl rfl, by nlinarith⟩
    · exact ⟨1, Or.inr rfl, by nlinarith⟩
  have has : ContDiffOn Real ∞ (fun q => s * a q) U := contDiffOn_const.mul ha
  have hbt : ContDiffOn Real ∞ (fun q => t * b q) U := contDiffOn_const.mul hb
  have hsaN : {q | 0 < s * a q} ∈ 𝓝 (0 : E2) :=
    (has.continuousOn 0 h0).continuousAt (hU.mem_nhds h0) |>.preimage_mem_nhds
      (Ioi_mem_nhds hsa)
  have htbN : {q | 0 < t * b q} ∈ 𝓝 (0 : E2) :=
    (hbt.continuousOn 0 h0).continuousAt (hU.mem_nhds h0) |>.preimage_mem_nhds
      (Ioi_mem_nhds htb)
  let V := U ∩ (interior {q | 0 < s * a q} ∩ interior {q | 0 < t * b q})
  have hV : IsOpen V := hU.inter (isOpen_interior.inter isOpen_interior)
  have h0V : (0 : E2) ∈ V :=
    ⟨h0, mem_interior_iff_mem_nhds.mpr hsaN, mem_interior_iff_mem_nhds.mpr htbN⟩
  have haV (q : E2) (hq : q ∈ V) : 0 < s * a q :=
    interior_subset (s := {q | 0 < s * a q}) hq.2.1
  have hbV (q : E2) (hq : q ∈ V) : 0 < t * b q :=
    interior_subset (s := {q | 0 < t * b q}) hq.2.2
  obtain ⟨e, he0, hez, heV, he, hei, hcoords⟩ :=
    Poincare.Analysis.Calculus.Morse.exists_diagonal_rescaling_localInverse hV h0V
      ((has.mono inter_subset_left).sqrt (fun q hq => (haV q hq).ne'))
      ((hbt.mono inter_subset_left).sqrt (fun q hq => (hbV q hq).ne'))
      (Real.sqrt_pos.mpr hsa).ne' (Real.sqrt_pos.mpr htb).ne'
  refine ⟨e, s, t, hs, ht, he0, hez, fun x hx => (heV hx).1, he, hei, ?_⟩
  intro x hx
  obtain ⟨hae, hbe⟩ := hcoords x hx
  have ha2 : (s * a (e x)) * (e x 0)^2 = (x 0)^2 := by
    simpa only [mul_pow, Real.sq_sqrt (haV _ (heV hx)).le] using
      congrArg (fun y : Real => y^(2 : Nat)) hae
  have hb2 : (t * b (e x)) * (e x 1)^2 = (x 1)^2 := by
    simpa only [mul_pow, Real.sq_sqrt (hbV _ (heV hx)).le] using
      congrArg (fun y : Real => y^(2 : Nat)) hbe
  rw [hform _ (heV hx).1]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> nlinarith

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model
