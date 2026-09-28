import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.MorseCoordinates.Factors
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.CoordinateRescaling

noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem exists_chartHeight_signed_square_coordinates {z : Real}
    (hl : (3 / 5 : Real) < z) (hu : z < 5 / 8)
    (hcrit : meridianRoot z * (2*z - 1) = (3 / 10) * z) :
    ∃ e : OpenPartialHomeomorph E2 E2,
      0 ∈ e.source ∧ e 0 = 0 ∧ MapsTo e e.source (coordinateDomain z) ∧
      ContDiffOn Real ∞ e e.source ∧ ContDiffOn Real ∞ e.symm e.target ∧
      ∀ x ∈ e.source, chartHeight z (e x) = chartHeight z 0 - (x 0)^2 + (x 1)^2 := by
  have hz : 0 < 1 - z^2 := by nlinarith
  have h0 : (0 : E2) ∈ coordinateDomain z := by simpa [coordinateDomain] using hz
  have hW := isOpen_coordinateDomain z
  obtain ⟨ha, hb⟩ := coefficients_smooth hz
  have hapos := negativeCoefficient_zero_pos hl hu
  have hane : {q | 0 < negativeCoefficient z q} ∈ 𝓝 (0 : E2) :=
    (ha.continuousOn 0 h0).continuousAt (hW.mem_nhds h0) |>.preimage_mem_nhds
      (Ioi_mem_nhds hapos)
  let U := coordinateDomain z ∩ interior {q | 0 < negativeCoefficient z q}
  have hU : IsOpen U := hW.inter isOpen_interior
  have h0U : (0 : E2) ∈ U := ⟨h0, mem_interior_iff_mem_nhds.mpr hane⟩
  have haU (q : E2) (hq : q ∈ U) : 0 < negativeCoefficient z q :=
    interior_subset (s := {q : E2 | 0 < negativeCoefficient z q}) hq.2
  have hbU (q : E2) (hq : q ∈ U) : 0 < positiveCoefficient z q := positiveCoefficient_pos hq.1
  obtain ⟨e, he0, hezero, heU, he, hei, hcoords⟩ :=
    Poincare.Analysis.Calculus.Morse.exists_diagonal_rescaling_localInverse hU h0U
      ((ha.mono inter_subset_left).sqrt (fun q hq => (haU q hq).ne'))
      ((hb.mono inter_subset_left).sqrt (fun q hq => (hbU q hq).ne'))
      (Real.sqrt_pos.mpr hapos).ne' (Real.sqrt_pos.mpr (hbU 0 h0U)).ne'
  refine ⟨e, he0, hezero, (fun x hx => (heU hx).1), he, hei, ?_⟩
  intro x hx
  have hxe := heU hx
  obtain ⟨hneg, hpos⟩ := hcoords x hx
  have hn : negativeCoefficient z (e x) * (e x 0)^2 = (x 0)^2 := by
    simpa only [mul_pow, Real.sq_sqrt (haU _ hxe).le] using
      congrArg (fun y : Real => y^(2 : Nat)) hneg
  have hp : positiveCoefficient z (e x) * (e x 1)^2 = (x 1)^2 := by
    simpa only [mul_pow, Real.sq_sqrt (hbU _ hxe).le] using
      congrArg (fun y : Real => y^(2 : Nat)) hpos
  rw [chartHeight_eq_signed_factors hz hcrit hxe.1, hn, hp]

end Poincare.Manifold.Schoenflies.Saddle.Nested
