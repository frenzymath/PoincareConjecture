import PoincareConjecture.Proofs.M14.Mathlib.InitialOperatorInjectivity
import PoincareConjecture.Proofs.M14.Mathlib.ClosedParameterDerivative










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]




theorem exists_open_initial_sliceDerivative_injective
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {b : ℝ} (hb : 0 < b) (f : ℝ × E → H)
    (hf : ContDiffOn ℝ ∞ f (Icc 0 b ×ˢ U)) (q : H)
    (hzero : ∀ y ∈ U, f (0, y) = q) (L : E →L[ℝ] H)
    (hL : Function.Injective L)
    (hvelocity : ∀ y ∈ U, derivWithin (fun s => f (s, y)) (Icc 0 b) 0 = L y) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ d : ℝ, 0 < d ∧ d ≤ b ∧
        ∀ y ∈ V, ∀ s ∈ Ioc 0 d,
          Function.Injective (fderiv ℝ (fun z => f (s, z)) y) := by
  let C := Icc (0 : ℝ) b
  let D := M08.spatialWithinFDeriv C U f
  let A := M08.timeWithinFDeriv C U f
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hb
  have h0 : (0 : ℝ) ∈ C := ⟨le_rfl, hb.le⟩
  have hD := M08.spatialWithinFDeriv_contDiffOn hC hU f hf
  have hA := M08.timeWithinFDeriv_contDiffOn hC hU f hf
  have hDzero (y : E) (hy : y ∈ U) : D (0, y) = 0 := by
    have heq : (fun z => f (0, z)) =ᶠ[𝓝 y] fun _ => q := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hzero z hz
    have hd := (M08.hasFDerivAt_spatialWithin hU f hf h0 hy).fderiv
    rw [heq.fderiv_eq, fderiv_const_apply] at hd
    exact hd.symm
  have hlinear : (fun y => A (0, y)) =ᶠ[𝓝 x] L := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ((M08.hasDerivWithinAt_timeWithin f hf h0 hy).derivWithin (hC 0 h0)).symm.trans
      (hvelocity y hy)
  have hsp : M08.spatialWithinFDeriv C U A (0, x) = L := by
    have hd := (M08.hasFDerivAt_spatialWithin hU A hA h0 hx).fderiv
    rw [hlinear.fderiv_eq, L.fderiv] at hd
    exact hd.symm
  have hjet : M08.timeWithinFDeriv C U D (0, x) = L := by
    ext v
    rw [M08.closed_time_spatial_commute hC hU f hf ⟨h0, hx⟩
      (M08.mem_closure_interior_Icc_prod hb hU h0 hx) v]
    exact congrArg (fun M : E →L[ℝ] H => M v) hsp
  obtain ⟨V, hV, hxV, hVU, d, hd, hdb, hgood⟩ :=
    exists_open_initial_operator_injective hU hx hb D hD hDzero L hL hjet
  refine ⟨V, hV, hxV, hVU, d, hd, hdb, ?_⟩
  intro y hy s hs
  rw [(M08.hasFDerivAt_spatialWithin hU f hf ⟨hs.1.le, hs.2.trans hdb⟩ (hVU hy)).fderiv]
  exact hgood y hy s hs

end PoincareConjecture.M14
