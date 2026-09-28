import PoincareConjecture.Proofs.M08.ChartConnectionVariation

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem parameterDerivative_contDiffOn
    {C : Set ℝ} {U : Set E} (hC : UniqueDiffOn ℝ C) (hU : IsOpen U)
    (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U))
    {x : E} (hx : x ∈ U) (v : E) :
    ContDiffOn ℝ ∞ (fun r => fderiv ℝ (fun y => f (r, y)) x v) C := by
  have hD := (M08.spatialWithinFDeriv_contDiffOn hC hU f hf).comp
    (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hr => ⟨hr, hx⟩)
  apply (hD.clm_apply (contDiffOn_const (c := v))).congr
  intro r hr
  exact congrArg (fun L : E →L[ℝ] H => L v)
    (M08.hasFDerivAt_spatialWithin hU f hf hr hx).fderiv

theorem hasDerivWithinAt_parameterDerivative
    {C : Set ℝ} {U : Set E} (hC : UniqueDiffOn ℝ C) (hU : IsOpen U)
    (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U))
    {s : ℝ} {x : E} (hs : s ∈ C) (hx : x ∈ U)
    (hcl : (s, x) ∈ closure (interior (C ×ˢ U))) (v : E) :
    HasDerivWithinAt (fun r => fderiv ℝ (fun y => f (r, y)) x v)
      (fderiv ℝ (fun y => derivWithin (fun r => f (r, y)) C s) x v) C s := by
  let D := M08.spatialWithinFDeriv C U f
  let A := M08.timeWithinFDeriv C U f
  have hD := M08.spatialWithinFDeriv_contDiffOn hC hU f hf
  have hA := M08.timeWithinFDeriv_contDiffOn hC hU f hf
  have hd := (M08.hasDerivWithinAt_timeWithin D hD hs hx).clm_apply
    (hasDerivWithinAt_const s C v)
  have hcomm := M08.closed_time_spatial_commute hC hU f hf ⟨hs, hx⟩ hcl v
  have ht : (fun y => derivWithin (fun r => f (r, y)) C s) =ᶠ[𝓝 x] fun y => A (s, y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (M08.hasDerivWithinAt_timeWithin f hf hs hy).derivWithin (hC s hs)
  have hAderiv := (M08.hasFDerivAt_spatialWithin hU A hA hs hx).fderiv
  have htarget : fderiv ℝ (fun y => derivWithin (fun r => f (r, y)) C s) x v =
      M08.timeWithinFDeriv C U D (s, x) v := by
    rw [ht.fderiv_eq, hAderiv]
    exact hcomm.symm
  rw [htarget]
  apply (show HasDerivWithinAt (fun r => D (r, x) v)
      (M08.timeWithinFDeriv C U D (s, x) v) C s by
    simpa only [map_zero, add_zero] using hd).congr_of_mem _ hs
  intro r hr
  exact congrArg (fun L : E →L[ℝ] H => L v)
    (M08.hasFDerivAt_spatialWithin hU f hf hr hx).fderiv

theorem hasDerivWithinAt_parameterDerivative_Icc
    {a b : ℝ} (hab : a < b) {U : Set E} (hU : IsOpen U)
    (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U))
    {s : ℝ} {x : E} (hs : s ∈ Icc a b) (hx : x ∈ U) (v : E) :
    HasDerivWithinAt (fun r => fderiv ℝ (fun y => f (r, y)) x v)
      (fderiv ℝ (fun y => derivWithin (fun r => f (r, y)) (Icc a b) s) x v)
      (Icc a b) s :=
  hasDerivWithinAt_parameterDerivative (uniqueDiffOn_Icc hab) hU f hf hs hx
    (M08.mem_closure_interior_Icc_prod hab hU hs hx) v

end PoincareConjecture.M14
