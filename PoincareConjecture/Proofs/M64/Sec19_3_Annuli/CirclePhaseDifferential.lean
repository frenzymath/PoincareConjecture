import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCircleCurrent





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}





theorem m64CirclePhase_current
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {L : LoopPlane → ℝ} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 (n + 1)) f p)
    (hL : DifferentiableAt ℝ L p)
    (hquot : P.circle.quotient ∘ L =ᶠ[𝓝 p] Prod.snd ∘ f) (i : Fin 2) :
    fderiv ℝ L p (EuclideanSpace.single i 1) = m64AnnulusCircleCurrent P t f i p := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let v : LoopPlane := EuclideanSpace.single i 1
  let W := mfderiv (𝓡 2) (𝓡 (n + 1)) f p v
  have hsnd : MDifferentiable (𝓡 (n + 1)) (𝓡 1)
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiable (by simp)
  have hpr := mfderiv_comp_apply (f := f)
    (g := (Prod.snd : P.charts.Point → P.circle.Point)) p (hsnd (f p)) hf v
  have hl := mfderiv_comp_apply (f := L) (g := P.circle.quotient) p
    (P.circle.quotient_smooth.mdifferentiableAt (by simp))
    hL.hasFDerivAt.hasMFDerivAt.mdifferentiableAt v
  rw [hquot.mfderiv_eq, mfderiv_eq_fderiv] at hl
  have hv : (P.charts.split (f p) W).2 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (L p) (fderiv ℝ L p v) := by
    rw [P.charts.split_circle]
    exact hpr.symm.trans hl
  have hpoint : P.circle.quotient (L p) = (f p).2 := hquot.eq_of_nhds
  have hsplit : P.charts.split (f p) (P.charts.circleUnit (f p)) =
      (0, P.circle.frame (f p).2) := (P.charts.split (f p)).apply_symm_apply _
  change fderiv ℝ L p v = (P.flow.metric t).inner (f p) W (P.charts.circleUnit (f p))
  rw [P.metric_eq, hsplit]
  simp only [map_zero, zero_add]
  rw [hv, ← hpoint]
  simp only [M62.CircleGeometry.quotient, P.circle.frame_quotient]
  simpa +instances only [M62.CircleGeometry.quotient, M62.CircleGeometry.metricOnPoints,
    mul_one] using! (P.circle.metric_quotient (L p) (fderiv ℝ L p v) 1).symm

end PoincareConjecture
