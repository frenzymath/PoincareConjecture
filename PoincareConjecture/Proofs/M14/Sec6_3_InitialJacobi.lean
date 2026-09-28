import PoincareConjecture.Proofs.M14.Sec6_3_InitialJacobiInterior
import PoincareConjecture.Proofs.M14.Mathlib.SectionThroughVector










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}




theorem initialValuePath_differential_jacobi
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) (W : G.Horizontal x)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval 0 τ)
    (V : G.Horizontal (P.square_path.curve s)) :
    M14JacobiResidual G P.square_path (initialValuePath_differentialData hM04 hM12 P W)
      s V = 0 := by
  let Q := initialValuePath_differentialData hM04 hM12 P W
  have hab : 0 < Real.sqrt τ := Real.sqrt_pos.mpr P.path.tau_lt
  have hC : M14SqrtParameterInterval 0 τ = Icc 0 (Real.sqrt τ) := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero]
  obtain ⟨A, hA, hAs⟩ := FiberBundle.exists_contMDiff_section_through
    (I := spacetimeModel n) (F := EuclideanSpace ℝ (Fin n)) V
  have hAE : Nonempty (M14PullbackExtension G P.square_path.curve
      (M14SqrtParameterInterval 0 τ) (fun r => A (P.square_path.curve r))) := by
    rw [hC]
    apply exists_pullbackExtension_Icc hab
    rw [← hC]
    exact hA.comp_contMDiffOn (P.square_path.smooth.mono P.square_path.interval_subset)
  obtain ⟨EA⟩ := hAE
  have hcont := (jacobiResidual_contDiffOn P.square_path Q EA hM04 hM12).continuousOn
  have hz : EqOn (fun r => M14JacobiResidual G P.square_path Q r (A (P.square_path.curve r)))
      (fun _ => 0) (Ioo 0 (Real.sqrt τ)) := fun _ hr =>
    initialValuePath_differential_jacobi_interior hM04 hM12 P W hr _
  have hclosed := hz.of_subset_closure hcont continuousOn_const
    (by rw [hC]; exact Ioo_subset_Icc_self)
    (by rw [hC, closure_Ioo hab.ne])
  simpa only [hAs] using hclosed hs

end PoincareConjecture.M14
