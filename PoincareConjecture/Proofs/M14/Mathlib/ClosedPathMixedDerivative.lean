import PoincareConjecture.Proofs.M14.Mathlib.ClosedPicardEquation










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M14

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {a b : ℝ}




theorem closedPath_eq_const_add_primitive (t₀ : Icc a b) (φ ψ : C(Icc a b, F))
    (hd : ∀ r : Icc a b, HasDerivWithinAt
      (fun s => φ (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (ψ r) (Icc a b) r.val) :
    φ = ContinuousMap.const _ (φ t₀) + closedPathPrimitive t₀ ψ := by
  let f : ℝ × F → F := fun z => ψ (projIcc a b (t₀.property.1.trans t₀.property.2) z.1)
  have hf : ContinuousOn f (Icc a b ×ˢ univ) :=
    (ψ.continuous.comp (continuous_projIcc.comp continuous_fst)).continuousOn
  have hpost : closedTimePostcomp f hf φ = ψ := by
    ext r
    change ψ (projIcc a b (t₀.property.1.trans t₀.property.2) r.val) = ψ r
    rw [projIcc_of_mem (t₀.property.1.trans t₀.property.2) r.property]
  have h := closedPath_picard_equation_of_ode t₀ f hf φ (fun r => by
    dsimp only [f]
    rw [projIcc_of_mem (t₀.property.1.trans t₀.property.2) r.property]
    exact hd r)
  rwa [hpost] at h



theorem closedPath_hasDerivWithinAt_of_primitive (t₀ : Icc a b)
    (φ ψ : C(Icc a b, F)) (c : F)
    (heq : φ = ContinuousMap.const _ c + closedPathPrimitive t₀ ψ) (r : Icc a b) :
    HasDerivWithinAt
      (fun s => φ (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (ψ r) (Icc a b) r.val := by
  have h := (hasDerivWithinAt_const r.val (Icc a b) c).add
    (closedPathPrimitive_hasDerivWithinAt t₀ r ψ)
  rw [zero_add] at h
  apply h.congr_of_mem _ r.property
  intro s _
  exact congrArg (fun v : C(Icc a b, F) =>
    v (projIcc a b (t₀.property.1.trans t₀.property.2) s)) heq




theorem closedPath_parameter_time_derivative (t₀ : Icc a b) {U : Set P} (hU : IsOpen U)
    (Φ Ψ : P → C(Icc a b, F)) (hΦ : DifferentiableOn ℝ Φ U)
    (hΨ : DifferentiableOn ℝ Ψ U)
    (ht : ∀ x ∈ U, ∀ r : Icc a b, HasDerivWithinAt
      (fun s => Φ x (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (Ψ x r) (Icc a b) r.val) {x : P} (hx : x ∈ U) (v : P) (r : Icc a b) :
    HasDerivWithinAt
      (fun s => fderiv ℝ Φ x v (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (fderiv ℝ Ψ x v r) (Icc a b) r.val := by
  let C₀ : F →L[ℝ] C(Icc a b, F) := ContinuousLinearMap.const ℝ (Icc a b)
  let ev : C(Icc a b, F) →L[ℝ] F := ContinuousMap.evalCLM ℝ t₀
  let L := closedPathPrimitive (E := F) t₀
  have hdΦ := ((hΦ x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hdΨ := ((hΨ x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have heq : ∀ᶠ y in 𝓝 x, Φ y = C₀ (ev (Φ y)) + L (Ψ y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact closedPath_eq_const_add_primitive t₀ (Φ y) (Ψ y) (ht y hy)
  have hd := ((C₀.hasFDerivAt.comp x (ev.hasFDerivAt.comp x hdΦ)).add
    (L.hasFDerivAt.comp x hdΨ)).congr_of_eventuallyEq heq
  have hpath : fderiv ℝ Φ x v = ContinuousMap.const _ (fderiv ℝ Φ x v t₀) +
      closedPathPrimitive t₀ (fderiv ℝ Ψ x v) :=
    congrArg (fun A : P →L[ℝ] C(Icc a b, F) => A v) (hdΦ.unique hd)
  exact closedPath_hasDerivWithinAt_of_primitive t₀ _ _ _ hpath r

end PoincareConjecture.M14
