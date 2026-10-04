import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!+# Smooth real partial derivatives with manifold parameters

Specializing the parameter-dependent manifold derivative to the real line
removes both tangent-coordinate changes. This is the regularity input in
the coherent-axial-orientation derivation for Morgan--Tian A.11(3), p. 503.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  {F : X × ℝ → ℝ} {z : X × ℝ}

/-- A smooth function of a manifold parameter and a real variable has
a smooth derivative in the real variable. This is the local regularity
step in the coherent orientation argument for MT A.11(3), p. 503. -/
theorem ContMDiffAt.real_partial_deriv_snd
    (hF : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F z) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : X × ℝ => deriv (fun r => F (p.1, r)) p.2) z := by
  let f : (X × ℝ) → ℝ → ℝ := fun p r => F (p.1, r)
  have hf : ContMDiffAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) (z, z.2) :=
    hF.comp (z, z.2) (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
  have hd := ContMDiffAt.mfderiv_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (m := ∞) f Prod.snd id (fun _ : X × ℝ => (1 : ℝ)) hf contMDiffAt_snd
      contMDiffAt_id contMDiffAt_const (by simp)
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv,
    fderiv_apply_one_eq_deriv, id_eq, f] using hd
