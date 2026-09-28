import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetChart
import PoincareConjecture.Proofs.M14.Mathlib.TrivializationConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Opens E)

theorem tangentBundle_snd_contMDiff :
    ContMDiff (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)) ∞
      (fun v : TangentBundle (𝓘(ℝ, E)) U => (show E from v.2)) := by
  have hi : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (Subtype.val : U → E) :=
    contMDiff_subtype_val
  have h := (contMDiff_snd_tangentBundle_modelSpace E (𝓘(ℝ, E)) (n := ∞)).comp
    (hi.contMDiff_tangentMap (m := ∞) (by simp))
  convert h using 1
  funext v
  dsimp only [Function.comp_def, tangentMap]
  rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val]
  rfl

theorem tangent_trivialization_apply (x y : U) (v : TangentSpace (𝓘(ℝ, E)) y) :
    (trivializationAt E (TangentSpace (𝓘(ℝ, E)) : U → Type _) x).continuousLinearMapAt
      ℝ y v = (show E from v) := by
  have hy : y ∈ (chartAt E x).source := by
    rw [U.chartAt_source_eq_univ]
    exact mem_univ y
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy]
  change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (Subtype.val : U → E) y v = v
  rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val]
  rfl

theorem tangent_trivialization_symmL_apply (x y : U) (v : E) :
    (trivializationAt E (TangentSpace (𝓘(ℝ, E)) : U → Type _) x).symmL ℝ y v = v := by
  let e := trivializationAt E (TangentSpace (𝓘(ℝ, E)) : U → Type _) x
  have hy : y ∈ e.baseSet := by
    change y ∈ (chartAt E x).source
    rw [U.chartAt_source_eq_univ]
    exact mem_univ y
  have h := e.symmL_continuousLinearMapAt (R := ℝ) hy
    (show TangentSpace (𝓘(ℝ, E)) y from v)
  rw [U.tangent_trivialization_apply] at h
  exact h

theorem contMDiff_constant_tangentField (v : E) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun y : U => TotalSpace.mk' E
        (E := (TangentSpace (𝓘(ℝ, E)) : U → Type _)) y v) := by
  intro x
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_id, ?_⟩
  convert (contMDiffAt_const (c := v) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun _ : U => v) x) using 1
  funext y
  have hy : y ∈ (trivializationAt E (TangentSpace (𝓘(ℝ, E)) : U → Type _) x).baseSet := by
    change y ∈ (chartAt E x).source
    rw [U.chartAt_source_eq_univ]
    exact mem_univ y
  let e := trivializationAt E (TangentSpace (𝓘(ℝ, E)) : U → Type _) x
  exact (e.continuousLinearMapAt_apply_of_mem ℝ hy v).symm.trans
    (U.tangent_trivialization_apply x y v)

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] {L : ModelWithCorners ℝ EP HP}
  [TopologicalSpace P] [ChartedSpace HP P]

theorem tangentField_contMDiffWithinAt {k : ℕ∞ω}
    {b : P → U} {v : P → E} {S : Set P} {z : P}
    (hb : ContMDiffWithinAt L (𝓘(ℝ, E)) k b S z)
    (hv : ContMDiffWithinAt L (𝓘(ℝ, E)) k v S z) :
    ContMDiffWithinAt L (𝓘(ℝ, E)).tangent k
      (fun a => TotalSpace.mk' E (E := (TangentSpace (𝓘(ℝ, E)) : U → Type _))
        (b a) (v a)) S z := by
  apply Bundle.contMDiffWithinAt_totalSpace.mpr
  refine ⟨hb, ?_⟩
  convert hv using 1
  funext a
  let e := trivializationAt E (TangentSpace (𝓘(ℝ, E)) : U → Type _) (b z)
  have ha : b a ∈ e.baseSet := by
    change b a ∈ (chartAt E (b z)).source
    rw [U.chartAt_source_eq_univ]
    exact mem_univ _
  exact (e.continuousLinearMapAt_apply_of_mem ℝ ha (v a)).symm.trans
    (U.tangent_trivialization_apply (b z) (b a) (v a))

variable [FiniteDimensional ℝ E]

theorem covariantDerivative_eq_derivative_add_constant
    {D : (∀ x : U, TangentSpace (𝓘(ℝ, E)) x) →
      ∀ x : U, TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x}
    (hD : IsCovariantDerivativeOn E D univ)
    {V : ∀ x : U, TangentSpace (𝓘(ℝ, E)) x} {x : U}
    (hV : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent (T% V) x)
    (v : TangentSpace (𝓘(ℝ, E)) x) :
    (show E from D V x v) =
      mvfderiv (𝓘(ℝ, E)) (fun y : U => (show E from V y)) x v +
        (show E from D (fun _ : U => (show E from V x)) x v) := by
  let e := trivializationAt E (TangentSpace (𝓘(ℝ, E)) : U → Type _) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hinv (w : E) : e.symmL ℝ x w = w := by
    have h := e.symmL_continuousLinearMapAt (R := ℝ) hx
      (show TangentSpace (𝓘(ℝ, E)) x from w)
    rw [U.tangent_trivialization_apply] at h
    exact h
  dsimp only [e] at hinv
  have hconst := (U.contMDiff_constant_tangentField (V x) x).mdifferentiableAt (by simp)
  have h₁ := e.covariantDerivative_eq_flat_add_difference
    (hD.mono (subset_univ e.baseSet)) hx hV v
  have h₂ := e.covariantDerivative_eq_flat_add_difference
    (hD.mono (subset_univ e.baseSet)) hx hconst v
  simp only [e, tangent_trivialization_apply] at h₁ h₂
  simp only [mvfderiv_const, zero_apply, hinv, zero_add] at h₁ h₂
  rw [h₁, h₂]

end TopologicalSpace.Opens
