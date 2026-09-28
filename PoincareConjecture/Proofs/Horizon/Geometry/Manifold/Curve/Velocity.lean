import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff

universe u

namespace Poincare.Manifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem contMDiffOn_velocity_lift {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I) :
    ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun u => (⟨γ u, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u (1 : ℝ)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)))) I := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro u
    apply contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
        (n := ∞) (x := u) (c := (1 : ℝ)))
  have h := (hγ.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    hI.uniqueMDiffOn).comp hunit.contMDiffOn (fun u hu => hu)
  apply h.congr
  intro u hu
  simp only [Function.comp_def, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hI.mem_nhds hu)]

end Poincare.Manifold
