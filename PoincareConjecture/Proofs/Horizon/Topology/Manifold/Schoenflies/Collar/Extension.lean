import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.Compact
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NormedAddCommGroup F] [NormedSpace Real F]
  {n : Nat} [Fact (Module.finrank Real E = n + 1)]

theorem exists_contDiff_extension_sphere
    (f : sphere (0 : E) 1 -> F)
    (hf : ContMDiff (𝓡 n) 𝓘(Real, F) ∞ f) :
    ∃ G : E -> F, ContDiff Real ∞ G ∧ ∀ p : sphere (0 : E) 1, G p = f p := by
  classical
  let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let radial : U -> sphere (0 : E) 1 := fun x =>
    ⟨‖x.val‖⁻¹ • x.val, by simp [norm_smul, norm_ne_zero_iff.mpr x.property]⟩
  have hn : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ (fun x : U => ‖x.val‖) := by
    intro x
    exact (contDiffAt_norm Real x.property).contMDiffAt.comp x (contMDiff_subtype_val x)
  have hr : ContMDiff 𝓘(Real, E) (𝓡 n) ∞ radial :=
    ((hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
      contMDiff_subtype_val).codRestrict_sphere _
  let g : E -> F := fun x => if hx : x = 0 then 0 else f (radial ⟨x, hx⟩)
  have hg : ContDiffOn Real ∞ g U := by
    intro x hx
    have hs : ContMDiff 𝓘(Real, E) 𝓘(Real, F) ∞ (fun y : U => g y.val) := by
      convert hf.comp hr using 1
      funext y
      exact dif_neg y.property
    exact (contMDiffAt_subtype_iff.mp (hs ⟨x, hx⟩)).contDiffAt.contDiffWithinAt
  have hSU : sphere (0 : E) 1 ⊆ U := fun x hx => ne_zero_of_mem_unit_sphere ⟨x, hx⟩
  obtain ⟨G, V, hG, _, hSV, _, heq⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact
      (isCompact_sphere 0 1) U.isOpen hSU g hg
  refine ⟨G, hG, ?_⟩
  intro p
  rw [heq (hSV p.property)]
  have hp : p.val ≠ 0 := ne_zero_of_mem_unit_sphere p
  simp [g, hp, radial]

end Poincare.Manifold.Schoenflies
