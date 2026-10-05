import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform composition near a compact reference image

The varying coordinate jets in Morgan--Tian Claim 11.34, pp. 288-289,
need uniform estimates on compact sets. Ambient continuity at the compact
reference image suffices even when the varying images leave that image.
Reviewed derivation: `claim11_34-compact-ricci-jets.md`, section 1.
-/

set_option autoImplicit false

open Set Filter

namespace PoincareMT.M32

/-- Uniform convergence survives composition by a function continuous at
every point of the compact reference image. Source: the compact-uniform
comparison in Claim 11.34, pp. 288-289, and the task derivation. -/
theorem tendstoUniformlyOn_comp_of_isCompact_image
    {A B C I : Type*} [UniformSpace B] [UniformSpace C]
    {K : Set A} {l : Filter I} {f : A → B} {F : I → A → B} {g : B → C}
    (hK : IsCompact (f '' K)) (hg : ∀ y ∈ f '' K, ContinuousAt g y)
    (hF : TendstoUniformlyOn F f l K) :
    TendstoUniformlyOn (fun i x => g (F i x)) (fun x => g (f x)) l K := by
  intro r hr
  have hnear := hK.uniformContinuousAt_of_continuousAt g hg hr
  filter_upwards [hF _ hnear] with i hi x hx
  exact hi x hx (mem_image_of_mem f hx)

end PoincareMT.M32
