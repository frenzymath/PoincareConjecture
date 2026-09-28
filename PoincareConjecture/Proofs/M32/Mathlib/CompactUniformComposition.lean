import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

open Set Filter

namespace PoincareConjecture.M32

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

end PoincareConjecture.M32
