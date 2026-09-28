import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem m64_eq_local_inverse_of_injOn_closure
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {f : X → Y} {S : Set X} {x : X}
    (hf : ContinuousAt f x) (hinj : InjOn f S) (hx : x ∈ closure S)
    (F : OpenPartialHomeomorph X Y) (hF : EqOn F f F.source)
    (hsource : F.source ⊆ S) (htarget : f x ∈ F.target) :
    x = F.symm (f x) := by
  have : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hlim : Tendsto f (𝓝[S] x) (𝓝 (f x)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have htargetNear : ∀ᶠ y in 𝓝[S] x, f y ∈ F.target :=
    hlim.eventually (F.open_target.mem_nhds htarget)
  have heq : (fun y => F.symm (f y)) =ᶠ[𝓝[S] x] id := by
    filter_upwards [self_mem_nhdsWithin, htargetNear] with y hy hfy
    have hpre : F.symm (f y) ∈ F.source := F.map_target hfy
    exact hinj (hsource hpre) hy ((hF hpre).symm.trans (F.right_inv hfy))
  have hinverse : Tendsto (fun y => F.symm (f y)) (𝓝[S] x) (𝓝 (F.symm (f x))) :=
    (F.continuousAt_symm htarget).tendsto.comp hlim
  exact tendsto_nhds_unique (tendsto_id.mono_left nhdsWithin_le_nhds)
    (hinverse.congr' heq)

end PoincareConjecture
