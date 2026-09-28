import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace Poincare

theorem eventually_injOn_of_locally_injective_total_map
    {P E X : Type*} [TopologicalSpace P] [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X] {f : P → E → X} {p : P} {K : Set E}
    (hK : IsCompact K) (hinj : InjOn (f p) K)
    (hcont : ∀ v ∈ K, ContinuousAt (fun z : P × E => f z.1 z.2) (p, v))
    (hlocal : ∀ v ∈ K, ∃ U ∈ 𝓝 (p, v),
      InjOn (fun z : P × E => (z.1, f z.1 z.2)) U) :
    ∀ᶠ q in 𝓝 p, InjOn (f q) K := by
  have hpair : ∀ z ∈ K ×ˢ K,
      ∀ᶠ t : P × (E × E) in 𝓝 (p, z),
        f t.1 t.2.1 = f t.1 t.2.2 → t.2.1 = t.2.2 := by
    rintro ⟨v, w⟩ ⟨hv, hw⟩
    have hleft : ContinuousAt (fun t : P × (E × E) => (t.1, t.2.1)) (p, v, w) :=
      continuous_fst.continuousAt.prodMk continuous_snd.fst.continuousAt
    have hright : ContinuousAt (fun t : P × (E × E) => (t.1, t.2.2)) (p, v, w) :=
      continuous_fst.continuousAt.prodMk continuous_snd.snd.continuousAt
    by_cases h : v = w
    · subst w
      obtain ⟨U, hU, hUi⟩ := hlocal v hv
      filter_upwards [hleft.preimage_mem_nhds hU, hright.preimage_mem_nhds hU]
        with t ht₁ ht₂
      intro heq
      exact congrArg Prod.snd (hUi ht₁ ht₂ (Prod.ext rfl heq))
    · have hne : f p v ≠ f p w := fun heq => h (hinj hv hw heq)
      have hcont₁ : ContinuousAt (fun t : P × (E × E) => f t.1 t.2.1) (p, v, w) :=
        (hcont v hv).comp_of_eq hleft rfl
      have hcont₂ : ContinuousAt (fun t : P × (E × E) => f t.1 t.2.2) (p, v, w) :=
        (hcont w hw).comp_of_eq hright rfl
      have hnear := (hcont₁.ne_iff_eventually_ne hcont₂).mp hne
      filter_upwards [hnear] with t ht
      exact fun heq => False.elim (ht heq)
  filter_upwards [(hK.prod hK).eventually_forall_of_forall_eventually
    (P := fun q z => f q z.1 = f q z.2 → z.1 = z.2) hpair] with q hq
  exact fun v hv w hw heq => hq (v, w) ⟨hv, hw⟩ heq

end Poincare
