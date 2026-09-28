import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Topology

theorem tendstoUniformlyOn_prod_of_moving_points
    {ι X Y Z : Type*} [PseudoMetricSpace Z]
    {l : Filter ι} {K : Set X} {S : Set Y}
    {f : ι → X × Y → Z} {g : Y → Z}
    (h : ∀ q : ι → X, (∀ i, q i ∈ K) →
      TendstoUniformlyOn (fun i y => f i (q i, y)) g l S) :
    TendstoUniformlyOn f (fun z => g z.2) l (K ×ˢ S) := by
  classical
  rcases K.eq_empty_or_nonempty with hK | ⟨x₀, hx₀⟩
  · simpa only [hK, empty_prod] using
      (tendstoUniformlyOn_empty :
        TendstoUniformlyOn f (fun z => g z.2) l ∅)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let bad (i : ι) (x : K) := ∃ y ∈ S, ¬ dist (g y) (f i (x, y)) < ε
  let q : ι → K := fun i =>
    if hb : ∃ x : K, bad i x then hb.choose else ⟨x₀, hx₀⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (h (fun i => q i) (fun i => (q i).property)) ε hε] with i hi
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  by_contra hbad
  have hex : ∃ x : K, bad i x := ⟨⟨x, hx⟩, y, hy, hbad⟩
  have hbq : bad i (q i) := by
    dsimp only [q]
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨z, hz, hfail⟩ := hbq
  exact hfail (hi z hz)

theorem tendstoUniformlyOn_prod_of_isCompact_of_local
    {ι X Y Z : Type*} [TopologicalSpace X] [PseudoMetricSpace Z]
    {l : Filter ι} {K : Set X} {S : Set Y}
    {f : ι → X × Y → Z} {g : Y → Z}
    (hK : IsCompact K)
    (hlocal : ∀ p ∈ K, ∃ U, IsOpen U ∧ p ∈ U ∧
      TendstoUniformlyOn f (fun z => g z.2) l ((K ∩ U) ×ˢ S)) :
    TendstoUniformlyOn f (fun z => g z.2) l (K ×ˢ S) := by
  apply hK.induction_on
    (p := fun T => TendstoUniformlyOn f (fun z => g z.2) l (T ×ˢ S))
  · simpa only [empty_prod] using
      (tendstoUniformlyOn_empty :
        TendstoUniformlyOn f (fun z => g z.2) l ∅)
  · intro A B hAB hB
    exact hB.mono (fun _ hz => ⟨hAB hz.1, hz.2⟩)
  · intro A B hA hB
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hA ε hε,
      Metric.tendstoUniformlyOn_iff.mp hB ε hε] with i hiA hiB
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact hx.elim (fun h => hiA (x, y) ⟨h, hy⟩) (fun h => hiB (x, y) ⟨h, hy⟩)
  · intro p hp
    obtain ⟨U, hU, hpU, hconv⟩ := hlocal p hp
    exact ⟨K ∩ U, inter_mem_nhdsWithin K (hU.mem_nhds hpU), hconv⟩

theorem tendstoUniformlyOn_prod_of_isCompact_of_locally_moving_points
    {ι X Y Z : Type*} [TopologicalSpace X] [PseudoMetricSpace Z]
    {l : Filter ι} {K : Set X} {S : Set Y}
    {f : ι → X × Y → Z} {g : Y → Z}
    (hK : IsCompact K)
    (hlocal : ∀ p ∈ K, ∃ U, IsOpen U ∧ p ∈ U ∧
      ∀ q : ι → X, (∀ i, q i ∈ K ∩ U) →
        TendstoUniformlyOn (fun i y => f i (q i, y)) g l S) :
    TendstoUniformlyOn f (fun z => g z.2) l (K ×ˢ S) := by
  apply tendstoUniformlyOn_prod_of_isCompact_of_local hK
  intro p hp
  obtain ⟨U, hU, hpU, hconv⟩ := hlocal p hp
  exact ⟨U, hU, hpU, tendstoUniformlyOn_prod_of_moving_points hconv⟩

end Poincare.Topology
