import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace.Real










set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M25.Topology3D



theorem exists_injective_product_neighborhood
    {X P Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace P]
    [TopologicalSpace Y] [T2Space Y] (f : X × P → Y) (p : P)
    (hi : Function.Injective (fun x => f (x, p)))
    (hc : ∀ x, ContinuousAt f (x, p))
    (hl : ∀ x, ∃ U ∈ 𝓝 (x, p), InjOn f U) :
    ∃ V : Set P, IsOpen V ∧ p ∈ V ∧ InjOn f (univ ×ˢ V) := by
  have hslice : InjOn f (univ ×ˢ ({p} : Set P)) := by
    rintro ⟨x, t⟩ ⟨_, rfl⟩ ⟨y, s⟩ ⟨_, rfl⟩ h
    exact Prod.ext (hi h) rfl
  obtain ⟨W, hW, hsliceW, hinjW⟩ := hslice.exists_isOpen_superset
    (isCompact_univ.prod isCompact_singleton)
    (by rintro ⟨x, t⟩ ⟨_, rfl⟩; exact hc x)
    (by rintro ⟨x, t⟩ ⟨_, rfl⟩; exact hl x)
  obtain ⟨A, B, _, hB, hA, hp, hAB⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hW hsliceW
  exact ⟨B, hB, hp (mem_singleton p),
    hinjW.mono (fun q hq => hAB ⟨hA hq.1, hq.2⟩)⟩



theorem exists_injective_uniform_tube
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] (f : X × ℝ → Y)
    (hi : Function.Injective (fun x => f (x, 0)))
    (hc : ∀ x, ContinuousAt f (x, 0))
    (hl : ∀ x, ∃ U ∈ 𝓝 (x, (0 : ℝ)), InjOn f U) :
    ∃ d > (0 : ℝ), InjOn f (univ ×ˢ Ioo (-d) d) := by
  obtain ⟨B, hB, hzero, hinj⟩ := exists_injective_product_neighborhood f 0 hi hc hl
  obtain ⟨d, hd, hball⟩ :=
    Metric.mem_nhds_iff.mp (hB.mem_nhds hzero)
  have hIB : Ioo (-d) d ⊆ B := by
    intro t ht
    apply hball
    change dist t 0 < d
    rw [Real.dist_eq, sub_zero]
    exact abs_lt.mpr ht
  refine ⟨d, hd, hinj.mono ?_⟩
  intro p hp
  exact ⟨hp.1, hIB hp.2⟩

end PoincareConjecture.M25.Topology3D
