import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceSeparation

set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.ChartDistance

theorem eventually_source_extension_eq_iff
    {Q Y : Type*} [MetricSpace Q] [TopologicalSpace Y]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {q : Y → Q} (hq : Continuous q)
    {A A' V : Set Q} {C : Set Y}
    (hA : IsCompact A) (hC : IsCompact C)
    (hAA' : A ⊆ interior A') (hA'V : A' ⊆ V)
    {F : ∀ k, Q → M k} {g : ∀ k, Y → M k}
    (hinj : ∀ᶠ k in atTop, InjOn (F k) V)
    (hconv : TendstoUniformlyOn
      (fun k (z : Q × Y) => dist (F k z.1) (g k z.2))
      (fun z => dist z.1 (q z.2)) atTop (A ×ˢ C))
    (hagree : ∀ᶠ k in atTop, ∀ y ∈ C, q y ∈ A' → g k y = F k (q y)) :
    ∀ᶠ k in atTop, ∀ p ∈ A, ∀ y ∈ C, F k p = g k y ↔ p = q y := by
  have hzero : ∀ z ∈ A ×ˢ C, dist z.1 (q z.2) = 0 →
      z ∈ (univ : Set Q) ×ˢ (q ⁻¹' interior A') := by
    intro z hz heq
    refine ⟨mem_univ _, ?_⟩
    change q z.2 ∈ interior A'
    exact (dist_eq_zero.mp heq) ▸ hAA' hz.1
  have hcollision := eventually_zero_mem_open_of_uniform_limit (hA.prod hC)
    (isOpen_univ.prod (isOpen_interior.preimage hq))
    (continuous_fst.dist (hq.comp continuous_snd)).continuousOn hconv hzero
  filter_upwards [hcollision, hinj, hagree] with k hk hi ha p hp y hy
  constructor
  · intro heq
    have hyA' : q y ∈ A' := interior_subset
      (hk (p, y) ⟨hp, hy⟩ (by simp only [heq, dist_self])).2
    exact hi (hA'V (interior_subset (hAA' hp))) (hA'V hyA')
      (heq.trans (ha y hy hyA'))
  · intro heq
    subst p
    exact (ha y hy (interior_subset (hAA' hp))).symm

end PoincareConjecture.ChartDistance
