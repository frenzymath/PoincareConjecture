import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.ProjectedDoubleLocus
import Mathlib.Topology.MetricSpace.Thickening












set_option autoImplicit false

open Set Geometry Topology Metric
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}




theorem Step.exists_protected_boundary_projection (step : Step s t)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space ↦ j x))
    (Q : Set V) (hQ : IsCompact Q) (hQK : Q ⊆ K.space) (R : Set M)
    (hproper : ∀ x ∈ K.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Q)
    (hrim : InjOn (t.projection ∘ j) Q) :
    let p := (step.projection ∘ step.inclusion) ∘ j
    ∃ (D : SimplicialComplex ℝ V) (O : Set s.Carrier) (ε : ℝ),
      D.faces.Finite ∧ D.space = doubleLocusOn p K.space ∧
      IsCompact D.space ∧ D.space ⊆ K.space ∧ Disjoint D.space Q ∧
      IsOpen O ∧ p '' Q ⊆ O ∧ 0 < ε ∧ cthickening ε Q ⊆ D.spaceᶜ ∧
      K.space ∩ p ⁻¹' O = K.space \ D.space ∧
      InjOn p (K.space \ D.space) ∧
      (∀ x ∈ K.space, x ∈ cthickening ε Q →
        ∀ y ∈ K.space, p x = p y → x = y) := by
  dsimp only
  let p := (step.projection ∘ step.inclusion) ∘ j
  obtain ⟨hp, _, L, D, _, hD, _, _, hDs, hDc, hDK⟩ :=
    step.exists_finite_source_double_locus K hK hj hji
  have hfront (x : V) (hx : x ∈ K.space) :
      p x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Q := by
    rw [step.frontier_preimage R] at hproper
    exact hproper x hx
  have hdis : Disjoint D.space Q := by
    apply disjoint_left.mpr
    intro x hx hxQ
    obtain ⟨hxK, y, hyK, hxy, hne⟩ := hDs.subset hx
    change p x = p y at hxy
    have hyQ : y ∈ Q := (hfront y hyK).mp (hxy ▸ (hfront x hxK).mpr hxQ)
    apply hne
    apply hrim hxQ hyQ
    change t.projection (j x) = t.projection (j y)
    rw [step.original_eq, step.original_eq]
    exact congrArg s.projection hxy
  have hsingle {x y : V} (hx : x ∈ K.space) (hn : x ∉ D.space)
      (hy : y ∈ K.space) (heq : p x = p y) : x = y := by
    by_contra hne
    exact hn (hDs.symm.subset ⟨hx, y, hy, heq, hne⟩)
  let O : Set s.Carrier := (p '' D.space)ᶜ
  have hO : IsOpen O :=
    (hDc.image_of_continuousOn (hp.continuousOn.mono hDK)).isClosed.isOpen_compl
  have hpre : K.space ∩ p ⁻¹' O = K.space \ D.space := by
    ext x
    constructor
    · rintro ⟨hx, hpO⟩
      exact ⟨hx, fun hxD ↦ hpO ⟨x, hxD, rfl⟩⟩
    · rintro ⟨hx, hn⟩
      refine ⟨hx, ?_⟩
      rintro ⟨y, hyD, hyx⟩
      exact hn ((hsingle hx hn (hDK hyD) hyx.symm).symm ▸ hyD)
  have hQO : p '' Q ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hpre.symm.subset ⟨hQK hx, fun hxD ↦ disjoint_left.mp hdis hxD hx⟩).2
  obtain ⟨ε, hε, hεQ⟩ := hQ.exists_cthickening_subset_open
    hDc.isClosed.isOpen_compl (fun _ hx hxD ↦ disjoint_left.mp hdis hxD hx)
  refine ⟨D, O, ε, hD, hDs, hDc, hDK, hdis, hO, hQO, hε, hεQ, hpre, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hsingle hx.1 hx.2 hy.1 hxy
  · intro x hx hxε y hy hxy
    exact hsingle hx (hεQ hxε) hy hxy

end Geometry.OriginalPLTower
