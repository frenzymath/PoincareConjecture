import PoincareConjecture.Proofs.M47.LimitFiniteOriginalSourceJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem limitFinite_compact_chart_cover
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (U : TopologicalSpace.Opens M) {K : Set M} (hK : IsCompact K) (hne : K.Nonempty)
    (P : K → ℝ → ℝ → PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞ → Prop)
    (hcharts : ∀ q : K, ∃ R ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧
      ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
        Φ.source = Metric.ball 0 R ∧ (Φ 0).val = q.val ∧ P q R ρ Φ) :
    ∃ N : ℕ, ∃ q : Fin (N + 1) → K, ∃ R ρ : Fin (N + 1) → ℝ,
      ∃ Φ : Fin (N + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
        (∀ i, 0 < ρ i ∧ 2 * ρ i < R i ∧
          (Φ i).source = Metric.ball 0 (R i) ∧ (Φ i 0).val = (q i).val ∧
            P (q i) (R i) (ρ i) (Φ i)) ∧
        K ⊆ ⋃ i, (fun z : E => (Φ i z).val) '' Metric.ball 0 (ρ i) := by
  classical
  choose R ρ hρ hρR Φ hsource hzero hP using hcharts
  let image := fun q : K => (fun z : E => (Φ q z).val) '' Metric.ball 0 (ρ q)
  have hopen (q : K) : IsOpen (image q) := by
    have hsubset : Metric.ball (0 : E) (ρ q) ⊆ (Φ q).source := by
      rw [hsource q]
      exact Metric.ball_subset_ball (by linarith [hρ q, hρR q])
    have h := U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
      ((Φ q).toOpenPartialHomeomorph.isOpen_image_of_subset_source
        Metric.isOpen_ball hsubset)
    change IsOpen (Subtype.val '' ((Φ q) '' Metric.ball 0 (ρ q))) at h
    simpa only [image, image_image, Function.comp_def] using h
  have hpoint (q : K) : q.val ∈ image q :=
    ⟨0, Metric.mem_ball_self (hρ q), hzero q⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover image hopen (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpoint ⟨x, hx⟩⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hqs, _⟩ := mem_iUnion.mp hq
    exact ⟨q, hqs⟩
  obtain ⟨q0, hq0⟩ := hsne
  let label : Fin (Fintype.card s + 1) → s :=
    Fin.cases ⟨q0, hq0⟩ (Fintype.equivFin s).symm
  have hlabel : Function.Surjective label := by
    intro q
    refine ⟨(Fintype.equivFin s q).succ, ?_⟩
    exact (Fintype.equivFin s).symm_apply_apply q
  refine ⟨Fintype.card s, fun i => (label i).val, fun i => R (label i).val,
    fun i => ρ (label i).val, fun i => Φ (label i).val, ?_, ?_⟩
  · intro i
    exact ⟨hρ _, hρR _, hsource _, hzero _, hP _⟩
  · intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hqs, hxq⟩ := mem_iUnion.mp hq
    obtain ⟨i, hi⟩ := hlabel ⟨q, hqs⟩
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change x ∈ image (label i).val
    rw [hi]
    exact hxq

end PoincareConjecture.M47
