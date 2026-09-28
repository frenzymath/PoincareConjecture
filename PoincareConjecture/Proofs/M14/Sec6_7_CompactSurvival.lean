import PoincareConjecture.Definitions.M14Exponential
import Mathlib.Topology.Compactness.Compact











set_option autoImplicit false

open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem zero_mem_interior_survival_image (E : M14ExponentialFamily G T x)
    {O : Set G.Point} (hO : IsOpen O) (hx : x ∈ O) (Z : G.Horizontal x) :
    (Z, 0) ∈ interior ((M14AdmissibleParameter G T x)ᶜ ∪
      (E.domain ∩ {z | E.gamma z.1 z.2 ∈ O})) := by
  obtain ⟨U, hU, hZU, hUD⟩ := E.domain_relative_open (Z, 0) (E.domain_zero Z)
  have hD : E.domain ∈ 𝓝[M14AdmissibleParameter G T x] (Z, 0) :=
    mem_nhdsWithin.mpr ⟨U, hU, hZU, hUD⟩
  have hγ := (E.joint_continuous (Z, 0) (E.domain_zero Z)).mono_of_mem_nhdsWithin hD
  have hO' : O ∈ 𝓝 (E.gamma Z 0) := by
    rw [E.gamma_at_zero]
    exact hO.mem_nhds hx
  have hS := Filter.inter_mem hD (hγ.preimage_mem_nhdsWithin hO')
  obtain ⟨V, hV, hVS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hS
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset hV
  intro z hz
  by_cases ha : z ∈ M14AdmissibleParameter G T x
  · exact Or.inr (hVS ⟨hz, ha⟩)
  · exact Or.inl ha





theorem compact_initial_survival_and_capture (E : M14ExponentialFamily G T x)
    {B : Set (G.Horizontal x)} (hB : IsCompact B) {K : Set G.Point}
    (hK : ∃ O : Set G.Point, IsOpen O ∧ x ∈ O ∧ O ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hwindow : Set.Icc (T - δ) T ⊆ I.domain) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ δ ∧
      ∀ Z ∈ B, ∀ τ ∈ Set.Icc 0 τ₀,
        (Z, Real.sqrt τ) ∈ E.domain ∧ E.gamma Z (Real.sqrt τ) ∈ K := by
  obtain ⟨O, hO, hxO, hOK⟩ := hK
  let U := interior ((M14AdmissibleParameter G T x)ᶜ ∪
    (E.domain ∩ {z | E.gamma z.1 z.2 ∈ O}))
  have hBU : B ×ˢ {(0 : ℝ)} ⊆ U := by
    rintro ⟨Z, s⟩ ⟨_, hs⟩
    rcases Set.mem_singleton_iff.mp hs with rfl
    exact zero_mem_interior_survival_image E hO hxO Z
  obtain ⟨V, W, _, hW, hBV, hzeroW, hVW⟩ :=
    generalized_tube_lemma hB isCompact_singleton isOpen_interior hBU
  have hW0 : W ∈ 𝓝 (0 : ℝ) := hW.mem_nhds (hzeroW (Set.mem_singleton 0))
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW0
  let τ₀ := min δ ((ε / 2) ^ 2)
  have hτ₀ : 0 < τ₀ := lt_min hδ (sq_pos_of_pos (half_pos hε))
  refine ⟨τ₀, hτ₀, min_le_left _ _, ?_⟩
  intro Z hZ τ hτ
  have hτδ : τ ≤ δ := hτ.2.trans (min_le_left _ _)
  have hsqrt : Real.sqrt τ ≤ ε / 2 :=
    Real.sqrt_le_iff.mpr ⟨(half_pos hε).le, hτ.2.trans (min_le_right _ _)⟩
  have hball : Real.sqrt τ ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt.trans_lt (half_lt_self hε)
  have hU : (Z, Real.sqrt τ) ∈ U := hVW ⟨hBV hZ, hεW hball⟩
  have hA : (Z, Real.sqrt τ) ∈ M14AdmissibleParameter G T x := by
    refine ⟨Real.sqrt_nonneg _, hwindow ?_⟩
    rw [Real.sq_sqrt hτ.1]
    exact ⟨sub_le_sub_left hτδ T, sub_le_self T hτ.1⟩
  have hgood : (Z, Real.sqrt τ) ∈ E.domain ∩ {z | E.gamma z.1 z.2 ∈ O} :=
    (interior_subset hU).resolve_left (fun hnot => hnot hA)
  exact ⟨hgood.1, hOK hgood.2⟩

end PoincareConjecture.M14
