import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeDifferentialLocal
import PoincareConjecture.Proofs.M14.Sec6_7_CompactSurvival










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}





theorem compact_initial_smallTime_differential_bijective
    (E : M14ExponentialFamily G T x) {B : Set (G.Horizontal x)} (hB : IsCompact B)
    {δ : ℝ} (hδ : 0 < δ) (hwindow : Icc (T - δ) T ⊆ I.domain) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ δ ∧
      ∀ Z ∈ B, ∀ τ ∈ Ioc 0 τ₀,
        ∃ hs : (Z, Real.sqrt τ) ∈ E.domain,
          Function.Bijective (E.differential Z (Real.sqrt τ) hs) := by
  obtain ⟨τS, hτS, _, hsurv⟩ := compact_initial_survival_and_capture E hB
    (K := univ) ⟨univ, isOpen_univ, mem_univ _, Subset.rfl⟩ hδ hwindow
  let A : Set (G.Horizontal x × ℝ) := {z | z.2 ≤ 0 ∨
    ∃ hs : z ∈ E.domain, Function.Bijective (E.differential z.1 z.2 hs)}
  let O := interior A
  have hBO : B ×ˢ {(0 : ℝ)} ⊆ O := by
    rintro ⟨Z, s⟩ ⟨hZ, hs⟩
    rcases mem_singleton_iff.mp hs with rfl
    have hZS := (hsurv Z hZ τS ⟨hτS.le, le_rfl⟩).1
    obtain ⟨V, hV, hZV, d, hd, _, hgood⟩ :=
      exists_open_smallTime_differential_bijective E (Real.sqrt_pos.mpr hτS) hZS
    have hrect : V ×ˢ Iio d ⊆ A := by
      intro z hz
      by_cases hnon : z.2 ≤ 0
      · exact Or.inl hnon
      · exact Or.inr (hgood z.1 hz.1 z.2 ⟨lt_of_not_ge hnon, hz.2.le⟩)
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset ((hV.prod isOpen_Iio).mem_nhds ⟨hZV, hd⟩) hrect
  obtain ⟨V, W, _, hW, hBV, hzeroW, hVW⟩ :=
    generalized_tube_lemma hB isCompact_singleton isOpen_interior hBO
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp
    (hW.mem_nhds (hzeroW (mem_singleton 0)))
  let τ₀ := min δ ((ε / 2) ^ 2)
  have hτ₀ : 0 < τ₀ := lt_min hδ (sq_pos_of_pos (half_pos hε))
  refine ⟨τ₀, hτ₀, min_le_left _ _, ?_⟩
  intro Z hZ τ hτ
  have hsqrt : Real.sqrt τ ≤ ε / 2 :=
    Real.sqrt_le_iff.mpr ⟨(half_pos hε).le, hτ.2.trans (min_le_right _ _)⟩
  have hball : Real.sqrt τ ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt.trans_lt (half_lt_self hε)
  have hO : (Z, Real.sqrt τ) ∈ O := hVW ⟨hBV hZ, hεW hball⟩
  exact (interior_subset hO).resolve_left (not_le_of_gt (Real.sqrt_pos.mpr hτ.1))

end PoincareConjecture.M14
