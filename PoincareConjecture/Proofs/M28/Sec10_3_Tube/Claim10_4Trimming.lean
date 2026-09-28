import PoincareConjecture.Proofs.M28.Sec10_3_Tube.ScalarTrimming











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28




theorem CounterexamplePathSegment.exists_level_eight_suffix
    (P : RicciFlowCurvatureTheory.{u}) {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    (S : CounterexamplePathSegment E) (hD₀ : 0 < D₀) (hD : 8 ≤ D) :
    let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
    let R := fun x : (E.flow.slice E.time).carrier => E.flow.scalar ⟨E.time, x⟩
    ∃ c : ℝ, S.level_parameter < c ∧ c < 1 ∧ R (S.path c) = 8 * Q ∧
      (∀ v ∈ Ioc c 1, 8 * Q < R (S.path v)) ∧
      MapsTo S.path (Icc c 1)
        (connectedComponentIn {x | 4 * Q < R x} (S.path c)) ∧
      (E.flow.metric E.time).pathELength S.path c 1 <
        ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) ∧
      ∀ x ∈ connectedComponentIn {x | 4 * Q < R x} (S.path c),
        Nonempty (GeneralizedCanonicalControl (F := E.flow) E.time x epsilon C) := by
  dsimp only
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  let R := fun x : (E.flow.slice E.time).carrier => E.flow.scalar ⟨E.time, x⟩
  have hQ : 0 < Q := lt_of_lt_of_le hD₀ E.base_lower
  have hscalar : ContinuousOn (R ∘ S.path) (Icc S.level_parameter 1) :=
    (E.flow.continuous_scalar_slice P E.time).comp_continuousOn
      S.path_smooth.continuous.continuousOn
  have hstart : R (S.path S.level_parameter) ≤ 8 * Q := by
    change E.flow.scalar ⟨E.time, S.path S.level_parameter⟩ ≤ 8 * Q
    rw [S.level_eq]
    change 4 * Q ≤ 8 * Q
    linarith only [hQ]
  have hend : 8 * Q < R (S.path 1) := by
    have hbound : 8 * Q ≤ D * Q := mul_le_mul_of_nonneg_right hD hQ.le
    exact hbound.trans_lt (by simpa only [R, Q, S.path_one] using E.scalar_large)
  obtain ⟨c, hc, hlevel, hafter⟩ :=
    exists_last_eq_of_continuousOn S.level_mem.2 hscalar hstart hend
  have hbefore : S.level_parameter < c := by
    rcases eq_or_lt_of_le hc.1 with heq | hlt
    · have hfour : R (S.path S.level_parameter) = 4 * Q := S.level_eq
      have hlevel' : R (S.path S.level_parameter) = 8 * Q := by
        simpa only [Function.comp_apply, ← heq] using hlevel
      linarith only [hfour, hlevel', hQ]
    · exact hlt
  have hlast : c < 1 := by
    by_contra h
    have hc1 : c = 1 := le_antisymm hc.2 (le_of_not_gt h)
    have hlevel' : R (S.path 1) = 8 * Q := by
      simpa only [Function.comp_apply, hc1] using hlevel
    exact (ne_of_lt hend) hlevel'.symm
  have hsuper : S.path '' Icc c 1 ⊆ {x | 4 * Q < R x} := by
    rintro x ⟨v, hv, rfl⟩
    change 4 * Q < R (S.path v)
    rcases eq_or_lt_of_le hv.1 with heq | hlt
    · have hlevel' : R (S.path v) = 8 * Q := by
        simpa only [Function.comp_apply, heq] using hlevel
      linarith only [hlevel', hQ]
    · exact (by linarith only [hQ] : 4 * Q < 8 * Q).trans (hafter v ⟨hlt, hv.2⟩)
  have hpre : IsPreconnected (S.path '' Icc c 1) :=
    isPreconnected_Icc.image S.path S.path_smooth.continuous.continuousOn
  have hcomponent : S.path '' Icc c 1 ⊆
      connectedComponentIn {x | 4 * Q < R x} (S.path c) :=
    hpre.subset_connectedComponentIn
      (mem_image_of_mem S.path (left_mem_Icc.mpr hc.2)) hsuper
  refine ⟨c, hbefore, hlast, hlevel, hafter, ?_, ?_, ?_⟩
  · intro v hv
    exact hcomponent (mem_image_of_mem S.path hv)
  · let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (E.flow.slice E.time).carrier → Type _) :=
      ⟨(E.flow.metric E.time).toRiemannianMetric⟩
    exact (Manifold.pathELength_mono hc.1 le_rfl).trans_lt S.suffix_length
  · intro x hx
    exact E.canonical x (connectedComponentIn_subset _ _ hx).le

end PoincareConjecture.M28
