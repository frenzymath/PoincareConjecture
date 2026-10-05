import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.Compactness
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Scalar levels in proper terminal horns

Morgan--Tian Theorem 11.31, printed pp. 291--292, and Corollary 11.36,
printed p. 292, use properness to reach prescribed high scalar levels.
Compact terminal scalar sublevels and proper horn coordinates give uniform
scalar growth on full tails. Continuity then gives exact levels both on
horn rays and in an existing escaping cut.

The proper-tail and ray arguments are rederived from the read-only donor
`Surgery/Singular/DeepHorn/Geometry/Levels.lean`: `StrongHorn.exists_tail_avoiding_compact`,
`StrongHorn.tail_not_subset_compact`, `SingularLimitConclusion.exists_horn_tail_scalar_gt`,
`SingularLimitConclusion.exists_horn_ray_scalar_eq`, and
`SingularLimitConclusion.exists_horn_scalar_eq_inverse_sq`. No Surgery module is imported.
The cut-level lemma retains its closure premise explicitly; this file does not assert
separation by a newly chosen neck sphere. The stage derivation is
`proof-work/tasks/M32/derivations/horn-levels.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

section ProperHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

/-- A compact set misses a full proper-horn tail, as used in the selected
level argument of Morgan--Tian Theorem 11.31, printed pp. 291--292. -/
theorem horn_exists_tail_avoiding_compact (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      ∀ s : UnitTwoSphere, ∀ t : ℝ, b < t → t < 1 →
        horn.parameterization (s, t) ∉ K := by
  let A : Set (UnitTwoSphere × Set.Ico (0 : ℝ) 1) :=
    {z | horn.parameterization (z.1, (z.2 : ℝ)) ∈ K}
  have hA : IsCompact A := horn.proper K hK
  by_cases hne : A.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hA.exists_isMaxOn hne
      (continuous_subtype_val.comp continuous_snd).continuousOn
    refine ⟨z.2, z.2.property.1, z.2.property.2, ?_⟩
    intro s t hzt ht hx
    have hmem : (s, ⟨t, ⟨z.2.property.1.trans hzt.le, ht⟩⟩) ∈ A := hx
    exact (not_le_of_gt hzt) (hmax hmem)
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    intro s t ht ht1 hx
    exact hne ⟨(s, ⟨t, ⟨ht.le, ht1⟩⟩), hx⟩

/-- Every full horn tail escapes compact sets, the proper-end property
used in Morgan--Tian Theorem 11.31, printed pp. 291--292. -/
theorem horn_tail_not_subset_compact (horn : StrongHorn E epsilon)
    (b : ℝ) (hb : b < 1)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ¬ horn.parameterization '' (Set.univ ×ˢ Set.Ioo b 1) ⊆ K := by
  obtain ⟨c, _, hc1, hc⟩ := horn_exists_tail_avoiding_compact horn K hK
  obtain ⟨t, ht, ht1⟩ := exists_between (max_lt hb hc1)
  have hsphere : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨s, hs⟩ := hsphere
  let p : UnitTwoSphere := ⟨s, hs⟩
  intro hsub
  exact hc p t ((le_max_right b c).trans_lt ht) ht1
    (hsub ⟨(p, t), ⟨Set.mem_univ _, (le_max_left b c).trans_lt ht, ht1⟩, rfl⟩)

end ProperHorn

section ScalarLevels

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {H : SingularTimeAssumptions F T M}

/-- The actual terminal scalar exceeds any fixed real level on a full horn
tail, as in Morgan--Tian Theorem 11.31, printed pp. 291--292. -/
theorem horn_exists_tail_scalar_gt (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension epsilon) (q : ℝ) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      ∀ s : UnitTwoSphere, ∀ t : ℝ, b < t → t < 1 →
        q < (Q.extension.extended.connection T).scalarCurvature
          (horn.parameterization (s, t)) := by
  obtain ⟨b, hb0, hb1, hb⟩ := horn_exists_tail_avoiding_compact horn _
    (terminalScalarSublevel_isCompact Q q)
  exact ⟨b, hb0, hb1, fun s t ht ht1 => lt_of_not_ge (hb s t ht ht1)⟩

/-- A level above a ray's boundary scalar is attained along that ray,
the continuity step in Morgan--Tian Theorem 11.31, printed p. 291. -/
theorem horn_exists_ray_scalar_eq (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension epsilon) (s : UnitTwoSphere) (q : ℝ)
    (hq : (Q.extension.extended.connection T).scalarCurvature
      (horn.parameterization (s, 0)) ≤ q) :
    ∃ t : Set.Ico (0 : ℝ) 1,
      (Q.extension.extended.connection T).scalarCurvature
        (horn.parameterization (s, (t : ℝ))) = q := by
  let : PreconnectedSpace (Set.Ico (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Ico
  let f : Set.Ico (0 : ℝ) 1 → ℝ := fun t =>
    (Q.extension.extended.connection T).scalarCurvature (horn.coordinate (s, t))
  have hf : Continuous f :=
    (Q.extension.extended.connection T).continuous_scalarCurvature.comp
      (continuous_subtype_val.comp
        (horn.coordinate.continuous.comp (continuous_const.prodMk continuous_id)))
  obtain ⟨b, hb0, hb1, hb⟩ := horn_exists_tail_scalar_gt Q horn q
  obtain ⟨t, hbt, ht1⟩ := exists_between hb1
  let t0 : Set.Ico (0 : ℝ) 1 := ⟨0, ⟨le_rfl, by norm_num⟩⟩
  let t1 : Set.Ico (0 : ℝ) 1 := ⟨t, ⟨hb0.trans hbt.le, ht1⟩⟩
  have h0 : f t0 ≤ q := by simpa [f, horn.coordinate_eq, t0] using hq
  have h1 : q ≤ f t1 := by
    simpa [f, horn.coordinate_eq, t1] using (hb s t hbt ht1).le
  obtain ⟨a, ha⟩ := intermediate_value_univ t0 t1 hf ⟨h0, h1⟩
  exact ⟨a, by simpa [f, horn.coordinate_eq] using ha⟩

/-- The exact inverse-square surgery level is attained in the horn carrier,
as required in Morgan--Tian Theorem 11.31, printed pp. 291--292. -/
theorem horn_exists_scalar_eq_inverse_sq (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension epsilon)
    {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (hhr : h ≤ r)
    (hboundary : HornBoundaryBelow horn r) :
    ∃ x ∈ horn.carrier,
      (Q.extension.extended.connection T).scalarCurvature x = h⁻¹ ^ 2 := by
  have hsphere : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨s, hs⟩ := hsphere
  let p : UnitTwoSphere := ⟨s, hs⟩
  have hp : horn.parameterization (p, 0) ∈ horn.boundary_sphere := by
    rw [horn.boundary_sphere_eq]
    exact ⟨(p, 0), ⟨Set.mem_univ _, rfl⟩, rfl⟩
  have hlevel : r⁻¹ ^ 2 ≤ h⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hr.le) ((inv_le_inv₀ hr hh).2 hhr) 2
  obtain ⟨t, ht⟩ := horn_exists_ray_scalar_eq Q horn p (h⁻¹ ^ 2)
    ((hboundary _ hp).trans hlevel)
  refine ⟨horn.coordinate (p, t), (horn.coordinate (p, t)).property, ?_⟩
  simpa [horn.coordinate_eq] using ht

/-- Scalar curvature is unbounded above on an actual escaping end cut,
using the compact sublevels of Morgan--Tian Theorem 11.31, printed p. 291. -/
theorem hornCut_exists_scalar_gt (Q : SingularLimitConclusion H)
    {delta rho : ℝ} {horn : StrongHorn Q.extension epsilon}
    {N : TerminalStrongNeck Q.extension delta} (cut : HornEndCut horn N rho) (q : ℝ) :
    ∃ x ∈ cut.carrier, q < (Q.extension.extended.connection T).scalarCurvature x := by
  by_contra h
  push Not at h
  exact cut.escapes_compact _ (terminalScalarSublevel_isCompact Q q) h

/-- Any level strictly above the scalar at a closure point is attained
inside an existing end cut. This is the level step of Corollary 11.36,
printed p. 292; the closure premise remains an explicit topology obligation. -/
theorem hornCut_exists_scalar_eq_of_mem_closure (Q : SingularLimitConclusion H)
    {delta rho : ℝ} {horn : StrongHorn Q.extension epsilon}
    {N : TerminalStrongNeck Q.extension delta} (cut : HornEndCut horn N rho)
    {x0 : (Q.extension.extended.slice T).carrier} (hx0 : x0 ∈ closure cut.carrier)
    {q : ℝ} (hq : (Q.extension.extended.connection T).scalarCurvature x0 < q) :
    ∃ x ∈ cut.carrier,
      (Q.extension.extended.connection T).scalarCurvature x = q := by
  let R := (Q.extension.extended.connection T).scalarCurvature
  have hR : Continuous R := (Q.extension.extended.connection T).continuous_scalarCurvature
  obtain ⟨a, haq, ha⟩ := mem_closure_iff.mp hx0 {x | R x < q}
    (isOpen_lt hR continuous_const) hq
  obtain ⟨b, hb, hbq⟩ := hornCut_exists_scalar_gt Q cut q
  have hcut : IsPreconnected cut.carrier := by
    rw [cut.component_eq]
    exact isPreconnected_connectedComponentIn
  exact hcut.intermediate_value ha hb hR.continuousOn ⟨haq.le, hbq.le⟩

end ScalarLevels

end PoincareMT.M32
