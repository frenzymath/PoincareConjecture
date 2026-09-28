import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.HornSelection
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}


theorem exists_tail_avoiding_compact (horn : StrongHorn E epsilon)
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


theorem tail_not_subset_compact (horn : StrongHorn E epsilon)
    (b : ℝ) (hb : b < 1)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ¬ horn.parameterization '' (Set.univ ×ˢ Set.Ioo b 1) ⊆ K := by
  obtain ⟨c, hc0, hc1, hc⟩ := horn.exists_tail_avoiding_compact K hK
  obtain ⟨t, ht, ht1⟩ := exists_between (max_lt hb hc1)
  let s : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
  intro hsub
  exact hc s t ((le_max_right b c).trans_lt ht) ht1
    (hsub ⟨(s, t), ⟨Set.mem_univ _, (le_max_left b c).trans_lt ht, ht1⟩, rfl⟩)

end StrongHorn

namespace SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions F T M}


theorem isCompact_scalar_sublevel (Q : SingularLimitConclusion H) (q : ℝ) :
    IsCompact {x | (Q.extension.extended.connection T).scalarCurvature x ≤ q} := by
  obtain ⟨L, hL⟩ := Q.scalar_lower
  have heq : {x | Q.terminal_scalar x ≤ q} = Q.terminal_scalar ⁻¹' Set.Icc L q := by
    ext x
    exact ⟨fun hx => ⟨hL x, hx⟩, fun hx => hx.2⟩
  rw [← Q.terminal_scalar_eq, heq]
  exact Q.scalar_proper _ isCompact_Icc


theorem isCompact_closure_of_scalar_bound (Q : SingularLimitConclusion H)
    (U : Set (Q.extension.extended.slice T).carrier) (q : ℝ)
    (hbound : ∀ x ∈ U, (Q.extension.extended.connection T).scalarCurvature x ≤ q) :
    IsCompact (closure U) := by
  apply (Q.isCompact_scalar_sublevel q).of_isClosed_subset isClosed_closure
  exact closure_minimal hbound
    (isClosed_le (Q.extension.extended.connection T).continuous_scalarCurvature continuous_const)


theorem exists_horn_tail_scalar_gt (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon)) (q : ℝ) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      ∀ s : UnitTwoSphere, ∀ t : ℝ, b < t → t < 1 →
        q < (Q.extension.extended.connection T).scalarCurvature
          (horn.parameterization (s, t)) := by
  obtain ⟨b, hb0, hb1, hb⟩ := horn.exists_tail_avoiding_compact _
    (Q.isCompact_scalar_sublevel q)
  exact ⟨b, hb0, hb1, fun s t ht ht1 => lt_of_not_ge (hb s t ht ht1)⟩


theorem exists_horn_ray_scalar_eq (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon))
    (s : UnitTwoSphere) (q : ℝ)
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
  obtain ⟨b, hb0, hb1, hb⟩ := Q.exists_horn_tail_scalar_gt horn q
  obtain ⟨t, hbt, ht1⟩ := exists_between hb1
  let t0 : Set.Ico (0 : ℝ) 1 := ⟨0, ⟨le_rfl, by norm_num⟩⟩
  let t1 : Set.Ico (0 : ℝ) 1 := ⟨t, ⟨hb0.trans hbt.le, ht1⟩⟩
  have h0 : f t0 ≤ q := by simpa [f, horn.coordinate_eq, t0] using hq
  have h1 : q ≤ f t1 := by
    simpa [f, horn.coordinate_eq, t1] using (hb s t hbt ht1).le
  obtain ⟨a, ha⟩ := intermediate_value_univ t0 t1 hf ⟨h0, h1⟩
  exact ⟨a, by simpa [f, horn.coordinate_eq] using ha⟩



theorem exists_last_horn_ray_scalar_eq (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon))
    (s : UnitTwoSphere) (q : ℝ)
    (hq : (Q.extension.extended.connection T).scalarCurvature
      (horn.parameterization (s, 0)) ≤ q) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      (Q.extension.extended.connection T).scalarCurvature
        (horn.parameterization (s, b)) = q ∧
      ∀ t : ℝ, b < t → t < 1 →
        q < (Q.extension.extended.connection T).scalarCurvature
          (horn.parameterization (s, t)) := by
  let R := (Q.extension.extended.connection T).scalarCurvature
  let K : Set (Q.extension.extended.slice T).carrier := {x | R x ≤ q}
  let A : Set (UnitTwoSphere × Set.Ico (0 : ℝ) 1) :=
    {z | horn.parameterization (z.1, (z.2 : ℝ)) ∈ K} ∩ {z | z.1 = s}
  have hA : IsCompact A :=
    (horn.proper K (Q.isCompact_scalar_sublevel q)).inter_right
      (isClosed_eq continuous_fst continuous_const)
  have hAne : A.Nonempty :=
    ⟨(s, ⟨0, ⟨le_rfl, by norm_num⟩⟩), hq, rfl⟩
  obtain ⟨z, hz, hmax⟩ := hA.exists_isMaxOn hAne
    (continuous_subtype_val.comp continuous_snd).continuousOn
  have hzs : z.1 = s := hz.2
  have hzq : R (horn.parameterization (s, (z.2 : ℝ))) ≤ q := by
    simpa only [Set.mem_ofPred_eq, K, hzs] using hz.1
  have hlater : ∀ t : ℝ, (z.2 : ℝ) < t → t < 1 →
      q < R (horn.parameterization (s, t)) := by
    intro t ht ht1
    apply lt_of_not_ge
    intro hle
    exact (not_le_of_gt ht) (hmax
      (show (s, ⟨t, ⟨z.2.property.1.trans ht.le, ht1⟩⟩) ∈ A from ⟨hle, rfl⟩))
  refine ⟨z.2, z.2.property.1, z.2.property.2, ?_, hlater⟩
  apply le_antisymm hzq
  by_contra hnot
  have hzlt : R (horn.parameterization (s, (z.2 : ℝ))) < q := lt_of_not_ge hnot
  let f : ℝ → ℝ := fun t => R (horn.parameterization (s, t))
  have hf : ContinuousOn f (Set.Ico (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Set.Ico (0 : ℝ) 1 => f t)
    have hc : Continuous (fun t : Set.Ico (0 : ℝ) 1 => R (horn.coordinate (s, t))) :=
      (Q.extension.extended.connection T).continuous_scalarCurvature.comp
        (continuous_subtype_val.comp
          (horn.coordinate.continuous.comp (continuous_const.prodMk continuous_id)))
    simpa only [horn.coordinate_eq, f] using hc
  obtain ⟨c, hzc, hc1⟩ := exists_between z.2.property.2
  have hfc : q < f c := hlater c hzc hc1
  have hfccont : ContinuousOn f (Set.Icc (z.2 : ℝ) c) :=
    hf.mono (fun t ht => ⟨z.2.property.1.trans ht.1, ht.2.trans_lt hc1⟩)
  obtain ⟨t, ht, htq⟩ := intermediate_value_Icc hzc.le hfccont ⟨hzlt.le, hfc.le⟩
  have hzt : (z.2 : ℝ) < t := lt_of_le_of_ne ht.1 (by
    intro heq
    exact (ne_of_lt hzlt) (heq ▸ htq))
  exact (ne_of_gt (hlater t hzt (ht.2.trans_lt hc1))) htq


theorem exists_horn_scalar_eq_inverse_sq (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon))
    {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (hhr : h ≤ r)
    (hboundary : HornBoundaryBelow horn r) :
    ∃ x ∈ horn.carrier,
      (Q.extension.extended.connection T).scalarCurvature x = h⁻¹ ^ 2 := by
  let s : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
  have hs : horn.parameterization (s, 0) ∈ horn.boundary_sphere := by
    rw [horn.boundary_sphere_eq]
    exact ⟨(s, 0), ⟨Set.mem_univ _, rfl⟩, rfl⟩
  have hlevel : r⁻¹ ^ 2 ≤ h⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hr.le) ((inv_le_inv₀ hr hh).2 hhr) 2
  obtain ⟨t, ht⟩ := Q.exists_horn_ray_scalar_eq horn s (h⁻¹ ^ 2)
    ((hboundary _ hs).trans hlevel)
  refine ⟨horn.coordinate (s, t), (horn.coordinate (s, t)).property, ?_⟩
  simpa [horn.coordinate_eq] using ht

end SingularLimitConclusion

end PoincareConjecture
