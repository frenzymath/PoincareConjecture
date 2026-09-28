import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.CoordinateCut









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem GeneralizedStrongNeck.isCompact_central_sphere
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) : IsCompact N.central_sphere := by
  let z0 : Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  let f : UnitTwoSphere → (F.slice t).carrier := fun s => N.coordinate (s, z0)
  have hf : Continuous f := continuous_subtype_val.comp
    (N.coordinate.continuous.comp (continuous_id.prodMk continuous_const))
  have heq : range f = N.central_sphere := by
    rw [N.central_sphere_eq]
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨(s, 0), ⟨mem_univ _, rfl⟩, (N.coordinate_map_eq (s, z0)).symm⟩
    · rintro ⟨⟨s, a⟩, ⟨_, ha⟩, rfl⟩
      have ha0 : a = 0 := ha
      subst a
      exact ⟨s, N.coordinate_map_eq (s, z0)⟩
  rw [← heq]
  exact isCompact_range hf

namespace StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}


def coordinatePrefix (horn : StrongHorn E epsilon) (b : ℝ) :
    Set (E.extended.slice T).carrier :=
  horn.parameterization '' (univ ×ˢ Icc 0 b)

theorem isCompact_coordinatePrefix (horn : StrongHorn E epsilon)
    {b : ℝ} (hb1 : b < 1) : IsCompact (horn.coordinatePrefix b) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply horn.parameterization_smooth.continuousOn.mono
  intro z hz
  exact ⟨hz.1, (neg_lt_zero.mpr horn.collar_pos).trans_le hz.2.1,
    hz.2.2.trans_lt hb1⟩

theorem carrier_subset_prefix_union_tail (horn : StrongHorn E epsilon) (b : ℝ) :
    horn.carrier ⊆ horn.coordinatePrefix b ∪ horn.coordinateTail b := by
  intro x hx
  let z := horn.coordinate.symm ⟨x, hx⟩
  have hz : horn.parameterization (z.1, (z.2 : ℝ)) = x :=
    horn.parameterization_coordinate_symm ⟨x, hx⟩
  rcases le_or_gt (z.2 : ℝ) b with hle | hgt
  · exact Or.inl ⟨(z.1, z.2), ⟨mem_univ _, z.2.property.1, hle⟩, hz⟩
  · exact Or.inr ⟨(z.1, z.2), ⟨mem_univ _, hgt, z.2.property.2⟩, hz⟩



theorem exists_unique_escaping_component (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ∃ x ∈ horn.carrier \ K, ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      horn.coordinateTail b ⊆ connectedComponentIn (horn.carrier \ K) x ∧
      (∀ L : Set (E.extended.slice T).carrier, IsCompact L →
        ¬ connectedComponentIn (horn.carrier \ K) x ⊆ L) ∧
      (∀ y : (E.extended.slice T).carrier,
        (∀ L : Set (E.extended.slice T).carrier, IsCompact L →
          ¬ connectedComponentIn (horn.carrier \ K) y ⊆ L) →
        connectedComponentIn (horn.carrier \ K) y =
          connectedComponentIn (horn.carrier \ K) x) := by
  obtain ⟨b, hb0, hb1, havoid⟩ := horn.exists_tail_avoiding_compact K hK
  have hsub : horn.coordinateTail b ⊆ horn.carrier \ K := by
    intro x hx
    refine ⟨horn.coordinateTail_subset_carrier hb0 hx, ?_⟩
    obtain ⟨⟨s, t⟩, ⟨_, ht, ht1⟩, rfl⟩ := hx
    exact havoid s t ht ht1
  let s : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
  let x := horn.parameterization (s, (b + 1) / 2)
  have hx : x ∈ horn.coordinateTail b := by
    refine ⟨(s, (b + 1) / 2), ⟨mem_univ _, ?_, ?_⟩, rfl⟩ <;> linarith
  have htail := (horn.isPreconnected_coordinateTail hb0).subset_connectedComponentIn hx hsub
  refine ⟨x, hsub hx, b, hb0, hb1, htail, ?_, ?_⟩
  · intro L hL hcontain
    exact horn.tail_not_subset_compact b hb1 L hL (htail.trans hcontain)
  · intro y hescape
    by_contra hne
    apply hescape (horn.coordinatePrefix b) (horn.isCompact_coordinatePrefix hb1)
    intro z hz
    rcases horn.carrier_subset_prefix_union_tail b
      (connectedComponentIn_subset (horn.carrier \ K) y hz).1 with hp | ht
    · exact hp
    · exact False.elim (hne ((connectedComponentIn_eq hz).trans
        (connectedComponentIn_eq (htail ht)).symm))



theorem exists_neck_escaping_component (horn : StrongHorn E epsilon)
    {delta : ℝ} (N : TerminalStrongNeck E delta) :
    ∃ x ∈ horn.carrier \ N.central_sphere, ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      horn.coordinateTail b ⊆ connectedComponentIn (horn.carrier \ N.central_sphere) x ∧
      (∀ L : Set (E.extended.slice T).carrier, IsCompact L →
        ¬ connectedComponentIn (horn.carrier \ N.central_sphere) x ⊆ L) ∧
      (∀ y : (E.extended.slice T).carrier,
        (∀ L : Set (E.extended.slice T).carrier, IsCompact L →
          ¬ connectedComponentIn (horn.carrier \ N.central_sphere) y ⊆ L) →
        connectedComponentIn (horn.carrier \ N.central_sphere) y =
          connectedComponentIn (horn.carrier \ N.central_sphere) x) :=
  horn.exists_unique_escaping_component N.central_sphere N.isCompact_central_sphere



noncomputable def endCutOfNoLowCurvature (horn : StrongHorn E epsilon)
    {delta : ℝ} (N : TerminalStrongNeck E delta) (rho : ℝ)
    (hhigh : ∀ x ∈ horn.carrier,
      rho⁻¹ ^ 2 < (E.extended.connection T).scalarCurvature x) : HornEndCut horn N rho := by
  apply Classical.choice
  obtain ⟨x, hx, b, hb0, hb1, htail, hescape, _⟩ := horn.exists_neck_escaping_component N
  exact ⟨{
    point := x
    point_mem := hx
    carrier := connectedComponentIn (horn.carrier \ N.central_sphere) x
    component_eq := rfl
    tail_level := b
    tail_level_nonneg := hb0
    tail_level_lt_one := hb1
    contains_tail := htail
    escapes_compact := hescape
    disjoint_low_curvature := disjoint_left.mpr (fun y hy hlow =>
      (not_le_of_gt (hhigh y
        (connectedComponentIn_subset (horn.carrier \ N.central_sphere) x hy).1)) hlow) }⟩

end StrongHorn

end PoincareConjecture
