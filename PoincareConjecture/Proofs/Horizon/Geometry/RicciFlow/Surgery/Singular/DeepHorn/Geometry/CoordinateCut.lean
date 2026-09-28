import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Levels
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

noncomputable def coordinateHeight (horn : StrongHorn E epsilon) (x : horn.carrier) : ℝ :=
  (horn.coordinate.symm x).2

theorem continuous_coordinateHeight (horn : StrongHorn E epsilon) :
    Continuous horn.coordinateHeight :=
  continuous_subtype_val.comp (continuous_snd.comp horn.coordinate.symm.continuous)

def coordinateSection (horn : StrongHorn E epsilon) (b : ℝ) :
    Set (E.extended.slice T).carrier :=
  horn.parameterization '' (Set.univ ×ˢ ({b} : Set ℝ))

def coordinateTail (horn : StrongHorn E epsilon) (b : ℝ) :
    Set (E.extended.slice T).carrier :=
  horn.parameterization '' (Set.univ ×ˢ Set.Ioo b 1)

theorem parameterization_coordinate_symm (horn : StrongHorn E epsilon)
    (x : horn.carrier) :
    horn.parameterization ((horn.coordinate.symm x).1,
      ((horn.coordinate.symm x).2 : ℝ)) = x := by
  rw [← horn.coordinate_eq]
  exact congrArg Subtype.val (horn.coordinate.apply_symm_apply x)

theorem mem_coordinateSection_iff (horn : StrongHorn E epsilon)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (x : horn.carrier) :
    (x : (E.extended.slice T).carrier) ∈ horn.coordinateSection b ↔
      horn.coordinateHeight x = b := by
  constructor
  · rintro ⟨⟨s, t⟩, ⟨_, ht⟩, heq⟩
    have htb : t = b := ht
    subst t
    have heq' : horn.coordinate (s, ⟨b, hb0, hb1⟩) = x :=
      Subtype.ext ((horn.coordinate_eq _).trans heq)
    rw [← heq']
    simp [coordinateHeight]
  · intro hx
    refine ⟨((horn.coordinate.symm x).1, b), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    simpa only [← hx, coordinateHeight] using horn.parameterization_coordinate_symm x

theorem mem_coordinateTail_iff (horn : StrongHorn E epsilon)
    {b : ℝ} (hb0 : 0 ≤ b) (x : horn.carrier) :
    (x : (E.extended.slice T).carrier) ∈ horn.coordinateTail b ↔
      b < horn.coordinateHeight x := by
  constructor
  · rintro ⟨⟨s, t⟩, ⟨_, hbt, ht1⟩, heq⟩
    have heq' : horn.coordinate (s, ⟨t, hb0.trans hbt.le, ht1⟩) = x :=
      Subtype.ext ((horn.coordinate_eq _).trans heq)
    rw [← heq']
    simpa [coordinateHeight] using hbt
  · intro hx
    refine ⟨((horn.coordinate.symm x).1, ((horn.coordinate.symm x).2 : ℝ)),
      ⟨Set.mem_univ _, hx, (horn.coordinate.symm x).2.property.2⟩,
      horn.parameterization_coordinate_symm x⟩

theorem coordinateTail_subset_carrier (horn : StrongHorn E epsilon)
    {b : ℝ} (hb0 : 0 ≤ b) : horn.coordinateTail b ⊆ horn.carrier := by
  rintro x ⟨⟨s, t⟩, ⟨_, hbt, ht1⟩, rfl⟩
  have hx := (horn.coordinate (s, ⟨t, hb0.trans hbt.le, ht1⟩)).property
  rwa [horn.coordinate_eq] at hx

theorem coordinateTail_subset_diff (horn : StrongHorn E epsilon)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    horn.coordinateTail b ⊆ horn.carrier \ horn.coordinateSection b := by
  intro x hx
  have hxc := horn.coordinateTail_subset_carrier hb0 hx
  refine ⟨hxc, ?_⟩
  intro hxs
  have hgt := (horn.mem_coordinateTail_iff hb0 ⟨x, hxc⟩).mp hx
  have heq := (horn.mem_coordinateSection_iff hb0 hb1 ⟨x, hxc⟩).mp hxs
  exact (ne_of_gt hgt) heq

theorem isPreconnected_coordinateTail (horn : StrongHorn E epsilon)
    {b : ℝ} (hb0 : 0 ≤ b) : IsPreconnected (horn.coordinateTail b) := by
  apply (isPreconnected_univ.prod isPreconnected_Ioo).image
  apply horn.parameterization_smooth.continuousOn.mono
  intro z hz
  exact ⟨hz.1, (neg_lt_zero.mpr horn.collar_pos).trans_le (hb0.trans hz.2.1.le), hz.2.2⟩

theorem coordinateTail_eq_connectedComponentIn (horn : StrongHorn E epsilon)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {x : (E.extended.slice T).carrier} (hx : x ∈ horn.coordinateTail b) :
    horn.coordinateTail b =
      connectedComponentIn (horn.carrier \ horn.coordinateSection b) x := by
  have hsub := horn.coordinateTail_subset_diff hb0 hb1
  apply Set.Subset.antisymm
    ((horn.isPreconnected_coordinateTail hb0).subset_connectedComponentIn hx hsub)
  intro y hy
  let A := connectedComponentIn (horn.carrier \ horn.coordinateSection b) x
  have hAc : A ⊆ horn.carrier := fun z hz =>
    (connectedComponentIn_subset (horn.carrier \ horn.coordinateSection b) x hz).1
  have hA : IsPreconnected (((↑) : horn.carrier → (E.extended.slice T).carrier) ⁻¹' A) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hAc]
    exact isPreconnected_connectedComponentIn
  let x' : horn.carrier := ⟨x, (hsub hx).1⟩
  let y' : horn.carrier := ⟨y, hAc hy⟩
  have hxA : (x' : (E.extended.slice T).carrier) ∈ A := mem_connectedComponentIn (hsub hx)
  have hxgt : b < horn.coordinateHeight x' := (horn.mem_coordinateTail_iff hb0 x').mp hx
  apply (horn.mem_coordinateTail_iff hb0 y').mpr
  by_contra hnot
  obtain ⟨z, hz, hzb⟩ := hA.intermediate_value hy hxA
    horn.continuous_coordinateHeight.continuousOn ⟨le_of_not_gt hnot, hxgt.le⟩
  have hznot := (connectedComponentIn_subset
    (horn.carrier \ horn.coordinateSection b) x hz).2
  exact hznot ((horn.mem_coordinateSection_iff hb0 hb1 z).mpr hzb)

noncomputable def endCutOfCoordinateSection (horn : StrongHorn E epsilon)
    {delta : ℝ} (N : TerminalStrongNeck E delta) (rho : ℝ)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hsphere : N.central_sphere = horn.coordinateSection b)
    (hlow : Disjoint (horn.coordinateTail b)
      {x | (E.extended.connection T).scalarCurvature x ≤ rho⁻¹ ^ 2}) :
    HornEndCut horn N rho := by
  let s : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
  let t : ℝ := (b + 1) / 2
  have hbt : b < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  let x := horn.parameterization (s, t)
  have hx : x ∈ horn.coordinateTail b :=
    ⟨(s, t), ⟨Set.mem_univ _, hbt, ht1⟩, rfl⟩
  refine {
    point := x
    point_mem := ?_
    carrier := horn.coordinateTail b
    component_eq := ?_
    tail_level := b
    tail_level_nonneg := hb0
    tail_level_lt_one := hb1
    contains_tail := Set.Subset.rfl
    escapes_compact := fun K hK => horn.tail_not_subset_compact b hb1 K hK
    disjoint_low_curvature := hlow }
  · simpa only [hsphere] using horn.coordinateTail_subset_diff hb0 hb1 hx
  · simpa only [hsphere] using horn.coordinateTail_eq_connectedComponentIn hb0 hb1 hx

end PoincareConjecture.StrongHorn
