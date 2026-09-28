import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.ActualIntersections











set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ V} {j : V → t.Carrier} {R : Set M} {boundary : Set V}

namespace OriginalRelativeNormalization

variable (D : OriginalRelativeNormalization step K j R boundary)

def faceIntersection (i : Fin D.length) (a b : Finset V3) : AffineSubspace ℝ V3 :=
  affineSpan ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3)) ⊓
    affineSpan ℝ (b : Set V3)

def exceptionalCoordinates (i : Fin D.length) (a b : Finset V3) : Set V3 :=
  {z | z ∈ D.faceIntersection i a b ∧
    Module.finrank ℝ (D.faceIntersection i a b).direction = 0}


def exceptionalValues : Set s.Carrier :=
  ⋃ i : Fin D.length, ⋃ old : (D.prior i.val).faces,
    ⋃ a ∈ (D.motions i).freeComplex.faces,
      ⋃ b ∈ ((D.motions i).targets old).faces,
        (D.activeBox i).lower.symm '' D.exceptionalCoordinates i a b

omit [FiniteDimensional ℝ V] in
theorem exceptionalCoordinates_finite (i : Fin D.length) (a b : Finset V3) :
    (D.exceptionalCoordinates i a b).Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  have hxy := (D.faceIntersection i a b).vsub_mem_direction hx.1 hy.1
  rw [Submodule.finrank_eq_zero.mp hx.2, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hxy
  exact hxy

omit [FiniteDimensional ℝ V] in

theorem exceptionalValues_finite : D.exceptionalValues.Finite := by
  apply Set.finite_iUnion
  intro i
  let : Fintype (D.prior i.val).faces :=
    (D.source_finite.subset (D.prefix_le i.val)).fintype
  apply Set.finite_iUnion
  intro old
  exact ((D.motions i).subdivision_finite.subset (D.motions i).free_le).biUnion
    fun a _ ↦ ((D.motions i).targets_finite old).biUnion
      fun b _ ↦ (D.exceptionalCoordinates_finite i a b).image _




theorem exists_triangle_interiors_of_not_exceptional
    (hcard : ∀ a ∈ K.faces, a.card ≤ 3)
    {x y : V} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : step.projection (step.inclusion ((D.states D.length).map x)) =
      step.projection (step.inclusion ((D.states D.length).map y)))
    (hex : step.projection (step.inclusion ((D.states D.length).map x)) ∉ D.exceptionalValues) :
    ∃ (i : Fin D.length) (x' y' : V) (old : (D.prior i.val).faces) (a b : Finset V3),
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ convexHull ℝ (D.face i : Set V) ∧ x' ∉ (D.prior i.val).space ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ (old.val : Set V)) ∧
      a ∈ (D.motions i).freeComplex.faces ∧ a ∉ (D.motions i).fixedComplex.faces ∧
      b ∈ ((D.motions i).targets old).faces ∧ a.card = 3 ∧ b.card = 3 ∧
      (D.face i).card = 3 ∧ old.val.card = 3 ∧
      (D.activeBox i).upper ((D.states D.length).map x') ∈ intrinsicInterior ℝ
        (convexHull ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3))) ∧
      (D.activeBox i).lower (step.projection (step.inclusion ((D.states D.length).map y'))) ∈
        intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) ∧
      affineSpan ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) = ⊤ := by
  obtain ⟨i, x', y', old, a, b, hswap, hxface, hxold, hyface,
    ha, ha0, hb, hxa, hyb, hac, hbc, hspan, hrank⟩ :=
    D.exists_endpoint_intersection_faces hx hy hne hxy
  have ha3 := hac.trans (D.source_card_le hcard (D.face_range.subset ⟨i, rfl⟩).1)
  have hb3 := hbc.trans (D.source_card_le hcard (D.prefix_le i.val old.property))
  have hpair : step.projection (step.inclusion ((D.states D.length).map x')) =
      step.projection (step.inclusion ((D.states D.length).map y')) := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm
  have hbase : step.projection (step.inclusion ((D.states D.length).map x')) =
      step.projection (step.inclusion ((D.states D.length).map x)) := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hxy.symm
  have hQsource : (D.states D.length).map x' ∈ (D.activeBox i).upper.source :=
    ((D.states D.length).retained
      ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩ hxface).1
  have hBsource := (D.activeBox i).projection_maps hQsource
  have hzero : Module.finrank ℝ (D.faceIntersection i a b).direction ≠ 0 := by
    intro hzero
    apply hex
    apply mem_iUnion.mpr ⟨i, ?_⟩
    apply mem_iUnion.mpr ⟨old, ?_⟩
    apply mem_iUnion₂.mpr ⟨a, ha, ?_⟩
    apply mem_iUnion₂.mpr ⟨b, hb, ?_⟩
    refine ⟨(D.activeBox i).upper ((D.states D.length).map x'), ⟨?_, hzero⟩, ?_⟩
    · refine ⟨convexHull_subset_affineSpan _ (intrinsicInterior_subset hxa), ?_⟩
      rw [(D.activeBox i).projection_value, hpair]
      exact convexHull_subset_affineSpan _ (intrinsicInterior_subset hyb)
    · rw [(D.activeBox i).projection_value]
      exact ((D.activeBox i).lower.left_inv hBsource).trans hbase
  change Module.finrank ℝ (D.faceIntersection i a b).direction + 3 =
    (a.card - 1) + (b.card - 1) at hrank
  have haa : a.card = 3 := by omega
  have hbb : b.card = 3 := by omega
  have hface3 : (D.face i).card = 3 := by
    have h := D.source_card_le hcard (D.face_range.subset ⟨i, rfl⟩).1
    omega
  have hold3 : old.val.card = 3 := by
    have h := D.source_card_le hcard (D.prefix_le i.val old.property)
    omega
  exact ⟨i, x', y', old, a, b, hswap, hxface, hxold, hyface,
    ha, ha0, hb, haa, hbb, hface3, hold3, hxa, hyb, hspan⟩

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
