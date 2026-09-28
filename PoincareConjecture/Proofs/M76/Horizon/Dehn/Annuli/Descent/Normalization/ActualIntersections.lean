import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Assignment.Construction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.HistoryIntersections

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

def activeBox (i : Fin D.length) :
    RelativeChartBox step R
      (j (D.center ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩)) :=
  D.box ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩

omit [FiniteDimensional ℝ V] in

theorem source_card_le {N : ℕ} (hcard : ∀ a ∈ K.faces, a.card ≤ N)
    {a : Finset V} (ha : a ∈ D.source.faces) : a.card ≤ N := by
  obtain ⟨b, hb, hab⟩ := D.subdivision.face_subset a ha
  have hspan : (a : Set V) ⊆ affineSpan ℝ (b : Set V) := by
    intro x hx
    exact convexHull_subset_affineSpan (b : Set V) (hab (subset_convexHull ℝ _ hx))
  exact ((D.source.indep ha).card_le_card_of_subset_affineSpan hspan).trans (hcard b hb)

theorem exists_endpoint_intersection_faces
    {x y : V} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : step.projection (step.inclusion ((D.states D.length).map x)) =
      step.projection (step.inclusion ((D.states D.length).map y))) :
    ∃ (i : Fin D.length) (x' y' : V) (old : (D.prior i.val).faces) (a b : Finset V3),
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ convexHull ℝ (D.face i : Set V) ∧ x' ∉ (D.prior i.val).space ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ (old.val : Set V)) ∧
      a ∈ (D.motions i).freeComplex.faces ∧ a ∉ (D.motions i).fixedComplex.faces ∧
      b ∈ ((D.motions i).targets old).faces ∧
      (D.activeBox i).upper ((D.states D.length).map x') ∈ intrinsicInterior ℝ
        (convexHull ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3))) ∧
      (D.activeBox i).lower (step.projection (step.inclusion ((D.states D.length).map y'))) ∈
        intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) ∧
      a.card ≤ (D.face i).card ∧ b.card ≤ old.val.card ∧
      affineSpan ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) = ⊤ ∧
      Module.finrank ℝ ((affineSpan ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3)) ⊓
        affineSpan ℝ (b : Set V3)).direction) + 3 = (a.card - 1) + (b.card - 1) := by
  have hface (i : Fin D.length) : D.face i ∈ D.source.faces :=
    (D.face_range.subset ⟨i, rfl⟩).1
  have hzero : InjOn ((step.projection ∘ step.inclusion) ∘ (D.states 0).map)
      (D.prior 0).space := by
    rw [D.initial, D.prefix_zero]
    intro u hu v hv huv
    exact D.protected_fiber u hu v (D.subdivision.space_eq.subset
      (SimplicialComplex.space_subset_of_le D.protected_le hv)) huv
  have hselected (i : Fin D.length) : (D.activeBox i).neighborhood ⊆
      (D.activeBox i).upper.source ∩ (D.activeBox i).upper ⁻¹' (D.activeBox i).support.space :=
    fun z hz ↦ ⟨hz.1, show (D.activeBox i).upper z ∈ (D.activeBox i).support.space from
      interior_subset ((D.activeBox i).neighborhood_support hz).2⟩
  have h := step.exists_relative_history_intersection_faces D.source_finite D.face hface
    D.prior (fun k _ ↦ D.prefix_le k) (congrArg SimplicialComplex.space D.prefix_last)
    D.prefix_succ (fun i ↦ (D.activeBox i).upper) (fun i ↦ (D.activeBox i).lower)
    (fun i ↦ (D.activeBox i).support) (fun i ↦ (D.activeBox i).upper_compatible)
    (fun i ↦ (D.activeBox i).projection_value) (fun i ↦ (D.activeBox i).projection_maps)
    (fun i ↦ (D.activeBox i).finite_support) (fun i ↦ (D.activeBox i).support_target)
    (fun a ↦ (D.box a).neighborhood) hselected
    (fun a ↦ (D.box a).neighborhood_injective) D.states D.motions D.transition D.stable hzero
    (D.subdivision.space_eq.symm.subset hx) (D.subdivision.space_eq.symm.subset hy) hne hxy
  simpa only [Module.finrank_fin_fun] using h

theorem endpoint_contact_card_cases
    (hcard : ∀ a ∈ K.faces, a.card ≤ 3)
    {x y : V} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : step.projection (step.inclusion ((D.states D.length).map x)) =
      step.projection (step.inclusion ((D.states D.length).map y))) :
    ∃ (i : Fin D.length) (old : (D.prior i.val).faces) (a b : Finset V3),
      a ∈ (D.motions i).freeComplex.faces ∧ a ∉ (D.motions i).fixedComplex.faces ∧
      b ∈ ((D.motions i).targets old).faces ∧
      ((a.card = 2 ∧ b.card = 3) ∨ (a.card = 3 ∧ b.card = 2) ∨
        (a.card = 3 ∧ b.card = 3)) := by
  obtain ⟨i, _, _, old, a, b, _, _, _, _, ha, ha0, hb, _, _, hac, hbc, _, hrank⟩ :=
    D.exists_endpoint_intersection_faces hx hy hne hxy
  have ha3 := hac.trans (D.source_card_le hcard (D.face_range.subset ⟨i, rfl⟩).1)
  have hb3 := hbc.trans (D.source_card_le hcard (D.prefix_le i.val old.property))
  exact ⟨i, old, a, b, ha, ha0, hb, by omega⟩

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
