import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PositionData
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.History
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Contacts.Carriers

set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier} {R Fmark : Set M}

namespace MarkedSurfacePositionData

variable (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)

def endpoint : V → t.Carrier := (D.states D.length).map
def projected : V → s.Carrier := (step.projection ∘ step.inclusion) ∘ D.endpoint

def faceIntersection (i : Fin D.length) (a b : Finset V3) : AffineSubspace ℝ V3 :=
  affineSpan ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3)) ⊓ affineSpan ℝ (b : Set V3)

def exceptionalCoordinates (i : Fin D.length) (a b : Finset V3) : Set V3 :=
  {z | z ∈ D.faceIntersection i a b ∧
    Module.finrank ℝ (D.faceIntersection i a b).direction = 0}

def exceptionalValues : Set s.Carrier :=
  ⋃ i : Fin D.length, ⋃ old : (D.previous i.val).faces,
    ⋃ a ∈ (D.motions i).freeComplex.faces,
      ⋃ b ∈ ((D.motions i).targets old).faces,
        (D.lowerChart i).symm '' D.exceptionalCoordinates i a b

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
  let : Fintype (D.previous i.val).faces :=
    (D.source_finite.subset (D.previous_faces i.val).1).fintype
  apply Set.finite_iUnion
  intro old
  exact ((D.motions i).subdivision_finite.subset (D.motions i).free_le).biUnion
    fun a _ => ((D.motions i).targets_finite old).biUnion
      fun b _ => (D.exceptionalCoordinates_finite i a b).image _

omit [FiniteDimensional ℝ V] in
theorem successor_agreement (i : Fin D.length) :
    EqOn D.endpoint ((D.motions i).ambient 1 ∘ (D.states i.val).map)
      (D.previous (i.val + 1)).space := by
  intro x hx
  exact (D.stable (i.val + 1) D.length (by omega) le_rfl hx).trans
    (congrFun (D.transitions i) x)

omit [FiniteDimensional ℝ V] in
theorem active_not_previous (i : Fin D.length) {x : V}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ ((D.order i).val : Set V))) :
    x ∉ (D.previous i.val).space := by
  intro hp
  obtain ⟨a, ha, hxa⟩ := (D.previous i.val).mem_space_iff.mp hp
  obtain ⟨k, hki, hka⟩ := (D.previous_faces i.val).2.subset ha
  have hsub := D.K.subset_of_mem_intrinsicInterior_face (D.order i).property
    ((D.previous_faces i.val).1 ha) hx hxa
  rw [← hka] at hsub
  by_cases heq : (D.order i).val = (D.order k).val
  · have hik := D.order_bijective.injective (Subtype.ext heq)
    subst k
    omega
  · have hik := D.order_before k i (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩)
    omega

theorem exists_triangle_interiors_of_not_exceptional
    {x y : V} (hx : x ∈ D.K.space) (hy : y ∈ D.K.space) (hne : x ≠ y)
    (hxy : D.projected x = D.projected y) (hex : D.projected x ∉ D.exceptionalValues) :
    ∃ (i : Fin D.length) (x' y' : V) (old : (D.previous i.val).faces) (a b : Finset V3),
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ intrinsicInterior ℝ (convexHull ℝ ((D.order i).val : Set V)) ∧
      x' ∉ (D.previous i.val).space ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ (old.val : Set V)) ∧
      a ∈ (D.motions i).freeComplex.faces ∧ a ∉ (D.motions i).fixedComplex.faces ∧
      b ∈ ((D.motions i).targets old).faces ∧ a.card = 3 ∧ b.card = 3 ∧
      (D.order i).val.card = 3 ∧ old.val.card = 3 ∧ D.boundary i = false ∧
      D.upperChart i (D.endpoint x') ∈ intrinsicInterior ℝ
        (convexHull ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3))) ∧
      D.lowerChart i (D.projected y') ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) ∧
      affineSpan ℝ ((D.motions i).coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) = ⊤ := by
  have hcell : ∀ a : D.K.faces, InjOn D.projected (convexHull ℝ (a.val : Set V)) := by
    simpa only [projected, endpoint, ← D.final_state] using D.cell_injective
  obtain ⟨i, k, x', y', old, a, b, hki, hswap, hxface, hyface, hold, _,
    ha, ha0, hb, hxa, hyb, hac, hbc, hspan, hrank⟩ :=
    step.exists_surface_history_intersection_faces D.source_finite D.order D.order_bijective
      D.order_before D.previous D.previous_faces D.successor_space D.boundary
      D.upperChart D.lowerChart D.carrier D.upper_compatible D.chart_values D.chart_mapsTo
      D.window D.window_subset D.states D.motions D.transitions D.stable hcell hx hy hne hxy
  have hpair : D.projected x' = D.projected y' := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm
  have hbase : D.projected x' = D.projected x := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hxy.symm
  have hxQ : D.endpoint x' ∈ (D.upperChart i).source :=
    D.window_subset i ((D.states D.length).retained (D.order i) (intrinsicInterior_subset hxface))
  have hxB := D.chart_mapsTo i hxQ
  have hzero : Module.finrank ℝ (D.faceIntersection i a b).direction ≠ 0 := by
    intro hzero
    apply hex
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨old,
      mem_iUnion₂.mpr ⟨a, ha, mem_iUnion₂.mpr ⟨b, hb, ?_⟩⟩⟩⟩
    refine ⟨D.upperChart i (D.endpoint x'), ⟨?_, hzero⟩, ?_⟩
    · refine ⟨convexHull_subset_affineSpan _ (intrinsicInterior_subset hxa), ?_⟩
      rw [D.chart_values]
      change D.lowerChart i (D.projected x') ∈ affineSpan ℝ (b : Set V3)
      rw [hpair]
      exact convexHull_subset_affineSpan _ (intrinsicInterior_subset hyb)
    · rw [D.chart_values]
      exact ((D.lowerChart i).left_inv hxB).trans hbase
  have hmarked : D.boundary i = true →
      (D.order i).val ∈ D.A.faces ∧ (D.order k).val ∈ D.A.faces := by
    intro hi
    have hiA := (D.boundary_iff i).mp hi
    exact ⟨hiA, D.boundary_phase i k hki hiA⟩
  have hbounds := (D.motions i).surface_intersection_rank_bounds D.source_dimension
    D.A D.boundary_dimension (D.order i).property (D.order k).property
    hmarked hac hbc hrank
  have hphase : D.boundary i = false := by
    cases hi : D.boundary i with
    | false => rfl
    | true => exact (hzero (hbounds.2.2.2.1 hi)).elim
  have hdim : Module.finrank ℝ (D.motions i).plane.direction = 3 := by
    simpa only [hphase, Bool.false_eq_true, ↓reduceIte] using (D.motions i).finrank_plane
  rw [hdim] at hrank
  have ha3 := hac.trans (D.source_dimension _ (D.order i).property)
  have hb3 := hbc.trans (D.source_dimension _ (D.order k).property)
  change Module.finrank ℝ (D.faceIntersection i a b).direction + 3 =
    (a.card - 1) + (b.card - 1) at hrank
  have haa : a.card = 3 := by omega
  have hbb : b.card = 3 := by omega
  have hface3 : (D.order i).val.card = 3 := by
    have hh := D.source_dimension _ (D.order i).property
    omega
  have hold3 : old.val.card = 3 := by
    rw [hold]
    have hh := D.source_dimension _ (D.order k).property
    omega
  refine ⟨i, x', y', old, a, b, hswap, hxface, D.active_not_previous i hxface,
    ?_, ha, ha0, hb, haa, hbb, hface3, hold3, hphase, hxa, hyb, ?_⟩
  · rwa [hold]
  · exact hspan.trans ((D.motions i).interior_plane hphase)

end MarkedSurfacePositionData
end Geometry.OriginalPLTower
