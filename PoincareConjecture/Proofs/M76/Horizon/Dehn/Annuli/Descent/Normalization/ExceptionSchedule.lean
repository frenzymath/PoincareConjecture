import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Contacts.WholeCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.FiniteExceptionNeighborhoods










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

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


def exceptionalDoubleValues : Set s.Carrier :=
  D.exceptionalValues ∩ D.projected '' doubleLocusOn D.projected K.space

omit [FiniteDimensional ℝ V] in
theorem exceptionalDoubleValues_finite : D.exceptionalDoubleValues.Finite :=
  D.exceptionalValues_finite.subset inter_subset_left

omit [FiniteDimensional ℝ V] in
theorem exceptionalDoubleValues_interior :
    D.exceptionalDoubleValues ⊆ interior (s.projection ⁻¹' R) := by
  rintro z ⟨_, x, ⟨hx, y, hy, hxy, hne⟩, rfl⟩
  exact D.double_point_interior hx hy hne hxy

omit [FiniteDimensional ℝ V] in


theorem exists_exception_schedule :
    ∃ (n : ℕ) (q : Fin n ≃ D.exceptionalDoubleValues)
      (w : Fin n → TwoBranchWindow (step.projection ∘ step.inclusion))
      (W : Fin n → Set s.Carrier),
      (∀ k, IsOpen (W k) ∧ (q k : s.Carrier) ∈ W k ∧
        IsCompact (closure (W k)) ∧
        closure (W k) ⊆ interior (s.projection ⁻¹' R) ∩ (w k).target ∧
        D.exceptionalDoubleValues ∩ closure (W k) = {(q k : s.Carrier)} ∧
        ∃ a b : K.space, a ≠ b ∧ D.projected a = (q k : s.Carrier) ∧
          D.projected b = (q k : s.Carrier) ∧
          D.endpoint a ∈ (w k).left.source ∧ D.endpoint b ∈ (w k).right.source) ∧
      Pairwise (fun k l ↦ Disjoint (closure (W k)) (closure (W l))) ∧
      Pairwise (fun k l ↦ Disjoint
        ((step.projection ∘ step.inclusion) ⁻¹' closure (W k))
        ((step.projection ∘ step.inclusion) ⁻¹' closure (W l))) ∧
      (∀ k a b,
        (t.charts a).symm.trans ((w k).left.trans (s.charts b)) ∈
          piecewiseAffineGroupoid V3 ∧
        (t.charts a).symm.trans ((w k).right.trans (s.charts b)) ∈
          piecewiseAffineGroupoid V3) ∧
      ∀ k, Disjoint (closure (W k)) (D.projected '' boundary) := by
  classical
  let p := step.projection ∘ step.inclusion
  have hdata (z : D.exceptionalDoubleValues) :
      ∃ (a b : K.space) (w : TwoBranchWindow p),
        a ≠ b ∧ D.projected a = (z : s.Carrier) ∧
        D.projected b = (z : s.Carrier) ∧
        D.endpoint a ∈ w.left.source ∧ D.endpoint b ∈ w.right.source := by
    obtain ⟨x, ⟨hx, y, hy, hxy, hne⟩, hxz⟩ := z.property.2
    obtain ⟨w, hxw, hyw⟩ := step.projectionInclusion_local.exists_twoBranchWindow
      (fun z ↦ (step.projectionInclusion_fiber z).1)
      (fun z ↦ (step.projectionInclusion_fiber z).2) hxy
      (fun h ↦ hne (congrArg Subtype.val (D.endpoint_embedding.injective
        (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)))
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, w, fun h ↦ hne (congrArg Subtype.val h),
      hxz, hxy.symm.trans hxz, hxw, hyw⟩
  choose a b w hab ha hb hal hbr using hdata
  have hzW (z : D.exceptionalDoubleValues) :
      (z : s.Carrier) ∈ interior (s.projection ⁻¹' R) ∩ (w z).target := by
    refine ⟨D.exceptionalDoubleValues_interior z.property, ?_⟩
    rw [← ha z, ← (w z).left_target]
    change p (D.endpoint (a z)) ∈ (w z).left.target
    exact (congrFun (w z).left_eq _) ▸ (w z).left.map_source (hal z)
  obtain ⟨n, q, W, hW, hdis⟩ := exists_finite_exception_neighborhoods
    D.exceptionalDoubleValues_finite
    (fun z ↦ interior (s.projection ⁻¹' R) ∩ (w z).target)
    (fun z ↦ isOpen_interior.inter (w z).open_target) hzW
  refine ⟨n, q, w ∘ q, W, ?_, hdis,
    pairwise_disjoint_exception_preimages p W hdis, ?_, ?_⟩
  · intro k
    exact ⟨(hW k).1, (hW k).2.1, (hW k).2.2.1, (hW k).2.2.2.1,
      (hW k).2.2.2.2, a (q k), b (q k), hab _, ha _, hb _, hal _, hbr _⟩
  · intro k a b
    exact ⟨step.branch_chart_PL (w (q k)).left
      (fun z _ ↦ congrFun (w (q k)).left_eq z) a b,
      step.branch_chart_PL (w (q k)).right
      (fun z _ ↦ congrFun (w (q k)).right_eq z) a b⟩
  · intro k
    apply disjoint_left.mpr
    rintro z hz ⟨x, hx, rfl⟩
    have hxK := D.subdivision.space_eq.subset
      (SimplicialComplex.space_subset_of_le D.protected_le (D.boundary_protected hx))
    exact ((D.projected_proper x hxK).mpr hx).2 ((hW k).2.2.2.1 hz).1

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
