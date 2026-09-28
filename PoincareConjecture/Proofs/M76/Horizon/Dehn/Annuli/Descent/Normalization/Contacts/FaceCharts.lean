import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Contacts.Carriers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Contacts.TriangleCharts










set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ V} {j : V → t.Carrier} {R : Set M} {boundary : Set V}

namespace OriginalRelativeNormalization

variable (D : OriginalRelativeNormalization step K j R boundary)



theorem exists_projected_face_crossing
    (hcard : ∀ a ∈ K.faces, a.card ≤ 3)
    {x y : V} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : D.projected x = D.projected y) (hex : D.projected x ∉ D.exceptionalValues) :
    ∃ (i : Fin D.length) (x' y' : V) (old : (D.prior i.val).faces)
      (H : OpenPartialHomeomorph V3 C3),
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ intrinsicInterior ℝ (convexHull ℝ (D.face i : Set V)) ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ (old.val : Set V)) ∧
      (D.face i).card = 3 ∧ old.val.card = 3 ∧
      D.endpoint x' ∈ (D.activeBox i).upper.source ∧
      D.projected y' ∈ (D.activeBox i).lower.source ∧
      (D.activeBox i).upper (D.endpoint x') = (D.activeBox i).lower (D.projected y') ∧
      (D.activeBox i).upper (D.endpoint x') ∈ H.source ∧
      H.source ⊆ (D.activeBox i).lower.target ∧
      H ((D.activeBox i).upper (D.endpoint x')) = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧ LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, z ∈ (D.activeBox i).lower ''
        (D.projected '' convexHull ℝ (D.face i : Set V) ∩ (D.activeBox i).lower.source) ↔
          (H z).2 = 0) ∧
      ∀ z ∈ H.source, z ∈ (D.activeBox i).lower ''
        (D.projected '' convexHull ℝ (old.val : Set V) ∩ (D.activeBox i).lower.source) ↔
          (H z).1.1 = 0 := by
  obtain ⟨i, x', y', old, a, b, hswap, hxface, hxold, hyface,
    ha, ha0, hb, ha3, hb3, hface3, hold3, hpa, hpb, hspan⟩ :=
    D.exists_triangle_interiors_of_not_exceptional hcard hx hy hne hxy hex
  have hpair : D.projected x' = D.projected y' := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm
  have hxQ : D.endpoint x' ∈ (D.activeBox i).upper.source :=
    ((D.states D.length).retained
      ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩ hxface).1
  have hyB : D.projected y' ∈ (D.activeBox i).lower.source :=
    hpair ▸ (D.activeBox i).projection_maps hxQ
  have hcommon : (D.activeBox i).upper (D.endpoint x') =
      (D.activeBox i).lower (D.projected y') :=
    ((D.activeBox i).projection_value (D.endpoint x')).trans
      (congrArg (D.activeBox i).lower hpair)
  have hpb' : (D.activeBox i).upper (D.endpoint x') ∈
      intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) := hcommon.symm ▸ hpb
  obtain ⟨H, hpH, hHO, hH0, hHPL, hHiPL, hHA, hHB⟩ :=
    D.exists_triangle_comparison_chart hcard i old ha ha0 hb ha3 hb3 hspan hpa hpb'
      (D.comparisonOpen_open i) (D.active_coordinate_mem_open i hxface hxold)
  refine ⟨i, x', y', old, H, hswap, D.active_intrinsicInterior i hxface hxold,
    hyface, hface3, hold3, hxQ, hyB, hcommon, hpH, ?_, hH0, hHPL, hHiPL, ?_, ?_⟩
  · intro z hz
    exact (D.activeBox i).targets.subset
      ((D.activeBox i).support_target (interior_subset (hHO hz).1))
  · intro z hz
    exact (D.active_carrier_iff i (hHO hz)).symm.trans (hHA z hz)
  · intro z hz
    exact (D.prior_carrier_iff i old (hHO hz)).symm.trans (hHB z hz)

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
