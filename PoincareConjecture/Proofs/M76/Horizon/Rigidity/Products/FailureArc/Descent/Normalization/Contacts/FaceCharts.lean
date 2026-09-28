import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Contacts.ExceptionalValues
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Contacts.TriangleCharts









set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier} {R Fmark : Set M}

namespace MarkedSurfacePositionData

variable (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)

theorem exists_projected_face_crossing
    {x y : V} (hx : x ∈ D.K.space) (hy : y ∈ D.K.space) (hne : x ≠ y)
    (hxy : D.projected x = D.projected y) (hex : D.projected x ∉ D.exceptionalValues) :
    ∃ (i : Fin D.length) (x' y' : V) (old : (D.previous i.val).faces)
      (H : OpenPartialHomeomorph V3 C3),
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ intrinsicInterior ℝ (convexHull ℝ ((D.order i).val : Set V)) ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ (old.val : Set V)) ∧
      (D.order i).val.card = 3 ∧ old.val.card = 3 ∧
      D.endpoint x' ∈ (D.upperChart i).source ∧
      D.projected y' ∈ (D.lowerChart i).source ∧
      D.upperChart i (D.endpoint x') = D.lowerChart i (D.projected y') ∧
      D.upperChart i (D.endpoint x') ∈ H.source ∧
      H.source ⊆ (D.lowerChart i).target ∧
      H (D.upperChart i (D.endpoint x')) = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧ LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, z ∈ (D.lowerChart i) ''
        (D.projected '' convexHull ℝ ((D.order i).val : Set V) ∩ (D.lowerChart i).source) ↔
          (H z).2 = 0) ∧
      ∀ z ∈ H.source, z ∈ (D.lowerChart i) ''
        (D.projected '' convexHull ℝ (old.val : Set V) ∩ (D.lowerChart i).source) ↔
          (H z).1.1 = 0 := by
  obtain ⟨i, x', y', old, a, b, hswap, hxface, hxold, hyface,
    ha, ha0, hb, ha3, hb3, hface3, hold3, _, hpa, hpb, hspan⟩ :=
    D.exists_triangle_interiors_of_not_exceptional hx hy hne hxy hex
  have hpair : D.projected x' = D.projected y' := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm
  have hret (k : ℕ) : MapsTo (D.states k).map
      (convexHull ℝ ((D.order i).val : Set V)) (D.upperChart i).source :=
    fun z hz => D.window_subset i ((D.states k).retained (D.order i) hz)
  have hxQ : D.endpoint x' ∈ (D.upperChart i).source :=
    hret D.length (intrinsicInterior_subset hxface)
  have hyB : D.projected y' ∈ (D.lowerChart i).source :=
    hpair ▸ D.chart_mapsTo i hxQ
  have hcommon : D.upperChart i (D.endpoint x') = D.lowerChart i (D.projected y') :=
    (D.chart_values i (D.endpoint x')).trans (congrArg (D.lowerChart i) hpair)
  have hpb' : D.upperChart i (D.endpoint x') ∈
      intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) := hcommon.symm ▸ hpb
  have hinj : InjOn (D.states i.val).map D.K.space := by
    intro z hz v hv hzv
    exact congrArg Subtype.val ((D.states i.val).embedding.injective
      (a₁ := ⟨z, hz⟩) (a₂ := ⟨v, hv⟩) hzv)
  have hnext := D.successor_agreement i
  have hpO := (D.motions i).active_coordinate_mem_comparisonOpen
    (D.previous_faces i.val).1 (D.previous_faces (i.val + 1)).1 hinj hnext
    ((D.successor_space i).symm.subset (Or.inr (intrinsicInterior_subset hxface)))
    hxold (hret i.val (intrinsicInterior_subset hxface))
  obtain ⟨H, hpH, hHO, hH0, hHPL, hHiPL, hHA, hHB⟩ :=
    (D.motions i).exists_triangle_comparison_chart D.source_finite D.source_dimension
      (D.previous_faces i.val).1 (D.order i).property (D.successor_space i)
      (D.states i.val).original_PL (D.upper_compatible i) old ha ha0 hb ha3 hb3
      hspan hpa hpb' (D.motions i).comparisonOpen_open hpO
  refine ⟨i, x', y', old, H, hswap, hxface, hyface, hface3, hold3,
    hxQ, hyB, hcommon, hpH, ?_, hH0, hHPL, hHiPL, ?_, ?_⟩
  · intro z hz
    exact (D.motions i).support_lower (interior_subset (hHO hz).1)
  · intro z hz
    exact ((D.motions i).active_carrier_iff (D.successor_space i) hnext
      (hret i.val) (hret D.length) (D.chart_values i) (D.chart_mapsTo i) (hHO hz)).symm.trans
        (hHA z hz)
  · intro z hz
    exact ((D.motions i).prior_carrier_iff
      (D.stable i.val D.length i.isLt.le le_rfl) old (hHO hz)).symm.trans (hHB z hz)

end MarkedSurfacePositionData
end Geometry.OriginalPLTower
