import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Recognition.FiniteModelTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Recognition.ModelComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.Injection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

open Classical in
theorem PLDomain.nonempty_edgeComponent_sourceSquareMap_of_original_model
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    {e : ι → OpenPartialHomeomorph X0 V3} {R S : Set X0}
    (he : PLDomain e R) (hR : IsCompact R) (hS : S ⊆ frontier R)
    (hwhole : ∀ x ∈ S, connectedComponentIn S x = connectedComponentIn (frontier R) x)
    (hnt : ∀ x : S, Nontrivial (FundamentalGroup (connectedComponentIn S x)
      ⟨x, mem_connectedComponentIn x.property⟩))
    (hinj : ∀ x : frontier R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier R, X0)) x))
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (f : E → X0) (hf : PolyhedralPLInCharts e f J.space)
    (H : J.space ≃ₜ S) (hH : ∀ z : J.space, f z = (H z : X0))
    (D : J.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    Nonempty (PeriodicSquare.SourceSquareMap 64 (J.edgeComponentComplex D)) := by
  obtain ⟨T, G, hTS, hcomponent, hG⟩ :=
    exists_whole_source_component_of_finite_model J hJ H D
  obtain ⟨z, hz⟩ := (J.edgeComponentComplex_isPathConnected D).nonempty
  let x : S := ⟨G ⟨z, hz⟩, hTS (G ⟨z, hz⟩).property⟩
  have hxT : (x : X0) ∈ T := (G ⟨z, hz⟩).property
  have hT : T = connectedComponentIn (frontier R) x :=
    (hcomponent x hxT).symm.trans (hwhole x x.property)
  have hnt' : Nontrivial (FundamentalGroup (connectedComponentIn (frontier R) x)
      ⟨x, mem_connectedComponentIn (hS x.property)⟩) := by
    let C := Homeomorph.setCongr (hwhole x x.property)
    let b : connectedComponentIn S (x : X0) := ⟨x, mem_connectedComponentIn x.property⟩
    let : Nontrivial (FundamentalGroup (connectedComponentIn S (x : X0)) b) := hnt x
    exact (C.fundamentalGroupMulEquiv b).injective.nontrivial
  have hinj' : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier R) x, X0))
      ⟨x, mem_connectedComponentIn (hS x.property)⟩) := by
    let inclusion := ContinuousMap.inclusion (connectedComponentIn_subset (frontier R) x)
    change Function.Injective (FundamentalGroup.map
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(frontier R, X0)).comp inclusion) _)
    rw [FundamentalGroup.map_comp]
    apply (hinj _).comp
    exact FundamentalGroup.inclusion_injective_of_whole_component
      (connectedComponentIn_subset (frontier R) x)
      (fun y hy => (connectedComponentIn_eq hy).symm) _
  have hK : (J.edgeComponentComplex D).faces.Finite :=
    hJ.subset (J.edgeComponentComplex_le D)
  apply he.nonempty_sourceSquareMap_of_original_component_model hR x (hS x.property)
    hnt' hinj' (J.edgeComponentComplex D) hK f
    (hf.restrict_finite _ hK (SimplicialComplex.space_subset_of_le (J.edgeComponentComplex_le D)))
    (G.trans (Homeomorph.setCongr hT))
  intro w
  exact (hH (Set.inclusion
    (SimplicialComplex.space_subset_of_le (J.edgeComponentComplex_le D)) w)).trans (hG w).symm

open Classical in
theorem PLDomain.exists_square_maps_on_original_phase_collar
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    {e : ι → OpenPartialHomeomorph X0 V3} {R S T N : Set X0}
    (he : PLDomain e R) (hR : IsCompact R)
    (hS : IsClosed S) (hT : IsClosed T) (hdis : Disjoint S T)
    (hfront : frontier R = S ∪ T)
    (model : FrontierResidualModel e N S)
    (hnt : ∀ i (x : model.components i), Nontrivial (FundamentalGroup (model.components i) x))
    (hinj : ∀ x : frontier R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier R, X0)) x))
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 ≤ r) (c : E × ℝ → X0)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (H : J.space ≃ₜ S) (hzero : ∀ z : J.space, c (z, 0) = (H z : X0)) :
    ∃ u : J.vertexAbstractComplex.edgeGraph.ConnectedComponent → (ℝ × ℝ) → E,
      ∀ D, FinitePiecewiseAffineOn (u D) (Icc 0 64 ×ˢ Icc 0 64) ∧
        u D '' (Icc 0 64 ×ˢ Icc 0 64) = (J.edgeComponentComplex D).space ∧
        ∀ z w : PeriodicSquare.Square 64,
          u D (z.1, z.2) = u D (w.1, w.2) ↔
            PeriodicSquare.projection 64 z = PeriodicSquare.projection 64 w := by
  let : Fact (0 < (64 : ℝ)) := ⟨by norm_num⟩
  have hSfront : S ⊆ frontier R := hfront.symm ▸ subset_union_left
  have hntS (x : S) : Nontrivial (FundamentalGroup (connectedComponentIn S x)
      ⟨x, mem_connectedComponentIn x.property⟩) := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (model.cover.symm.subset x.property)
    have hall : ∀ y : connectedComponentIn S (x : X0),
        Nontrivial (FundamentalGroup (connectedComponentIn S (x : X0)) y) := by
      rw [(model.component i).2.2.2 x hi]
      exact hnt i
    exact hall _
  let a : E →ᴬ[ℝ] (E × ℝ) :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have ha : FinitePiecewiseAffineOn a J.space :=
    ⟨J, hJ, rfl, J.affineOnFaces_affine a⟩
  have hzeroPL : PolyhedralPLInCharts e (fun z => c (z, 0)) J.space :=
    hc.comp_finitePiecewiseAffineOn J hJ ha
      (fun z hz => ⟨hz, neg_nonpos.mpr hr, hr⟩)
  have hex (D : J.vertexAbstractComplex.edgeGraph.ConnectedComponent) :=
    he.nonempty_edgeComponent_sourceSquareMap_of_original_model hR hSfront
      (fun x hx => connectedComponentIn_eq_of_disjoint_closed_partition hS hT hdis hfront hx)
      hntS hinj J hJ (fun z => c (z, 0)) hzeroPL H hzero D
  let M (D : J.vertexAbstractComplex.edgeGraph.ConnectedComponent) := (hex D).some
  choose u hu hvalue using fun D => (M D).finite_piecewise_affine
  refine ⟨u, fun D => ⟨hu D, ?_, ?_⟩⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      let w : PeriodicSquare.Square 64 := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
      rw [show u D z = ((M D).map w : E) from hvalue D w]
      exact ((M D).map w).property
    · intro hy
      obtain ⟨z, hz⟩ := (M D).surjective ⟨y, hy⟩
      exact ⟨(z.1, z.2), ⟨z.1.property, z.2.property⟩,
        (hvalue D z).trans (congrArg Subtype.val hz)⟩
  · intro z w
    rw [hvalue D z, hvalue D w, Subtype.val_inj]
    rw [(M D).fibers, PeriodicSquare.projection_eq_iff]

end PoincareConjecture.M76
