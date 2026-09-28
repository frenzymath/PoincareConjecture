import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedChartSubdivision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.ModelComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Topology.Mathlib.FiniteClosedComponentPartition



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem restrict_marked_surface_charts_to_open_piece
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) {S T M U : Set X}
    (hU : IsOpen U) (hT : T = S ∩ U)
    (hlocal : ∀ x ∈ S, ∃ D : OpenPartialHomeomorph X V3,
      x ∈ D.source ∧ (∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ D.source, y ∈ S ↔ ell (D y) = 0) ∧ Disjoint D.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ D.source, y ∈ S ↔ ell (D y) = 0 ∧ 0 ≤ psi (D y)) ∧
          ∀ y ∈ D.source, y ∈ M ↔ psi (D y) = 0)) :
    ∀ x ∈ T, ∃ D : OpenPartialHomeomorph X V3,
      x ∈ D.source ∧ (∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ D.source, y ∈ T ↔ ell (D y) = 0) ∧ Disjoint D.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ D.source, y ∈ T ↔ ell (D y) = 0 ∧ 0 ≤ psi (D y)) ∧
          ∀ y ∈ D.source, y ∈ M ↔ psi (D y) = 0) := by
  intro x hx
  have hxSU := hT.subset hx
  obtain ⟨D, hxD, hc, hk⟩ := hlocal x hxSU.1
  refine ⟨D.restrOpen U hU, ⟨hxD, hxSU.2⟩, ?_, ?_⟩
  · intro i
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hc i)).mono
      ((e i).symm.trans (D.restrOpen U hU)).open_source (fun _ hy => ⟨hy.1, hy.2.1⟩)
  · rcases hk with ⟨ell, v, hv, hs, hd⟩ | ⟨ell, psi, u, v, hu, hv, huv, hs, hm⟩
    · left
      refine ⟨ell, v, hv, ?_, hd.mono_left inter_subset_left⟩
      intro y hy
      change y ∈ T ↔ ell (D y) = 0
      rw [hT, mem_inter_iff, and_iff_left hy.2]
      exact hs y hy.1
    · right
      refine ⟨ell, psi, u, v, hu, hv, huv, ?_, fun y hy => hm y hy.1⟩
      intro y hy
      change y ∈ T ↔ ell (D y) = 0 ∧ 0 ≤ psi (D y)
      rw [hT, mem_inter_iff, and_iff_left hy.2]
      exact hs y hy.1

open Classical in
theorem exists_open_edge_component_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ U : Set E, IsOpen U ∧ K.space ∩ U = (K.edgeComponentComplex D).space := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let V (i : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) : Set K.space :=
    Subtype.val ⁻¹' (K.edgeComponentComplex i).space
  have hvcover : (⋃ i, V i) = univ := by
    ext z
    simp only [V, mem_iUnion, mem_preimage, mem_univ, iff_true]
    exact mem_iUnion.mp (K.iUnion_edgeComponentComplex_space.symm.subset z.property)
  have ho := (Dehn.isClopen_of_finite_disjoint_closed_cover V
    (fun i => ((K.edgeComponentComplex i).isCompact_space_of_finite
      (hK.subset (K.edgeComponentComplex_le i))).isClosed.preimage continuous_subtype_val)
    (fun i j hij => (K.pairwise_disjoint_edgeComponentComplex_space hij).preimage _)
    hvcover D).2
  obtain ⟨U, hU, heq⟩ := isOpen_induced_iff.mp ho
  refine ⟨U, hU, ?_⟩
  ext z
  constructor
  · rintro ⟨hzK, hzU⟩
    exact (congrArg (fun W : Set K.space => (⟨z, hzK⟩ : K.space) ∈ W) heq).mp hzU
  · intro hzD
    have hzK := SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D) hzD
    exact ⟨hzK, (congrArg (fun W : Set K.space => (⟨z, hzK⟩ : K.space) ∈ W) heq).mpr hzD⟩

end PoincareConjecture.M76
