import PoincareConjecture.Proofs.M76.Rigidity.EmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLMap.restrict_compact_domain
    {X Y ι κ : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph Y V3} {R N : Set X} {T : Set Y}
    {f : C(R, T)} (hf : ChartwisePLMap e d f)
    (he : PLDomain e N) (hN : IsCompact N) (hne : N.Nonempty) (hNR : N ⊆ R) :
    ChartwisePLMap e d (f.comp (ContinuousMap.inclusion hNR)) := by
  classical
  obtain ⟨s, _, K, _, H, g, _, _, _, hK, _, _, _, _, _, _, hgc, hgval, hgPL, _⟩ :=
    he.exists_original_frontier_surface_model hN hne
  let q : (s → ℝ × V3) → R := fun z => ⟨g z, hNR (g z).property⟩
  have hval : ContinuousOn (fun z => (g z : X)) K.space :=
    continuous_subtype_val.comp_continuousOn hgc
  have hqc : ContinuousOn q K.space := by
    apply Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
    exact hval
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space := hgPL
  have htarget := hf.polyhedralPLInCharts_comp K hK q hqc hqPL (fun _ _ => mem_univ _)
  have hg (z : K.space) : g z = H.symm z := Subtype.ext (hgval z)
  have hsurj : Function.Surjective (fun z : K.space => g z) := by
    intro x
    exact ⟨H x, (hg (H x)).trans (H.symm_apply_apply x)⟩
  have hgi : Topology.IsEmbedding (fun z : K.space => g z) := by
    have heq : (fun z : K.space => g z) = H.symm := funext hg
    rw [heq]
    exact H.symm.isEmbedding
  apply chartwisePLMap_of_embedded_polyhedral_parameters (E := s → ℝ × V3)
    e d he hf.target_domain (f.comp (ContinuousMap.inclusion hNR))
  intro x
  obtain ⟨z, hz⟩ := hsurj x
  exact ⟨K, g, z, hK, hgc, hgi, hz,
    hsurj.range_eq.symm ▸ Filter.univ_mem, hgPL, htarget⟩

end PoincareConjecture.M76
