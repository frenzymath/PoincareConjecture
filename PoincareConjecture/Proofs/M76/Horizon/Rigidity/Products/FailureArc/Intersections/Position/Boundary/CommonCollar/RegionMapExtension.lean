import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

noncomputable def extendRegionMap {X : Type*} {R : Set X} (G : R → R) (x : X) : X := by
  classical
  exact if hx : x ∈ R then G ⟨x, hx⟩ else x

theorem extendRegionMap_apply {X : Type*} {R : Set X} (G : R → R) (x : R) :
    extendRegionMap G x = (G x : X) := by
  classical
  simp only [extendRegionMap, dif_pos x.property]

theorem extendRegionMap_injective {X : Type*} {R : Set X} {G : R → R}
    (hG : Function.Injective G) : Function.Injective (extendRegionMap G) := by
  classical
  intro x y h
  by_cases hx : x ∈ R <;> by_cases hy : y ∈ R
  · simp only [extendRegionMap, dif_pos hx, dif_pos hy] at h
    exact congrArg Subtype.val (hG (Subtype.ext h))
  · simp only [extendRegionMap, dif_pos hx, dif_neg hy] at h
    exact (hy (h ▸ (G ⟨x, hx⟩).property)).elim
  · simp only [extendRegionMap, dif_neg hx, dif_pos hy] at h
    exact (hx (h.symm ▸ (G ⟨y, hy⟩).property)).elim
  · simpa only [extendRegionMap, dif_neg hx, dif_neg hy] using h

theorem ChartwisePLMap.polyhedralPLInCharts_extendRegionMap
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    {G : C(R, R)} (hG : ChartwisePLMap e e G)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (x₀ : R) (f : E → X) (hf : PolyhedralPLInCharts e f K.space)
    (hfR : MapsTo f K.space R) :
    PolyhedralPLInCharts e (extendRegionMap G ∘ f) K.space := by
  classical
  let q (z : E) : R := if hz : z ∈ K.space then ⟨f z, hfR hz⟩ else x₀
  have hqval (z : E) (hz : z ∈ K.space) : (q z : X) = f z := by
    simp only [q, dif_pos hz]
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space :=
    hf.congr (fun z hz => (hqval z hz).symm)
  have hq : ContinuousOn q K.space :=
    IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  apply (hG.polyhedralPLInCharts_comp K hK q hq hqPL (mapsTo_univ _ _)).congr
  intro z hz
  rw [Function.comp_apply, ← hqval z hz, extendRegionMap_apply]

end PoincareConjecture.M76
