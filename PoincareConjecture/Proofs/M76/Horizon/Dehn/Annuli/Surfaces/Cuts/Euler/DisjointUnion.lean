import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceCountInclusionExclusion

set_option autoImplicit false
open Set Geometry
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype β]

theorem surfaceEulerCount_disjoint_family
    (U : SimplicialComplex ℝ E) (L : β → SimplicialComplex ℝ E)
    (hL : ∀ i, (L i).faces.Finite)
    (hfaces : U.faces = ⋃ i, (L i).faces)
    (hdis : Pairwise (fun i j ↦ Disjoint (L i).space (L j).space)) :
    U.surfaceEulerCount = ∑ i, (L i).surfaceEulerCount := by
  classical
  have hU : U.faces.Finite := hfaces ▸ finite_iUnion hL
  have hfinset : hU.toFinset = Finset.univ.biUnion (fun i ↦ (hL i).toFinset) := by
    ext s
    simp [hfaces]
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset β) : Set β)
      (fun i ↦ (hL i).toFinset) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro s hi hj
    have hsi := (hL i).mem_toFinset.mp hi
    have hsj := (hL j).mem_toFinset.mp hj
    obtain ⟨v, hvs⟩ := (L i).nonempty_of_mem_faces hsi
    have hv : v ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ hvs
    exact Set.disjoint_left.mp (hdis hij)
      ((L i).convexHull_subset_space hsi hv) ((L j).convexHull_subset_space hsj hv)
  rw [U.surfaceEulerCount_eq_sum hU, hfinset, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro i _
  exact ((L i).surfaceEulerCount_eq_sum (hL i)).symm

end Geometry.SimplicialComplex
