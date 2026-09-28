import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PartitionedGraphWalkPaths
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLIntervalImageGraph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPaths

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem FinitePiecewiseAffineOn.exists_image_graph_walk
    {f : ℝ → E} (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1)) :
    ∃ (K : SimplicialComplex ℝ E) (hzero : f 0 ∈ K.vertices) (hone : f 1 ∈ K.vertices)
      (hm : MapsTo f (Icc (0 : ℝ) 1) K.space),
      K.faces.Finite ∧ K.space = f '' Icc (0 : ℝ) 1 ∧
      (∀ s ∈ K.faces, s.card ≤ 2) ∧
      ∃ w : K.vertexAbstractComplex.edgeGraph.Walk ⟨f 0, hzero⟩ ⟨f 1, hone⟩,
        (K.geometricWalkPath w).Homotopic
          (Path.intervalIn K.space f hf.continuousOn hm) := by
  classical
  obtain ⟨n, t, ht, ht0, ht1, hformula⟩ := hf.exists_interval_partition_four
  have hparam (i : Fin (n + 4)) : t i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le i)
    · rw [← ht1]
      exact ht.monotone (Fin.le_last i)
  let P : Finset E := Finset.univ.image (fun i => f (t i))
  have hP : (P : Set E) ⊆ f '' Icc (0 : ℝ) 1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact mem_image_of_mem f (hparam i)
  obtain ⟨K, hK, hspace, hdim, hvertices⟩ := hf.exists_interval_image_graph P hP
  have hv (i : Fin (n + 4)) : f (t i) ∈ K.vertices :=
    hvertices (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hzero : f 0 ∈ K.vertices := congrArg f ht0 ▸ hv 0
  have hone : f 1 ∈ K.vertices := congrArg f ht1 ▸ hv (Fin.last (n + 3))
  have hm : MapsTo f (Icc (0 : ℝ) 1) K.space := fun x hx =>
    hspace.symm.subset (mem_image_of_mem f hx)
  refine ⟨K, hzero, hone, hm, hK, hspace, hdim, ?_⟩
  exact K.exists_partitioned_geometric_walk hK hdim f hf.continuousOn hm hzero hone
    (n := n + 2) t ht ht0 ht1 hv hformula

end Geometry
