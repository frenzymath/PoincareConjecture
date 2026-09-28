import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions









set_option autoImplicit false

open Set Geometry

namespace Set.Finite



theorem exists_finite_geometric_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : S.Finite) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = S := by
  classical
  let : Finite S := hS.to_subtype
  obtain ⟨K, hK, hKs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
      (fun x : S => ({(x : E)} : Finset E))
      (fun _ => affineIndependent_of_subsingleton ℝ _)
  refine ⟨K, hK, hKs.trans ?_⟩
  simp only [Finset.coe_singleton, convexHull_singleton]
  ext y
  simp

end Set.Finite

namespace Geometry




theorem polyhedralPLInCharts_of_finite
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (f : E → X) {S : Set E} (hS : S.Finite) :
    PolyhedralPLInCharts e f S := by
  classical
  let : Finite S := hS.to_subtype
  refine ⟨hS.continuousOn f, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover (f x)
  obtain ⟨J, hJ, hJs⟩ := (finite_singleton (x : E)).exists_finite_geometric_carrier
  have hJx {y : E} (hy : y ∈ J.space) : y = x := by
    simpa only [hJs, mem_singleton_iff] using hy
  refine ⟨i, J, {x}, hJ, ?_, isOpen_discrete _, mem_singleton x, ?_, ?_, ?_⟩
  · intro y hy
    rw [hJx hy]
    exact x.property
  · rintro _ ⟨y, hy, rfl⟩
    rcases mem_singleton_iff.mp hy with rfl
    rw [hJs]
    exact mem_singleton _
  · intro y hy
    rw [hJx hy]
    exact hi
  · apply ((J.affineOnFaces_affine
      (ContinuousAffineMap.const ℝ E (e i (f x)))).finitePiecewiseAffineOn hJ).congr
    intro y hy
    change e i (f x) = e i (f y)
    rw [hJx hy]

end Geometry
