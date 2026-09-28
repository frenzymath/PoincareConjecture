import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLGraphCover
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPLProduct











set_option autoImplicit false

open Set Geometry Topology

namespace OpenPartialHomeomorph

variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_locallyPL_closedEmbedding_with_core_coordinates
    {ι : Type*} [Fintype ι] (e : ι → OpenPartialHomeomorph M E)
    (Q : ι → Set M)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hQ : ∀ i, IsCompact (Q i)) (hQe : ∀ i, Q i ⊆ (e i).source)
    (hcover : ∀ x : M, ∃ i, x ∈ Q i) :
    ∃ F : M → (ι → ℝ × E), IsClosedEmbedding F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      ∀ i, EqOn (fun x => F x i) (fun x => (1, e i x)) (Q i) := by
  classical
  choose f C hC hCe hfcont hfzero hfeq hfbound hfrecover hfPL using
    fun i => (e i).exists_compactly_supported_PL_graph_block (hQ i) (hQe i)
  let F : M → (ι → ℝ × E) := fun x i => f i x
  have hFcont : Continuous F := continuous_pi hfcont
  have hFinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨i, hxi⟩ := hcover x
    have hblock : f i x = f i y := congrFun hxy i
    have hfx : f i x = (1, e i x) := hfeq i hxi
    have hfy : (f i y).1 = 1 := by rw [← hblock, hfx]
    obtain ⟨hye, hycoord⟩ := hfrecover i y hfy
    apply (e i).injOn (hQe i hxi) hye
    have hcoord := congrArg Prod.snd hblock
    simpa only [hfx, hycoord] using hcoord
  refine ⟨F, hFcont.isClosedEmbedding hFinj, ?_, hfeq⟩
  intro i
  exact LocallyPiecewiseAffineOn.pi (e i).open_target
    (fun j => hfPL j (e i) (hcompat i j))





theorem exists_locallyPL_closedEmbedding_of_compact_cores
    {ι : Type*} [Fintype ι] (e : ι → OpenPartialHomeomorph M E)
    (Q : ι → Set M)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hQ : ∀ i, IsCompact (Q i)) (hQe : ∀ i, Q i ⊆ (e i).source)
    (hcover : ∀ x : M, ∃ i, x ∈ Q i) :
    ∃ F : M → (ι → ℝ × E), IsClosedEmbedding F ∧
      ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target := by
  obtain ⟨F, hF, hFPL, _⟩ := exists_locallyPL_closedEmbedding_with_core_coordinates
    e Q hcompat hQ hQe hcover
  exact ⟨F, hF, hFPL⟩

end OpenPartialHomeomorph

namespace ChartedSpace

variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M]





theorem exists_finite_locallyPL_embedding_with_chart_projections
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening
      (M := M) (E := E)) :
    ∃ (s : Finset (OpenPartialHomeomorph M E))
      (F : M → (s → ℝ × E)) (U : s → Set M), IsClosedEmbedding F ∧
      (∀ i : s, LocallyPiecewiseAffineOn
        (F ∘ (i : OpenPartialHomeomorph M E).symm)
        (i : OpenPartialHomeomorph M E).target) ∧
      (∀ i, IsOpen (U i)) ∧
      (∀ i, U i ⊆ (i : OpenPartialHomeomorph M E).source) ∧
      (∀ x : M, ∃ i, x ∈ U i) ∧
      (∀ i, EqOn (fun x => (F x i).2) (i : OpenPartialHomeomorph M E) (U i)) := by
  classical
  obtain ⟨s, Q, hcompat, hQ, hQs, hcover⟩ :=
    exists_finite_compact_PL_chart_cover_with_interiors hlocal
  have hQcover (x : M) : ∃ i, x ∈ Q i := by
    obtain ⟨i, hxi⟩ := hcover x
    exact ⟨i, interior_subset hxi⟩
  obtain ⟨F, hF, hFPL, hFQ⟩ :=
    OpenPartialHomeomorph.exists_locallyPL_closedEmbedding_with_core_coordinates
      (fun i : s => (i : OpenPartialHomeomorph M E)) Q hcompat hQ hQs hQcover
  refine ⟨s, F, fun i => interior (Q i), hF, hFPL, fun _ => isOpen_interior,
    fun i => interior_subset.trans (hQs i), hcover, ?_⟩
  intro i x hx
  exact congrArg Prod.snd (hFQ i (interior_subset hx))




theorem exists_finite_locallyPL_embedding
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening
      (M := M) (E := E)) :
    ∃ (s : Finset (OpenPartialHomeomorph M E))
      (F : M → (s → ℝ × E)), IsClosedEmbedding F ∧
      (∀ i : s, LocallyPiecewiseAffineOn
        (F ∘ (i : OpenPartialHomeomorph M E).symm)
        (i : OpenPartialHomeomorph M E).target) ∧
      (∀ x : M, ∃ i : s, x ∈ (i : OpenPartialHomeomorph M E).source) := by
  classical
  obtain ⟨s, Q, hcompat, hQ, hQe, hcover⟩ :=
    exists_finite_compact_PL_chart_cover hlocal
  obtain ⟨F, hF, hFPL⟩ :=
    OpenPartialHomeomorph.exists_locallyPL_closedEmbedding_of_compact_cores
      (fun i : s => (i : OpenPartialHomeomorph M E)) Q hcompat hQ hQe hcover
  refine ⟨s, F, hF, hFPL, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := hcover x
  exact ⟨i, hQe i hxi⟩

end ChartedSpace
