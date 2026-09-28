import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCoreGraph
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLImageNeighborhood

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_compact_PL_neighborhood_model
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {A W : Set M} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ (s : Finset A) (F : M → (s → ℝ × E)) (C : Set M)
      (K : SimplicialComplex ℝ (s → ℝ × E)) (H : C ≃ₜ K.space),
      IsCompact C ∧ A ⊆ interior C ∧ C ⊆ W ∧ K.faces.Finite ∧
      Continuous F ∧ (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      (∀ x : C, (H x : s → ℝ × E) = F x) ∧
      ∀ x ∈ C, ∃ (i : ι) (V : Set M) (a : (s → ℝ × E) →ᴬ[ℝ] E),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  obtain ⟨s, c, Q, F, _, hQe, hAQ, hFc, hFPL, hproj, hsep⟩ :=
    exists_locallyPL_graph_separating_compact_core e hcompat hcover hA hW hAW
  let V : Set M := ⋃ i, interior (Q i)
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_interior)
  have hVQ : V ⊆ ⋃ i, Q i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, interior_subset hxi⟩
  have hVW : V ⊆ W := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hVQ hx)
    exact (hQe i hxi).2
  have hinj : InjOn F V := fun x hx _ _ hxy => hsep x (hVQ hx) _ hxy
  obtain ⟨C, K, H, hC, hAC, hCV, hK, _, hHF⟩ :=
    exists_compact_finitePL_image_neighborhood e F hFc hcover hFPL hA hV hAQ hinj
  refine ⟨s, F, C, K, H, hC, hAC, hCV.trans hVW, hK, hFc, hFPL, hHF, ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hCV hx)
  let a : (s → ℝ × E) →ᴬ[ℝ] E :=
    ((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.proj i)).toContinuousAffineMap
  refine ⟨c i, interior (Q i), a, isOpen_interior, hxi,
    fun y hy => (hQe i (interior_subset hy)).1, ?_⟩
  intro y hy
  exact congrArg Prod.snd (hproj i (interior_subset hy))

end OpenPartialHomeomorph
