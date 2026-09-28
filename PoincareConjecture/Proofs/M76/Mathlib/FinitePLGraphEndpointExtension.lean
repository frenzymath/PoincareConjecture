import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalEndpointExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedGraphGluing

set_option autoImplicit false

open Set

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_finitePL_marked_graph_with_end_intervals {ι : Type*} [Finite ι]
    (S : ι → Set E) (T : ι → Set F)
    (d : ι → Bool → Set E) (D : ι → Bool → Set F)
    (a : Bool → E) (A : Bool → F) (c : ι → Bool → E) (C : ι → Bool → F)
    (hS : ∀ i, IsFinitePLBallPair ℝ (S i) {a false, a true})
    (hT : ∀ i, IsFinitePLBallPair ℝ (T i) {A false, A true})
    (hSi : Pairwise (fun i j => S i ∩ S j = {a false, a true}))
    (hTi : Pairwise (fun i j => T i ∩ T j = {A false, A true}))
    (hd : ∀ i j, IsFinitePLBallPair ℝ (d i j) {a j, c i j})
    (hD : ∀ i j, IsFinitePLBallPair ℝ (D i j) {A j, C i j})
    (hds : ∀ i j, d i j ⊆ S i) (hDt : ∀ i j, D i j ⊆ T i)
    (ha : a false ≠ a true) (hA : A false ≠ A true)
    (hac : ∀ i j, a j ≠ c i j) (hAC : ∀ i j, A j ≠ C i j)
    (hdis : ∀ i, Disjoint (d i false) (d i true))
    (hDis : ∀ i, Disjoint (D i false) (D i true))
    (e : ∀ i j, d i j ≃ₜ D i j) (he : ∀ i j, (e i j).IsFinitePL)
    (hea : ∀ i j, (e i j ⟨a j, (hd i j).1 (Or.inl rfl)⟩ : F) = A j)
    (hec : ∀ i j, (e i j ⟨c i j, (hd i j).1 (Or.inr rfl)⟩ : F) = C i j) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i j (x : d i j),
        (H ⟨x, mem_iUnion.mpr ⟨i, hds i j x.property⟩⟩ : F) = e i j x) ∧
      (∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i) ∧
      (∀ x : ⋃ i, S i, (H x : F) = A false ↔ (x : E) = a false) ∧
      (∀ x : ⋃ i, S i, (H x : F) = A true ↔ (x : E) = a true) := by
  classical
  choose f hf hkeep _ hends using fun i =>
    (hS i).exists_extension_of_disjoint_end_intervals
      (d i) (D i) a (c i) A (C i) (hT i) (hd i) (hD i) (hds i) (hDt i)
      ha hA (hac i) (hAC i) (hdis i) (hDis i) (e i) (he i) (hea i) (hec i)
  obtain ⟨H, hH, hHkeep, hpieces, haH, hbH⟩ :=
    exists_finitePL_marked_graph_of_maps S T
      (fun i => hds i false ((hd i false).1 (Or.inl rfl)))
      (fun i => hds i true ((hd i true).1 (Or.inl rfl)))
      hSi hTi f hf (fun i => hends i false) (fun i => hends i true)
  refine ⟨H, hH, ?_, hpieces, haH, hbH⟩
  intro i j x
  exact (hHkeep i ⟨x, hds i j x.property⟩).trans
    (congrArg (fun y : T i => (y : F)) (hkeep i j x))

end Set
