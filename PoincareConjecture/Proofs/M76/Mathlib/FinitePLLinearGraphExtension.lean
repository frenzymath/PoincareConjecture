import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGraphEndpointExtension
import PoincareConjecture.Proofs.M76.Mathlib.LinearPatchHomeomorphisms

set_option autoImplicit false

open Set

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_finitePL_marked_graph_with_linear_ends {ι : Type*} [Finite ι]
    (S : ι → Set E) (T : ι → Set F) (d : ι → Bool → Set E)
    (a : Bool → E) (A : Bool → F) (c : ι → Bool → E)
    (L : Bool → E ≃L[ℝ] F)
    (hS : ∀ i, IsFinitePLBallPair ℝ (S i) {a false, a true})
    (hT : ∀ i, IsFinitePLBallPair ℝ (T i) {A false, A true})
    (hSi : Pairwise (fun i j => S i ∩ S j = {a false, a true}))
    (hTi : Pairwise (fun i j => T i ∩ T j = {A false, A true}))
    (hd : ∀ i j, IsFinitePLBallPair ℝ (d i j) {a j, c i j})
    (hds : ∀ i j, d i j ⊆ S i)
    (hDt : ∀ i j, L j '' d i j ⊆ T i)
    (ha : a false ≠ a true) (hA : A false ≠ A true)
    (hac : ∀ i j, a j ≠ c i j)
    (hdis : ∀ i, Disjoint (d i false) (d i true))
    (hDis : ∀ i, Disjoint (L false '' d i false) (L true '' d i true))
    (hLa : ∀ j, L j (a j) = A j) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i j (x : d i j),
        (H ⟨x, mem_iUnion.mpr ⟨i, hds i j x.property⟩⟩ : F) = L j x) ∧
      (∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i) ∧
      (∀ x : ⋃ i, S i, (H x : F) = A false ↔ (x : E) = a false) ∧
      (∀ x : ⋃ i, S i, (H x : F) = A true ↔ (x : E) = a true) ∧
      ∀ i j (x : ⋃ i, S i), (x : E) ∈ d i j ↔ (H x : F) ∈ L j '' d i j := by
  let D : ι → Bool → Set F := fun i j => L j '' d i j
  let C : ι → Bool → F := fun i j => L j (c i j)
  let e : ∀ i j, d i j ≃ₜ D i j := fun i j => (L j).toHomeomorph.image (d i j)
  have hD (i : ι) (j : Bool) : IsFinitePLBallPair ℝ (D i j) {A j, C i j} := by
    simpa only [D, C, image_pair, hLa j] using
      ((hd i j).linear_image_patch_data (L j)).1
  have he (i : ι) (j : Bool) : (e i j).IsFinitePL :=
    ((hd i j).linear_image_patch_data (L j)).2.1
  have hAC (i : ι) (j : Bool) : A j ≠ C i j := by
    intro h
    exact hac i j ((L j).injective ((hLa j).trans h))
  have hea (i : ι) (j : Bool) :
      (e i j ⟨a j, (hd i j).1 (Or.inl rfl)⟩ : F) = A j := hLa j
  have hec (i : ι) (j : Bool) :
      (e i j ⟨c i j, (hd i j).1 (Or.inr rfl)⟩ : F) = C i j := rfl
  obtain ⟨H, hH, hkeep, hpieces, hfalse, htrue⟩ :=
    exists_finitePL_marked_graph_with_end_intervals S T d D a A c C
      hS hT hSi hTi hd hD hds hDt ha hA hac hAC hdis hDis e he hea hec
  refine ⟨H, hH, hkeep, hpieces, hfalse, htrue, ?_⟩
  intro i j
  exact H.mem_subset_iff_of_extension (e i j)
    ((hds i j).trans (subset_iUnion S i)) ((hDt i j).trans (subset_iUnion T i))
    (fun x => Subtype.ext (hkeep i j x))

end Set
