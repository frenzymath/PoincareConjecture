import PoincareConjecture.Proofs.M76.Dehn.OriginalFaceDiskState
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Construction












set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Qrim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}







theorem Step.exists_original_disk_face_history
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R)
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j D)
    (hji : IsEmbedding (fun x : D => j x))
    (hjR : MapsTo j D (t.projection ⁻¹' R))
    (hproper : ∀ x : D, j x ∈ frontier (t.projection ⁻¹' R) ↔ (x : V2) ∈ Qrim)
    (hjF : ∀ x : Qrim, t.projection (j x) ∈ Fmark) :
    ∃ (W : Set M) (K A : SimplicialComplex ℝ V2),
      IsOpen W ∧ Fmark = frontier R ∩ W ∧
      K.faces.Finite ∧ K.space = D ∧ A.faces.Finite ∧ A ≤ K ∧ A.space = Qrim ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ A.vertices) → a ∈ A.faces) ∧
      ∃ (n : ℕ) (order : Fin n → K.faces),
        Function.Bijective order ∧
        (∀ i k, (order k).val ⊂ (order i).val → k < i) ∧
        (∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces) ∧
        ∃ P : ℕ → SimplicialComplex ℝ V2,
          (∀ k, (P k).faces.Finite ∧ P k ≤ K ∧
            (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a}) ∧
          (P 0).space = ∅ ∧ (P n).space = K.space ∧ Monotone P ∧
          ∃ (boundary : Fin n → Bool)
            (Q : Fin n → OpenPartialHomeomorph t.Carrier V3)
            (B : Fin n → OpenPartialHomeomorph s.Carrier V3)
            (J : Fin n → SimplicialComplex ℝ V3) (U : K.faces → Set t.Carrier),
            (∀ i, boundary i = true ↔ (order i).val ∈ A.faces) ∧
            (∀ i : Fin n,
              (P (i.val + 1)).space = (P i.val).space ∪
                convexHull ℝ ((order i).val : Set V2)) ∧
            (∀ i : Fin n,
              (boundary i = true → (P (i.val + 1)).space ⊆ Qrim) ∧
              (boundary i = false → Qrim ⊆ (P i.val).space)) ∧
            (∀ i, InjOn (step.projection ∘ step.inclusion) (Q i).source ∧
              (∀ k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid V3) ∧
              (∀ k, (s.charts k).symm.trans (B i) ∈ piecewiseAffineGroupoid V3) ∧
              (Q i).target = (B i).target ∧
              (∀ y, Q i y = B i (step.projection (step.inclusion y))) ∧
              MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source ∧
              EqOn ((step.projection ∘ step.inclusion) ∘ (Q i).symm)
                (B i).symm (B i).target ∧
              (J i).faces.Finite ∧ Convex ℝ (J i).space ∧ (J i).space ⊆ (Q i).target ∧
              (boundary i = true → (Q i).source ⊆ t.projection ⁻¹' W) ∧
              ((B i).source ⊆ interior (s.projection ⁻¹' R) ∨
                ∃ ell : V3 →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
                  (∀ y ∈ (B i).source,
                    y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B i y)) ∧
                  ∀ y ∈ (B i).source,
                    y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B i y) = 0)) ∧
            (∀ a, IsOpen (U a)) ∧
            (∀ i, U (order i) ⊆ (Q i).source ∩ (Q i) ⁻¹' interior (J i).space) ∧
            ∃ states : ℕ → FaceDiskState t K U R Fmark,
              (states 0).map = j ∧
              (∀ i (hi : i < n),
                ∃ motion : FaceMotionData step K (P i) (P (i + 1)) (states i).map
                  (Q ⟨i, hi⟩) (B ⟨i, hi⟩) (J ⟨i, hi⟩) U R Fmark (boundary ⟨i, hi⟩),
                  (states (i + 1)).map = motion.ambient 1 ∘ (states i).map) ∧
              (∀ i k, i ≤ k → k ≤ n →
                EqOn (states k).map (states i).map (P i).space) ∧
              ∀ a : K.faces, InjOn ((step.projection ∘ step.inclusion) ∘ (states n).map)
                (convexHull ℝ (a.val : Set V2)) := by
  obtain ⟨K₀, A₀, hK₀, hK₀s, hA₀, hA₀K₀, hA₀s, _, _⟩ :=
    SimplicialComplex.exists_marked_square_face_cover (fun _ : Unit => (univ : Set D))
      (fun _ => isOpen_univ) (fun _ => ⟨(), mem_univ _⟩)
  have history :=
    step.exists_marked_surface_normalization_history K₀ A₀ hK₀ hA₀
      (SimplicialComplex.space_subset_of_le hA₀K₀) he hF hopen
      (by rw [hK₀s]; exact hj) (by rw [hK₀s]; exact hji)
      (by rw [hK₀s]; exact hjR) (by rw [hK₀s, hA₀s]; exact hproper)
      (by rw [hA₀s]; exact hjF)
  rw [hK₀s, hA₀s] at history
  exact history

end Geometry.OriginalPLTower
