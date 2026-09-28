import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityLevels
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCharge

set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

theorem exists_nonzero_cut_level_charge_bound
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    {s₀ s₁ r t₀ t₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (A : E →ᵃ[ℝ] ℝ) (hcut : s₀ ∩ s₁ ⊆ {x | A x = 0})
    {c : ℝ} (hc : c ≠ 0)
    (hsection : (s₀ ∪ s₁) ∩ {x | A x = c} = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r))
    (e₀ : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ t₀) (he₀ : e₀.IsFinitePL)
    (e₁ : (s₁ ∩ {x | A x = c} : Set E) ≃ₜ t₁) (he₁ : e₁.IsFinitePL) :
    ∃ (I : Set ι) (f₀ f₁ : E → E)
      (N₀ : I → ℕ) (Q₀ : ∀ i, Polygon E (N₀ i + 3))
      (N₁ : (Iᶜ : Set ι) → ℕ) (Q₁ : ∀ i, Polygon E (N₁ i + 3)),
      (∀ x : (s₀ ∩ {x | A x = c} : Set E), (e₀ x : E) = f₀ x) ∧
      (∀ x : (s₁ ∩ {x | A x = c} : Set E), (e₁ x : E) = f₁ x) ∧
      (∀ i, Function.Injective (Q₀ i) ∧ (Q₀ i).HasSimplicialEdges ∧
        (Q₀ i).boundary ℝ = f₀ '' (P i).boundary ℝ) ∧
      (∀ i, Function.Injective (Q₁ i) ∧ (Q₁ i).HasSimplicialEdges ∧
        (Q₁ i).boundary ℝ = f₁ '' (P i).boundary ℝ) ∧
      t₀ = f₀ '' (r ∩ s₀) ∪ ⋃ i, (Q₀ i).boundary ℝ ∧
      t₁ = f₁ '' (r ∩ s₁) ∪ ⋃ i, (Q₁ i).boundary ℝ ∧
      Pairwise (fun i j => (Q₀ i).boundary ℝ ∩ (Q₀ j).boundary ℝ ⊆ f₀ '' (r ∩ s₀)) ∧
      Pairwise (fun i j => (Q₁ i).boundary ℝ ∩ (Q₁ j).boundary ℝ ⊆ f₁ '' (r ∩ s₁)) ∧
      alexanderCurveCount (fun i => (Q₀ i).boundary ℝ) +
        alexanderCurveCount (fun i => (Q₁ i).boundary ℝ) ≤
        alexanderCurveCount (fun i => (P i).boundary ℝ) := by
  obtain ⟨I, hI, hIc, _, ⟨f₀, N₀, Q₀, _, hrep₀, hQ₀, hcover₀, hpair₀⟩,
      ⟨f₁, N₁, Q₁, _, hrep₁, hQ₁, hcover₁, hpair₁⟩⟩ :=
    exists_nonzero_cut_level_family_transport n P hPe hPi hs₀ hs₁ A hcut hc
      hsection hpair e₀ he₀ e₁ he₁
  have hPlevel (i : ι) : (P i).boundary ℝ ⊆ {x | A x = c} := by
    intro x hx
    exact (hsection.symm.subset (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))).2
  have hcount₀ : alexanderCurveCount (fun i => (Q₀ i).boundary ℝ) =
      alexanderCurveCount (fun i : I => (P i).boundary ℝ) := by
    calc
      alexanderCurveCount (fun i => (Q₀ i).boundary ℝ) =
          alexanderCurveCount (fun i : I => f₀ '' (P i).boundary ℝ) :=
        congrArg alexanderCurveCount (funext (fun i => (hQ₀ i).2.2))
      _ = alexanderCurveCount (fun i : I => (P i).boundary ℝ) :=
        e₀.alexanderCurveCount_image (fun i : I => (P i).boundary ℝ)
          (fun i x hx => ⟨hI i i.property hx, hPlevel i hx⟩) f₀ hrep₀
  have hcount₁ : alexanderCurveCount (fun i => (Q₁ i).boundary ℝ) =
      alexanderCurveCount (fun i : (Iᶜ : Set ι) => (P i).boundary ℝ) := by
    calc
      alexanderCurveCount (fun i => (Q₁ i).boundary ℝ) =
          alexanderCurveCount (fun i : (Iᶜ : Set ι) => f₁ '' (P i).boundary ℝ) :=
        congrArg alexanderCurveCount (funext (fun i => (hQ₁ i).2.2))
      _ = alexanderCurveCount (fun i : (Iᶜ : Set ι) => (P i).boundary ℝ) :=
        e₁.alexanderCurveCount_image (fun i : (Iᶜ : Set ι) => (P i).boundary ℝ)
          (fun i x hx => ⟨hIc i i.property hx, hPlevel i hx⟩) f₁ hrep₁
  refine ⟨I, f₀, f₁, N₀, Q₀, N₁, Q₁, hrep₀, hrep₁, hQ₀, hQ₁,
    hcover₀, hcover₁, hpair₀, hpair₁, ?_⟩
  rw [hcount₀, hcount₁]
  exact alexanderCurveCount_partition_le (fun i => (P i).boundary ℝ) I

end Polygon
