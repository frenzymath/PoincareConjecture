import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCut
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityTransport
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import Mathlib.SetTheory.Cardinal.Finite











set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]





theorem exists_nonzero_cut_level_family_transport
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    {s₀ s₁ r t₀ t₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (A : E →ᵃ[ℝ] ℝ) (hcut : s₀ ∩ s₁ ⊆ {x | A x = 0})
    {c : ℝ} (hc : c ≠ 0)
    (hsection : (s₀ ∪ s₁) ∩ {x | A x = c} = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r))
    (e₀ : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ t₀) (he₀ : e₀.IsFinitePL)
    (e₁ : (s₁ ∩ {x | A x = c} : Set E) ≃ₜ t₁) (he₁ : e₁.IsFinitePL) :
    ∃ I : Set ι,
      (∀ i ∈ I, (P i).boundary ℝ ⊆ s₀) ∧
      (∀ i ∉ I, (P i).boundary ℝ ⊆ s₁) ∧
      Nat.card I + Nat.card (Iᶜ : Set ι) = Nat.card ι ∧
      (∃ (f : E → E) (N : I → ℕ) (Q : ∀ i, Polygon E (N i + 3)),
        FinitePiecewiseAffineOn f (s₀ ∩ {x | A x = c}) ∧
        (∀ x : (s₀ ∩ {x | A x = c} : Set E), (e₀ x : E) = f x) ∧
        (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges ∧
          (Q i).boundary ℝ = f '' (P i).boundary ℝ) ∧
        t₀ = f '' (r ∩ s₀) ∪ ⋃ i, (Q i).boundary ℝ ∧
        Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ f '' (r ∩ s₀))) ∧
      (∃ (f : E → E) (N : (Iᶜ : Set ι) → ℕ) (Q : ∀ i, Polygon E (N i + 3)),
        FinitePiecewiseAffineOn f (s₁ ∩ {x | A x = c}) ∧
        (∀ x : (s₁ ∩ {x | A x = c} : Set E), (e₁ x : E) = f x) ∧
        (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges ∧
          (Q i).boundary ℝ = f '' (P i).boundary ℝ) ∧
        t₁ = f '' (r ∩ s₁) ∪ ⋃ i, (Q i).boundary ℝ ∧
        Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ f '' (r ∩ s₁))) := by
  classical
  have hpre (i : ι) : IsPreconnected ((P i).boundary ℝ) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hPe i) (hPi i)
    exact (isConnected_iff_connectedSpace.mpr
      (e.connectedSpace_iff.mpr inferInstance)).isPreconnected
  have hPsection (i : ι) : (P i).boundary ℝ ⊆ (s₀ ∪ s₁) ∩ {x | A x = c} := by
    intro x hx
    exact hsection.symm.subset (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
  have hPinter (i : ι) : (P i).boundary ℝ ∩ (s₀ ∩ s₁) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hc ((hPsection i hx.1).2.symm.trans (hcut hx.2))
  obtain ⟨I, h₀, h₁, hI₀, hI₁⟩ := exists_connected_cut_partition hs₀ hs₁
    (fun i => (P i).boundary ℝ) hpre (fun i x hx => (hPsection i hx).1) hPinter
  have hs₀section : s₀ ∩ {x | A x = c} =
      (r ∩ s₀) ∪ ⋃ i : I, (P i).boundary ℝ := by
    calc
      s₀ ∩ {x | A x = c} = ((s₀ ∪ s₁) ∩ {x | A x = c}) ∩ s₀ := by
        ext x
        simp only [mem_inter_iff, mem_union]
        tauto
      _ = (r ∩ s₀) ∪ ⋃ i : I, (P i).boundary ℝ := by
        rw [hsection, union_inter_distrib_right, hI₀]
  have hs₁section : s₁ ∩ {x | A x = c} =
      (r ∩ s₁) ∪ ⋃ i : (Iᶜ : Set ι), (P i).boundary ℝ := by
    calc
      s₁ ∩ {x | A x = c} = ((s₀ ∪ s₁) ∩ {x | A x = c}) ∩ s₁ := by
        ext x
        simp only [mem_inter_iff, mem_union]
        tauto
      _ = (r ∩ s₁) ∪ ⋃ i : (Iᶜ : Set ι), (P i).boundary ℝ := by
        rw [hsection, union_inter_distrib_right, hI₁]
  have hpair₀ : Pairwise (fun i j : I =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r ∩ s₀) := by
    intro i j hij x hx
    exact ⟨hpair (fun h => hij (Subtype.ext h)) hx, (h₀ i i.property).1 hx.1⟩
  have hpair₁ : Pairwise (fun i j : (Iᶜ : Set ι) =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r ∩ s₁) := by
    intro i j hij x hx
    exact ⟨hpair (fun h => hij (Subtype.ext h)) hx, (h₁ i i.property).1 hx.1⟩
  refine ⟨I, fun i hi => (h₀ i hi).1, fun i hi => (h₁ i hi).1, ?_, ?_, ?_⟩
  · rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.Set.sumCompl I)
  · exact exists_finitePL_image_family (fun i : I => n i) (fun i => P i)
      (fun i => hPe i) (fun i => hPi i) hs₀section hpair₀ e₀ he₀
  · exact exists_finitePL_image_family (fun i : (Iᶜ : Set ι) => n i) (fun i => P i)
      (fun i => hPe i) (fun i => hPi i) hs₁section hpair₁ e₁ he₁

end Polygon
