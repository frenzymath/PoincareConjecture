import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.RegularCuts
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas



noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Analysis.Calculus.Morse



theorem exists_isolating_cut_radius {A : Set Real} (hA : A.Finite) (c : Real) :
    ∃ R : Real, 0 < R ∧ ∀ k ∈ A, k ≠ c -> R < |k - c| := by
  have hc : c ∈ (A \ {c})ᶜ := by simp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    hA.sdiff.isClosed.isOpen_compl c hc
  refine ⟨ε / 2, by positivity, ?_⟩
  intro k hk hkc
  have hd : ε ≤ dist k c := by
    by_contra! hlt
    exact (hball hlt) ⟨hk, hkc⟩
  rw [Real.dist_eq] at hd
  linarith



theorem exists_isolating_cut_radius_with_closed_heights
    {A B : Set Real} (hA : A.Finite) (hB : IsClosed B) (c : Real) (hc : c ∉ B) :
    ∃ R : Real, 0 < R ∧ (∀ k ∈ A, k ≠ c -> R < |k - c|) ∧
      ∀ k ∈ B, R < |k - c| := by
  have hclosed : IsClosed ((A \ {c}) ∪ B) := hA.sdiff.isClosed.union hB
  have hout : c ∈ ((A \ {c}) ∪ B)ᶜ := by simp [hc]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl c hout
  have hfar (k : Real) (hk : k ∈ (A \ {c}) ∪ B) : ε / 2 < |k - c| := by
    have hd : ε ≤ dist k c := by
      by_contra! hlt
      exact (hball hlt) hk
    rw [Real.dist_eq] at hd
    linarith
  exact ⟨ε / 2, by positivity, fun k hk hkc => hfar k (Or.inl ⟨hk, hkc⟩),
    fun k hk => hfar k (Or.inr hk)⟩

end Poincare.Analysis.Calculus.Morse
