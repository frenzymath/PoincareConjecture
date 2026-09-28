import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.ClosedCompactness

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff BigOperators

namespace PoincareConjecture.M30

theorem exists_smooth_subsequence_on_closed_convex_of_eventually
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y]
    {Ω : Set X} (hclosed : IsClosed Ω) (hconvex : Convex ℝ Ω)
    (hne : (interior Ω).Nonempty) (f : ℕ → X → Y)
    (hf : ∀ᶠ k : ℕ in atTop, ContDiffOn ℝ ∞ (f k) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f k) Ω x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : X → Y, ContDiffOn ℝ ∞ F Ω ∧
      ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f (σ k)) Ω)
        (iteratedFDerivWithin ℝ m F Ω) atTop K := by
  classical
  have hunique := uniqueDiffOn_convex hconvex hne
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  let f' := fun k => f (max k N)
  have hf' (k : ℕ) : ContDiffOn ℝ ∞ (f' k) Ω := hN _ (le_max_right k N)
  have heq : ∀ᶠ k : ℕ in atTop, f' k = f k :=
    (eventually_ge_atTop N).mono fun k hk => congrArg f (max_eq_left hk)
  have hbound' (K : Set X) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k x, x ∈ K → ‖iteratedFDerivWithin ℝ m (f' k) Ω x‖ ≤ B := by
    obtain ⟨B, hB, hevent⟩ := hbound K hK hKΩ m
    obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
    have hfinite (k : Fin M) : ∃ C : ℝ, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f' k) Ω x‖ ≤ C :=
      hK.exists_bound_of_continuousOn
        (((hf' k).continuousOn_iteratedFDerivWithin
          (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)) hunique).mono hKΩ)
    choose C hC using hfinite
    let D := ∑ k : Fin M, max (C k) 0
    have hD : 0 ≤ D := Finset.sum_nonneg fun k _ => le_max_right (C k) 0
    refine ⟨max B D, le_max_of_le_left hB, ?_⟩
    intro k x hx
    by_cases hk : M ≤ k
    · exact (hM (max k N) (hk.trans (le_max_left k N)) x hx).trans (le_max_left B D)
    · have hkM : k < M := lt_of_not_ge hk
      have hCD : C ⟨k, hkM⟩ ≤ D :=
        (le_max_left (C ⟨k, hkM⟩) 0).trans
          (Finset.single_le_sum (fun i _ => le_max_right (C i) 0)
            (Finset.mem_univ (⟨k, hkM⟩ : Fin M)))
      exact (hC ⟨k, hkM⟩ x hx).trans (hCD.trans (le_max_right B D))
  obtain ⟨σ, hσ, F, hF, hjets⟩ :=
    Poincare.AncientVolume.exists_smooth_subsequence_on_closed_convex
      hclosed hconvex hne f' hf' hbound'
  refine ⟨σ, hσ, F, hF, ?_⟩
  intro m K hK hKΩ
  exact (hjets m K hK hKΩ).congr
    ((hσ.tendsto_atTop.eventually heq).mono fun k hk x _ => by rw [hk])

end PoincareConjecture.M30
