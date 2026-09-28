import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Transition
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Comparison.Jets.ComparisonCoordinateJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem exists_finite_transition_jet_bound_at
    {ι : Type*} {f : ι → E → E} (x : ι → E)
    {A B : ι → E → ChristoffelSpace E}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (x i))
    (hB : ∀ i, ContDiffAt ℝ ∞ (B i) (f i (x i)))
    (m : ℕ)
    (hAj : ∃ C : ℝ, ∀ i j, j ≤ m → ‖iteratedFDeriv ℝ j (A i) (x i)‖ ≤ C)
    (hBj : ∃ C : ℝ, ∀ i j, j ≤ m → ‖iteratedFDeriv ℝ j (B i) (f i (x i))‖ ≤ C)
    (hzero : ∃ C : ℝ, ∀ i, ‖f i (x i)‖ ≤ C)
    (hfirst : ∃ C : ℝ, ∀ i, ‖fderiv ℝ (f i) (x i)‖ ≤ C)
    (hEq : ∀ i, ∀ᶠ y in 𝓝 (x i),
      fderiv ℝ (fderiv ℝ (f i)) y =
        transitionHessianPolynomial (A i y, (B i (f i y), fderiv ℝ (f i) y))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i j, j ≤ m + 2 →
      ‖iteratedFDeriv ℝ j (f i) (x i)‖ ≤ C := by
  obtain ⟨CA, hCA⟩ := hAj
  obtain ⟨CB, hCB⟩ := hBj
  obtain ⟨C₀, hC₀⟩ := hzero
  obtain ⟨C₁, hC₁⟩ := hfirst
  let D := fun i => fderiv ℝ (f i)
  have hD (i : ι) : ContDiffAt ℝ ∞ (D i) (x i) :=
    (hf i).fderiv_right (m := ∞) (by simp)
  have hDj : ∀ n, n ≤ m + 1 → ∃ C : ℝ, 1 ≤ C ∧
      ∀ i j, j ≤ n → ‖iteratedFDeriv ℝ j (D i) (x i)‖ ≤ C := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨max C₁ 1, le_max_right _ _, ?_⟩
        intro i j hj
        have : j = 0 := by omega
        subst j
        simpa only [norm_iteratedFDeriv_zero] using (hC₁ i).trans (le_max_left C₁ 1)
    | succ n ih =>
        intro hn
        have hnm : n ≤ m := by omega
        obtain ⟨C, hC, hCj⟩ := ih (by omega)
        let Q := max C (max C₀ 1)
        have hQ : 1 ≤ Q := (le_max_right C₀ 1).trans (le_max_right C (max C₀ 1))
        have hfj (i : ι) (j : ℕ) (hj : j ≤ n) :
            ‖iteratedFDeriv ℝ j (f i) (x i)‖ ≤ Q := by
          cases j with
          | zero =>
              simpa only [norm_iteratedFDeriv_zero] using
                (hC₀ i).trans ((le_max_left C₀ 1).trans (le_max_right C (max C₀ 1)))
          | succ j =>
              rw [← norm_iteratedFDeriv_fderiv]
              exact (hCj i j (by omega)).trans (le_max_left _ _)
        let CB' := max CB 0
        have hCB' : 0 ≤ CB' := le_max_right _ _
        let T := max 1 (max CA (max (n.factorial * CB' * Q ^ n) C))
        have hT : 1 ≤ T := le_max_left _ _
        have hCT : C ≤ T :=
          (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
        have hCAT : CA ≤ T := (le_max_left _ _).trans (le_max_right _ _)
        let p := fun i y => (A i y, (B i (f i y), D i y))
        have hps (i : ι) : ContDiffAt ℝ ∞ (p i) (x i) :=
          (hA i).prodMk (((hB i).comp (x i) (hf i)).prodMk (hD i))
        have hpj (i : ι) (j : ℕ) (hj : j ≤ n) :
            ‖iteratedFDeriv ℝ j (p i) (x i)‖ ≤ T := by
          have hBj' : ‖iteratedFDeriv ℝ j (B i ∘ f i) (x i)‖ ≤
              n.factorial * CB' * Q ^ n := by
            apply (MetricSurgery.norm_iteratedFDeriv_comp_uniform_at (hf i) (hB i) j hQ
              (fun l hl => (hCB i l ((hl.trans hj).trans hnm)).trans (le_max_left _ _))
              (fun l _ hl => hfj i l (hl.trans hj))).trans
            gcongr
          have hsB : ContDiffAt ℝ ∞ (fun y => B i (f i y)) (x i) :=
            (hB i).comp (x i) (hf i)
          have hjtop : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
          have hprod₁ := iteratedFDeriv_prodMk (hA i) (hsB.prodMk (hD i)) hjtop
          have hprod₂ := iteratedFDeriv_prodMk hsB (hD i) hjtop
          change ‖iteratedFDeriv ℝ j (fun y => (A i y, (B i (f i y), D i y))) (x i)‖ ≤ T
          have hnorm₁ := ContinuousMultilinearMap.opNorm_prod
            (G := ChristoffelSpace E) (G' := ChristoffelSpace E × (E →L[ℝ] E))
            (iteratedFDeriv ℝ j (A i) (x i))
            (iteratedFDeriv ℝ j (fun y => (B i (f i y), D i y)) (x i))
          have hnorm₂ := ContinuousMultilinearMap.opNorm_prod
            (G := ChristoffelSpace E) (G' := E →L[ℝ] E)
            (iteratedFDeriv ℝ j (fun y => B i (f i y)) (x i))
            (iteratedFDeriv ℝ j (D i) (x i))
          rw [hprod₁, hnorm₁, hprod₂, hnorm₂]
          exact max_le ((hCA i j (hj.trans hnm)).trans hCAT)
            (max_le (hBj'.trans ((le_max_left _ _).trans
              ((le_max_right _ _).trans (le_max_right _ _)))) ((hCj i j hj).trans hCT))
        let H := ChristoffelSpace E × (ChristoffelSpace E × (E →L[ℝ] E))
        let : ProperSpace H := FiniteDimensional.proper ℝ H
        obtain ⟨L, hL, hLj⟩ := MetricSurgery.exists_compact_local_jet_bound
          (isCompact_closedBall (0 : H) T)
          (fun _ _ => contDiff_transitionHessianPolynomial.contDiffAt) n
        have hpball (i : ι) : p i (x i) ∈ Metric.closedBall (0 : H) T := by
          rw [Metric.mem_closedBall, @dist_zero_right H _ (p i (x i))]
          simpa only [norm_iteratedFDeriv_zero] using
            hpj i 0 (Nat.zero_le n)
        let Cnew := max C (n.factorial * L * T ^ n)
        refine ⟨Cnew, hC.trans (le_max_left _ _), ?_⟩
        intro i j hj
        by_cases hjn : j ≤ n
        · exact (hCj i j hjn).trans (le_max_left _ _)
        have heqj : j = n + 1 := by omega
        subst j
        have he : fderiv ℝ (D i) =ᶠ[𝓝 (x i)]
            (fun y => transitionHessianPolynomial (p i y)) := hEq i
        rw [← norm_iteratedFDeriv_fderiv, (he.iteratedFDeriv ℝ n).self_of_nhds]
        have hb := MetricSurgery.norm_iteratedFDeriv_comp_uniform_at (hps i)
          contDiff_transitionHessianPolynomial.contDiffAt n hT
          (fun l hl => hLj l hl (p i (x i)) (hpball i))
          (fun l _ hl => hpj i l hl)
        exact hb.trans (le_max_right _ _)
  obtain ⟨C, hC, hCj⟩ := hDj (m + 1) le_rfl
  refine ⟨max C C₀, hC.trans (le_max_left _ _), ?_⟩
  intro i j hj
  cases j with
  | zero =>
      simpa only [norm_iteratedFDeriv_zero] using (hC₀ i).trans (le_max_right C C₀)
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv]
      exact (hCj i j (by omega)).trans (le_max_left _ _)

end PoincareConjecture.CoordinateTransition
