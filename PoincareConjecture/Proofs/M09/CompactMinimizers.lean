import PoincareConjecture.Proofs.M09.ReducedLengthUpperSemicontinuity
import PoincareConjecture.Proofs.M09.MinimizingInitialVectors
import PoincareConjecture.Proofs.M09.ExponentialAction

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

theorem lExponentialFamily_isCompact_minimizers {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p)
    (K : Set (TangentSpace (𝓡 n) p × ℝ)) (hK : IsCompact K)
    (hKt : K ⊆ Set.univ ×ˢ Set.Ioo 0 τmax) :
    IsCompact {z : TangentSpace (𝓡 n) p × ℝ | z ∈ K ∧
      ∃ (ht : 0 < z.2) (hmax : z.2 < τmax),
        IsMinimizingBackwardLPath F T 0 z.2 (A.path z.1 z.2 ht hmax)} := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let Φ : TangentSpace (𝓡 n) p × ℝ → M × ℝ := fun z ↦ (A.gamma z.1 z.2, z.2)
  let a : TangentSpace (𝓡 n) p × ℝ → ℝ := fun z ↦ A.action z.1 z.2 / (2 * Real.sqrt z.2)
  have hΦ : ContinuousOn Φ K :=
    (A.gamma_smooth.continuousOn.mono hKt).prodMk continuous_snd.continuousOn
  have ha : ContinuousOn a K :=
    ((lExponentialFamily_action_contDiffOn hM04 hτmax hwindow A).continuousOn.mono hKt).div
      (continuous_const.mul (Real.continuous_sqrt.comp continuous_snd)).continuousOn
      (fun z hz ↦ (mul_pos zero_lt_two (Real.sqrt_pos.mpr (hKt hz).2.1)).ne')
  have hl : UpperSemicontinuousOn
      (fun z : TangentSpace (𝓡 n) p × ℝ ↦ reducedLength F T p (A.gamma z.1 z.2) z.2) K :=
    (reducedLength_upperSemicontinuousOn F hM04 T τmax hτmax hwindow hL p).comp hΦ
      (fun z hz ↦ ⟨Set.mem_univ _, (hKt hz).2⟩)
  let g : TangentSpace (𝓡 n) p × ℝ → ℝ := fun z ↦
    reducedLength F T p (A.gamma z.1 z.2) z.2 + -a z
  have hg : UpperSemicontinuousOn g K := hl.add ha.neg.upperSemicontinuousOn
  have heq : K ∩ g ⁻¹' Set.Ici 0 =
      {z : TangentSpace (𝓡 n) p × ℝ | z ∈ K ∧
        ∃ (ht : 0 < z.2) (hmax : z.2 < τmax),
          IsMinimizingBackwardLPath F T 0 z.2 (A.path z.1 z.2 ht hmax)} := by
    ext z
    constructor
    · rintro ⟨hz, hgap⟩
      have ht := (hKt hz).2
      have hle := lExponentialFamily_reducedLength_le_action hL A z.1 z.2 ht.1 ht.2
      have hvalue : reducedLength F T p (A.gamma z.1 z.2) z.2 =
          A.action z.1 z.2 / (2 * Real.sqrt z.2) := by
        change 0 ≤ reducedLength F T p (A.gamma z.1 z.2) z.2 +
          -(A.action z.1 z.2 / (2 * Real.sqrt z.2)) at hgap
        linarith
      exact ⟨hz, ht.1, ht.2,
        (lExponentialFamily_reducedLength_eq_action_iff hL A z.1 z.2 ht.1 ht.2).mp hvalue⟩
    · rintro ⟨hz, ht, hmax, hmin⟩
      have hvalue := (lExponentialFamily_reducedLength_eq_action_iff hL A z.1 z.2 ht hmax).mpr hmin
      refine ⟨hz, ?_⟩
      change 0 ≤ reducedLength F T p (A.gamma z.1 z.2) z.2 +
        -(A.action z.1 z.2 / (2 * Real.sqrt z.2))
      rw [hvalue]
      exact (add_neg_cancel _).ge
  exact heq ▸ hg.isCompact_inter_preimage_Ici hK 0

end PoincareConjecture.Proofs.M09
