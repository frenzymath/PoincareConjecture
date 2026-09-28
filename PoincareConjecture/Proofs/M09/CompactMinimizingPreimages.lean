import PoincareConjecture.Proofs.M09.BoundedMinimizingVectors
import PoincareConjecture.Proofs.M09.CompactMinimizers

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem lExponentialFamily_isCompact_minimizing_preimage {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p)
    (Q : Set (M × ℝ)) (hQ : IsCompact Q) (hQt : Q ⊆ Set.univ ×ˢ Set.Ioo 0 τmax) :
    IsCompact {z : TangentSpace (𝓡 n) p × ℝ |
      ∃ (ht : 0 < z.2) (hmax : z.2 < τmax), (A.gamma z.1 z.2, z.2) ∈ Q ∧
        IsMinimizingBackwardLPath F T 0 z.2 (A.path z.1 z.2 ht hmax)} := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  rcases Q.eq_empty_or_nonempty with hzero | hnonempty
  · simpa only [hzero, Set.mem_empty_iff_false, false_and, exists_false,
      Set.ofPred_false] using (isCompact_empty : IsCompact (∅ : Set (TangentSpace (𝓡 n) p × ℝ)))
  obtain ⟨za, hza, hmin⟩ := hQ.exists_isMinOn hnonempty continuous_snd.continuousOn
  obtain ⟨zb, hzb, hmax⟩ := hQ.exists_isMaxOn hnonempty continuous_snd.continuousOn
  obtain ⟨R, _, hR⟩ := lExponentialFamily_minimizing_initial_bounded F hM04 T τmax hτmax
    hwindow hcurvature hL p A Q hQ hQt
  let K := Metric.closedBall (0 : TangentSpace (𝓡 n) p) R ×ˢ Set.Icc za.2 zb.2
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKt : K ⊆ Set.univ ×ˢ Set.Ioo 0 τmax := by
    intro z hz
    exact ⟨Set.mem_univ _, (hQt hza).2.1.trans_le hz.2.1,
      hz.2.2.trans_lt (hQt hzb).2.2⟩
  let S := {z : TangentSpace (𝓡 n) p × ℝ | z ∈ K ∧
    ∃ (ht : 0 < z.2) (hm : z.2 < τmax),
      IsMinimizingBackwardLPath F T 0 z.2 (A.path z.1 z.2 ht hm)}
  have hS : IsCompact S := lExponentialFamily_isCompact_minimizers F hM04 T τmax
    hτmax hwindow hL p A K hK hKt
  let Φ : TangentSpace (𝓡 n) p × ℝ → M × ℝ := fun z ↦ (A.gamma z.1 z.2, z.2)
  have hΦ : ContinuousOn Φ S :=
    (A.gamma_smooth.continuousOn.mono (fun z hz ↦ hKt hz.1)).prodMk continuous_snd.continuousOn
  have hSQ : IsCompact (S ∩ Φ ⁻¹' Q) :=
    hS.of_isClosed_subset (hΦ.preimage_isClosed_of_isClosed hS.isClosed hQ.isClosed)
      Set.inter_subset_left
  have heq : S ∩ Φ ⁻¹' Q = {z : TangentSpace (𝓡 n) p × ℝ |
      ∃ (ht : 0 < z.2) (hm : z.2 < τmax), (A.gamma z.1 z.2, z.2) ∈ Q ∧
        IsMinimizingBackwardLPath F T 0 z.2 (A.path z.1 z.2 ht hm)} := by
    ext z
    constructor
    · rintro ⟨⟨_, ht, hm, hpath⟩, hzQ⟩
      exact ⟨ht, hm, hzQ, hpath⟩
    · rintro ⟨ht, hm, hzQ, hpath⟩
      have hnorm : ‖z.1‖ ≤ R := by
        rw [norm_eq_sqrt_real_inner]
        exact hR z.1 z.2 ht hm hzQ hpath
      refine ⟨⟨?_, ht, hm, hpath⟩, hzQ⟩
      exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm,
        hmin hzQ, hmax hzQ⟩
  exact heq ▸ hSQ

end PoincareConjecture.Proofs.M09
