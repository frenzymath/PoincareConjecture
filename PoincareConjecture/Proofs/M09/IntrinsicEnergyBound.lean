import PoincareConjecture.Proofs.M09.IntrinsicEnergy
import PoincareConjecture.Proofs.M09.GeometricEnergyBound








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem exists_uniform_regularizedCurveEnergy_exp_bound {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (b : ℝ) (hb : 0 < b) (hbmax : b < τmax) :
    ∃ A : ℝ, 0 < A ∧ ∀ (γ : ℝ → M) (U : Set ℝ) (h : ℝ),
      0 ≤ h → h < Real.sqrt b → IsOpen U → Set.Icc 0 h ⊆ U →
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U →
      ∀ E : ParametricAlongCurveExtensionOn (n := n) (Set.Icc 0 h) γ
        (curveVelocityWithin (n := n) γ (Set.Icc 0 h)),
      (∀ s ∈ Set.Icc 0 h, regularizedLGeodesicEquation F T γ (Set.Icc 0 h) E s) →
      ∀ s ∈ Set.Icc 0 h, regularizedCurveEnergy F T γ s + 1 ≤
        (regularizedCurveEnergy F T γ 0 + 1) * Real.exp (A * s) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_geometricEnergy_bound F hM04 T τmax
    hτmax hwindow hcurvature b hb.le hbmax
  refine ⟨A, hA, ?_⟩
  intro γ U h hh hhb hU hIU hγ E heq
  rcases eq_or_lt_of_le hh with hzero | hpos
  · intro s hs
    have hs0 : s = 0 := by linarith [hs.1, hs.2]
    simp only [hs0, mul_zero, Real.exp_zero, mul_one, le_refl]
  have hI : UniqueDiffOn ℝ (Set.Icc 0 h) := uniqueDiffOn_Icc hpos
  have hw : Set.Icc (T - b) T ⊆ J := by
    intro t ht
    exact hwindow ⟨by linarith [ht.1], ht.2⟩
  let e := regularizedCurveEnergy F T γ
  let e' : ℝ → ℝ := fun s ↦
    4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature
      (γ s) (curveVelocity γ s) -
      4 * s * (F.connection (T - s ^ 2)).ricci (γ s)
        (curveVelocity γ s) (curveVelocity γ s)
  have hd : ∀ s ∈ Set.Icc 0 h, HasDerivAt e (e' s) s := by
    intro s hs
    apply regularizedCurveEnergy_hasDerivAt F hM04 T b hb hw γ U (Set.Icc 0 h)
      hU hIU hI hγ E s hs
    · exact ⟨lt_of_lt_of_le (neg_lt_zero.mpr (Real.sqrt_pos.mpr hb)) hs.1,
        hs.2.trans_lt hhb⟩
    · exact heq s hs
  apply nonnegativeEnergy_exp_bound e e' h A hh hA.le
  · exact fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rcases eq_or_ne (curveVelocity (n := n) γ s) 0 with hv | hv
    · simp [e, regularizedCurveEnergy, hv]
    · exact ((F.metric (T - s ^ 2)).pos (γ s) (curveVelocity γ s) hv).le
  · exact fun s hs ↦ hd s ⟨hs.1, hs.2.le⟩
  · intro s hs
    exact hbound s ⟨hs.1, hs.2.le.trans hhb.le⟩ (γ s) (curveVelocity γ s)

end PoincareConjecture.Proofs.M09
