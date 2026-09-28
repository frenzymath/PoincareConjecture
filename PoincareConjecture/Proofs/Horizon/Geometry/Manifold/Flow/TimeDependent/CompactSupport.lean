import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.ProperControl
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ}

private theorem isProperMap_euclidean_norm_sq :
    IsProperMap (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨by fun_prop, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (|R| + 1)).of_isClosed_subset
    (hK.isClosed.preimage (by fun_prop))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq : ‖x‖ ^ 2 ≤ R := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖x‖))] using hR _ hx
  nlinarith [norm_nonneg x, abs_nonneg R, le_abs_self R]

theorem exists_smooth_global_timeDependentFlow_of_compact_spatial_support
    {J : Set ℝ} (hJ : IsOpen J) (hcJ : Convex ℝ J)
    {X : ℝ → (x : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × EuclideanSpace ℝ (Fin n) =>
        (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n))))
      (J ×ˢ univ))
    (hsupport : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ J →
      ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
        ∀ t ∈ Icc a b, ∀ x ∉ K, X t x = 0) :
    ∃ E : ℝ → ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ s ∈ J, ∀ x, E s s x = x) ∧
      (∀ s ∈ J, ContDiffOn ℝ ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => E s p.1 p.2) (J ×ˢ univ)) ∧
      (∀ s ∈ J, ∀ x, ∀ t ∈ J,
        HasDerivAt (fun r => E s r x) (X t (E s t x)) t) ∧
      (∀ s ∈ J, ∀ t ∈ J, ∀ r ∈ J, ∀ x, E t r (E s t x) = E s r x) ∧
      (∀ s ∈ J, ∀ t ∈ J, Function.LeftInverse (E t s) (E s t) ∧
        Function.RightInverse (E t s) (E s t)) := by
  have hcontrol : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ J → ∃ A : ℝ, 0 ≤ A ∧
      ∀ t ∈ Icc a b, ∀ x : EuclideanSpace ℝ (Fin n),
        |mvfderiv (𝓡 n) (fun y => ‖y‖ ^ 2) x (X t x)| ≤ A := by
    intro a b hab hsub
    obtain ⟨K, hK, hzero⟩ := hsupport a b hab hsub
    let g : ℝ × EuclideanSpace ℝ (Fin n) → ℝ :=
      fun p => 2 * inner ℝ p.2 (X p.1 p.2)
    have hinner : Continuous (fun v : TangentBundle (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) => inner ℝ v.1 v.2) := by
      exact (FiberBundle.continuous_proj _ _).inner
        (contMDiff_snd_tangentBundle_modelSpace
          (EuclideanSpace ℝ (Fin n)) (𝓡 n) (n := ∞)).continuous
    have hg : ContinuousOn g (Icc a b ×ˢ K) := by
      apply continuousOn_const.mul
      exact hinner.comp_continuousOn
        (hX.continuousOn.mono (Set.prod_mono hsub (subset_univ K)))
    obtain ⟨A, hA⟩ := ((isCompact_Icc.prod hK).image_of_continuousOn hg).isBounded.exists_norm_le
    refine ⟨max A 0, le_max_right _ _, ?_⟩
    intro t ht x
    have he : mvfderiv (𝓡 n) (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x
        (X t x) = g (t, x) := by
      simp only [mvfderiv, NormedSpace.fromTangentSpace, mfderiv_eq_fderiv,
        fderiv_norm_sq_apply]
      change (2 • (innerSL ℝ) x) (X t x) = 2 * inner ℝ x (X t x)
      simp [innerSL_apply_apply]
    rw [he]
    by_cases hx : x ∈ K
    · have hgx : ‖g (t, x)‖ ≤ A := hA _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      have hgx' : |g (t, x)| ≤ A := by simpa only [Real.norm_eq_abs] using hgx
      exact hgx'.trans (le_max_left _ _)
    · simp only [g, hzero t ht x hx, inner_zero_right, mul_zero, abs_zero]
      exact le_max_right _ _
  obtain ⟨E, hi, hs, ho, hc, hinv⟩ :=
    exists_smooth_global_timeDependentFlow_of_proper_control hJ hcJ hX
      (contDiff_norm_sq ℝ).contMDiff isProperMap_euclidean_norm_sq hcontrol
  refine ⟨E, hi, ?_, ?_, hc, hinv⟩
  · intro s hsJ
    have h := hs s hsJ
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  · intro s hsJ x t htJ
    exact hasDerivAt_iff_hasFDerivAt.mpr (ho s hsJ x t htJ).hasFDerivAt

end Poincare.Manifold
