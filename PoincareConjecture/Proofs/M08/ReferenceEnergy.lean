import PoincareConjecture.Proofs.M08.ActionBounds
import PoincareConjecture.Proofs.M08.RegularizedAction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle intervalIntegral Topology
open MeasureTheory

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem curveVelocity_continuousOn_open {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ I) :
    ContinuousOn (fun s ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n)) (γ s) (curveVelocity (n := n) γ s)) I := by
  let ι : ℝ → TangentBundle (𝓘(ℝ, ℝ)) ℝ :=
    (tangentBundleModelSpaceHomeomorph (𝓘(ℝ, ℝ))).symm ∘
      (fun s : ℝ ↦ (s, (1 : ℝ)))
  have hι : Continuous ι :=
    (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(ℝ, ℝ)) (n := ∞)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have ht := hγ.continuousOn_tangentMapWithin (by norm_num) hI.uniqueMDiffOn
  have hcomp := ht.comp hι.continuousOn (fun s hs ↦ hs)
  apply hcomp.congr
  intro s hs
  change Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s)
      (curveVelocity (n := n) γ s) =
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s)
      ((mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ I s) 1)
  rw [mfderivWithin_of_mem_nhds (hI.mem_nhds hs)]
  rfl

noncomputable def referenceSpeedSq (g : RiemannianMetric n M)
    (γ : ℝ → M) (s : ℝ) : ℝ :=
  g.inner (γ s) (curveVelocity (n := n) γ s) (curveVelocity (n := n) γ s)

theorem referenceSpeedSq_nonneg (g : RiemannianMetric n M)
    (γ : ℝ → M) (s : ℝ) : 0 ≤ referenceSpeedSq g γ s := by
  by_cases hv : curveVelocity (n := n) γ s = 0
  · simp [referenceSpeedSq, hv]
  · exact (g.pos (γ s) _ hv).le

theorem referenceSpeedSq_continuousOn {γ : ℝ → M} {I : Set ℝ}
    (g : RiemannianMetric n M) (hI : IsOpen I)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ I) :
    ContinuousOn (referenceSpeedSq g γ) I := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  have hv := curveVelocity_continuousOn_open hI hγ
  exact hv.inner_bundle hv

theorem referenceSpeedSq_le_evolving {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax K τ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Set.Icc (T - τmax) T, ∀ x : M,
      |(F.connection t).curvatureTensorNorm x| ≤ K)
    (hτ : τ ∈ Set.Icc 0 τmax) (γ : ℝ → M) :
    referenceSpeedSq (F.metric T) γ τ ≤
      Real.exp (2 * (n : ℝ) * K * τmax) * referenceSpeedSq (F.metric (T - τ)) γ τ := by
  have h := (backwardPath_metric_comparison hM04 hwindow le_rfl hτ.1 hτ.2 hK hbound
    (γ τ) (curveVelocity (n := n) γ τ)).2
  simp only [sub_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (referenceSpeedSq_nonneg _ _ _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hτ.2 (mul_nonneg (by positivity) hK)

theorem referenceWeightedEnergy_bound {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ K : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Set.Icc (T - τmax) T, ∀ x : M,
      |(F.connection t).curvatureTensorNorm x| ≤ K)
    (p : BackwardTimePath F T τ₁ τ₂) (hτ₂ : τ₂ ≤ τmax) :
    IntervalIntegrable (fun τ ↦ Real.sqrt τ * referenceSpeedSq (F.metric T) p.curve τ)
      volume τ₁ τ₂ ∧
    (∫ τ in τ₁..τ₂, Real.sqrt τ * referenceSpeedSq (F.metric T) p.curve τ) ≤
      Real.exp (2 * (n : ℝ) * K * τmax) *
        (backwardLLength F T τ₁ τ₂ p.curve +
          (Real.sqrt τ₂ * (n : ℝ) ^ 2 * K) * (τ₂ - τ₁)) := by
  let Q := Real.exp (2 * (n : ℝ) * K * τmax)
  let W := fun τ ↦ Real.sqrt τ * referenceSpeedSq (F.metric T) p.curve τ
  have hWnonneg (τ : ℝ) : 0 ≤ W τ :=
    mul_nonneg (Real.sqrt_nonneg _) (referenceSpeedSq_nonneg _ _ _)
  have hWbound (τ : ℝ) (hτ : τ ∈ Set.Icc τ₁ τ₂) :
      W τ ≤ Q * backwardLKinetic F T p.curve τ := by
    have h := mul_le_mul_of_nonneg_left
      (referenceSpeedSq_le_evolving hM04 hwindow hK hbound
        ⟨p.nonnegative.trans hτ.1, hτ.2.trans hτ₂⟩ p.curve) (Real.sqrt_nonneg τ)
    simpa only [W, backwardLKinetic, referenceSpeedSq, Q, mul_left_comm] using h
  have hmeas : AEStronglyMeasurable W (volume.restrict (Set.uIoc τ₁ τ₂)) := by
    rw [Set.uIoc_of_le p.ordered.le, ← restrict_Ioo_eq_restrict_Ioc]
    exact (Real.continuous_sqrt.continuousOn.mul
      (referenceSpeedSq_continuousOn (F.metric T) isOpen_Ioo p.regular)).aestronglyMeasurable
        measurableSet_Ioo
  have hk := (backwardLKinetic_intervalIntegrable hM04 p).const_mul Q
  have hW : IntervalIntegrable W volume τ₁ τ₂ := by
    apply hk.mono_fun' hmeas
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg τ)]
    apply hWbound
    simpa only [Set.uIcc_of_le p.ordered.le] using Set.uIoc_subset_uIcc hτ
  refine ⟨hW, ?_⟩
  calc
    (∫ τ in τ₁..τ₂, W τ) ≤ ∫ τ in τ₁..τ₂, Q * backwardLKinetic F T p.curve τ :=
      intervalIntegral.integral_mono_on p.ordered.le hW hk hWbound
    _ = Q * ∫ τ in τ₁..τ₂, backwardLKinetic F T p.curve τ :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (backwardLLength_coercive hM04 p hτ₂ hbound).2 (Real.exp_pos _).le

end PoincareConjecture.M08
