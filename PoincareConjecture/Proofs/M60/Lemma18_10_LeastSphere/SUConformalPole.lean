import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundMetric
import PoincareConjecture.Proofs.M60.Mathlib.ChartedDenseComplement










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m60WeaklyConformal_of_compl_singleton (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (p : UnitTwoSphere)
    (hoff : ∀ q, q ≠ p → ∃ s : ℝ, 0 ≤ s ∧ ∀ v w : TangentSpace (𝓡 2) q,
      g.inner (f q) (mfderiv (𝓡 2) (𝓡 n) f q v) (mfderiv (𝓡 2) (𝓡 n) f q w) =
        s * m60RoundSphereInner q v w) : M60WeaklyConformal g f := by
  intro q
  by_cases hqp : q = p
  · subst q
    let v₀ : TangentSpace (𝓡 2) p := EuclideanSpace.basisFun (Fin 2) ℝ 0
    let V₀ := FiberBundle.extend LoopPlane v₀
    have hV₀ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
        (fun q => (⟨q, V₀ q⟩ : TangentBundle (𝓡 2) UnitTwoSphere)) p :=
      FiberBundle.contMDiffAt_extend (𝓡 2) LoopPlane v₀
    let A : UnitTwoSphere → ℝ := fun q => M60.metricPullbackForm (n := 2) g f q (V₀ q) (V₀ q)
    let B : UnitTwoSphere → ℝ := fun q => m60RoundSphereMetric.inner q (V₀ q) (V₀ q)
    have hA : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ A p := by
      have h := (M60.metricPullbackForm_contMDiffAt g (hf p)).clm_bundle_apply₂
        (F₃ := ℝ) (E₃ := Bundle.Trivial UnitTwoSphere ℝ) hV₀ hV₀
      simpa using (Bundle.contMDiffAt_totalSpace.mp h).2
    have hB : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ B p := by
      have h := (m60RoundSphereMetric.contMDiff p).clm_bundle_apply₂
        (F₃ := ℝ) (E₃ := Bundle.Trivial UnitTwoSphere ℝ) hV₀ hV₀
      simpa using (Bundle.contMDiffAt_totalSpace.mp h).2
    have hBp : B p = 1 := by
      dsimp only [B, V₀]
      rw [FiberBundle.extend_apply_self, m60RoundSphereMetric_inner,
        m60RoundSphereInner_eq_inner]
      change inner ℝ (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 1
      simp only [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow]
    have hBne : B p ≠ 0 := by rw [hBp]; norm_num
    have hAp : 0 ≤ A p := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact real_inner_self_nonneg (x := mfderiv (𝓡 2) (𝓡 n) f p (V₀ p))
    refine ⟨A p, hAp, ?_⟩
    intro v w
    let V := FiberBundle.extend LoopPlane v
    let W := FiberBundle.extend LoopPlane w
    have hV : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
        (fun q => (⟨q, V q⟩ : TangentBundle (𝓡 2) UnitTwoSphere)) p :=
      FiberBundle.contMDiffAt_extend (𝓡 2) LoopPlane v
    have hW : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
        (fun q => (⟨q, W q⟩ : TangentBundle (𝓡 2) UnitTwoSphere)) p :=
      FiberBundle.contMDiffAt_extend (𝓡 2) LoopPlane w
    let L : UnitTwoSphere → ℝ := fun q => M60.metricPullbackForm (n := 2) g f q (V q) (W q)
    let R : UnitTwoSphere → ℝ := fun q => m60RoundSphereMetric.inner q (V q) (W q)
    have hL : ContinuousAt L p := by
      have h := (M60.metricPullbackForm_contMDiffAt g (hf p)).clm_bundle_apply₂
        (F₃ := ℝ) (E₃ := Bundle.Trivial UnitTwoSphere ℝ) hV hW
      exact (show ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ L p from
        by simpa using (Bundle.contMDiffAt_totalSpace.mp h).2).continuousAt
    have hR : ContinuousAt R p := by
      have h := (m60RoundSphereMetric.contMDiff p).clm_bundle_apply₂
        (F₃ := ℝ) (E₃ := Bundle.Trivial UnitTwoSphere ℝ) hV hW
      exact (show ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ R p from
        by simpa using (Bundle.contMDiffAt_totalSpace.mp h).2).continuousAt
    have hd : Dense ({p}ᶜ : Set UnitTwoSphere) :=
      M60.dense_compl_singleton_of_charted (H := LoopPlane) p
    let : NeBot (𝓝[≠] p) := mem_closure_iff_nhdsWithin_neBot.mp (hd p)
    have heq : L =ᶠ[𝓝[≠] p] (fun q => (A q / B q) * R q) := by
      filter_upwards [self_mem_nhdsWithin,
        (hB.continuousAt.eventually_ne hBne).filter_mono nhdsWithin_le_nhds] with q hq hBq
      obtain ⟨s, -, hs⟩ := hoff q hq
      have hscale : A q = s * B q := by
        simpa only [A, B, M60.metricPullbackForm_apply, m60RoundSphereMetric_inner]
          using hs (V₀ q) (V₀ q)
      have hpair : L q = s * R q := by
        simpa only [L, R, M60.metricPullbackForm_apply, m60RoundSphereMetric_inner]
          using hs (V q) (W q)
      rw [hpair, hscale, mul_div_cancel_right₀ s hBq]
    have hlim := tendsto_nhds_unique
      ((hL.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
      (((hA.continuousAt.div hB.continuousAt hBne).mul hR).tendsto.mono_left
        nhdsWithin_le_nhds)
    simpa only [Pi.mul_apply, Pi.div_apply, L, R, V, W, FiberBundle.extend_apply_self,
      M60.metricPullbackForm_apply, m60RoundSphereMetric_inner, hBp, div_one] using hlim
  · exact hoff q hqp

end PoincareConjecture
