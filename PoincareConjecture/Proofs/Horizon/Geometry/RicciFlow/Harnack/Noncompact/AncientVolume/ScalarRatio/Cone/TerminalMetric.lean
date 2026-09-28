import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.AncientLimit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow

theorem exists_terminal_metric_of_ancient_chart_limit
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (Fseq : ℕ → RicciFlow n M (Iic 0))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {ρ : ℝ} (U : Opens (EuclideanSpace ℝ (Fin n))) (hzeroU : 0 ∈ U)
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball 0 ρ)
    (F : RicciFlow n U (Iic 0))
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall 0 ρ))
    (hcoeff : ∀ (x : U) (v w : EuclideanSpace ℝ (Fin n)),
      (F.metric 0).inner x v w = B (0, x) v w)
    (hjet : ∀ r K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric z.1).pullbackCoefficients (Φ k) z.2)
          (Iic 0 ×ˢ closedBall 0 ρ))
        (iteratedFDerivWithin ℝ r B (Iic 0 ×ˢ closedBall 0 ρ)) atTop K) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g) (V : Opens (EuclideanSpace ℝ (Fin n))),
      0 ∈ V ∧ V ≤ U ∧
      (∀ x ∈ V, g.euclideanCoefficients x = B (0, x)) ∧
      (∀ (x : U), (x : EuclideanSpace ℝ (Fin n)) ∈ V → ∀ v w,
        (F.metric 0).inner x v w = g.inner (x : EuclideanSpace ℝ (Fin n)) v w) ∧
      ∀ K, IsCompact K → K ⊆ V →
        TendstoUniformlyOn (fun k => ((Fseq k).metric 0).pullbackCoefficients (Φ k))
          g.euclideanCoefficients atTop K := by
  have hslice : ContDiffOn ℝ ∞ (fun x => B (0, x)) U := by
    apply hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    exact fun x hx => ⟨by simp, ball_subset_closedBall (hU hx)⟩
  obtain ⟨g, D, V, hVo, hzeroV, hVU, heq⟩ :=
    RiemannianMetric.exists_local_realization U.isOpen hzeroU (fun x => B (0, x))
      hslice (fun x hx v w => by
        rw [← hcoeff ⟨x, hx⟩ v w, ← hcoeff ⟨x, hx⟩ w v]
        exact (F.metric 0).symm _ _ _)
      (fun x hx v hv => by
        rw [← hcoeff ⟨x, hx⟩ v v]
        exact (F.metric 0).pos _ v hv)
  refine ⟨g, D, ⟨V, hVo⟩, hzeroV, hVU, heq, ?_, ?_⟩
  · intro x hx v w
    rw [hcoeff]
    exact (congrArg (fun T => T v w) (heq x hx)).symm
  · intro K hK hKV
    let e : EuclideanSpace ℝ (Fin n) → ℝ × EuclideanSpace ℝ (Fin n) := fun x => (0, x)
    have hKe : IsCompact (e '' K) := hK.image (continuous_const.prodMk continuous_id)
    have hsubset : e '' K ⊆ Iic 0 ×ˢ closedBall 0 ρ := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by simp [e], ball_subset_closedBall (hU (hVU (hKV hx)))⟩
    have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
        (hjet 0 (e '' K) hKe hsubset)
    have hp := (hh.comp e).mono (subset_preimage_image e K)
    simp only [Function.comp_def, iteratedFDerivWithin_zero_apply, e] at hp
    exact hp.congr_right (fun x hx => (heq x (hKV hx)).symm)

end PoincareConjecture.RicciFlow
