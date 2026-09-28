import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinFlowEquation
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricCoefficients
import PoincareConjecture.Proofs.M28.Mathlib.TimeJetsWithin
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetPostcompose

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_of_bilinear_within_spacetime_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M)
    (hJ : UniqueDiffOn ℝ J) (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hjets : ∀ (x : M) (r : ℕ)
      (K : Set (ℝ × EuclideanSpace ℝ (Fin n))), IsCompact K →
      K ⊆ J ×ˢ (extChartAt (𝓡 n) x).target → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2)
          (J ×ˢ (extChartAt (𝓡 n) x).target))
        (iteratedFDerivWithin ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            (g p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2)
          (J ×ˢ (extChartAt (𝓡 n) x).target)) atTop K) :
    ∃ F : RicciFlow n M J, F.metric = g := by
  let B (G : ℝ → RiemannianMetric n M) (x : M)
      (p : ℝ × EuclideanSpace ℝ (Fin n)) :=
    (G p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2
  have hsmooth (G : ℝ → RiemannianMetric n M)
      (hG : RiemannianMetric.IsSmoothFamilyOn G J) (x : M) :
      ContDiffOn ℝ ∞ (B G x) (J ×ˢ (extChartAt (𝓡 n) x).target) :=
    hG.contDiffOn_spacetime_pullbackCoefficients_within (isOpen_extChartAt_target x)
      (fun y hy => contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy)
  have hread (x : M)
      (L : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ)
      (r : ℕ) (K : Set (ℝ × EuclideanSpace ℝ (Fin n)))
      (hK : IsCompact K) (hKS : K ⊆ J ×ˢ (extChartAt (𝓡 n) x).target) :=
    (hjets x r K hK hKS).iteratedFDerivWithin_postcompose L
      (hJ.prod (isOpen_extChartAt_target x).uniqueDiffOn) hKS
      (Eventually.of_forall fun k => hsmooth (Fseq k).metric (Fseq k).smooth x)
      (hsmooth g hg x)
      (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  apply exists_of_within_coordinate_jets Fseq g hJ hg
  · intro t ht x r _ a b
    let L : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ b)).comp
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (EuclideanSpace.basisFun (Fin n) ℝ a))
    have hK : {(t, extChartAt (𝓡 n) x x)} ⊆
        J ×ˢ (extChartAt (𝓡 n) x).target :=
      singleton_subset_iff.mpr ⟨ht, mem_extChartAt_target x⟩
    have h := (hread x L r _ isCompact_singleton hK).iteratedFDeriv_spatial_slice
      hJ (isOpen_extChartAt_target x) hK
      (Eventually.of_forall fun k =>
        L.contDiff.comp_contDiffOn (hsmooth (Fseq k).metric (Fseq k).smooth x))
      (L.contDiff.comp_contDiffOn (hsmooth g hg x))
      (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
    simpa only [L, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using
      h.tendsto_at (mem_singleton (t, extChartAt (𝓡 n) x x))
  · intro t ht x u v
    let c := extChartAt (𝓡 n) x
    let p := c x
    have hp : c.symm p = x := c.left_inv (mem_extChartAt_source x)
    have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm p).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) (mem_extChartAt_target x)
    obtain ⟨e, he⟩ := hi
    let L : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (e.symm v)).comp
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (e.symm u))
    have heval (G : ℝ → RiemannianMetric n M) (s : ℝ) :
        L (B G x (s, p)) = (G s).inner x u v := by
      change (G s).inner (c.symm p)
        (mfderiv (𝓡 n) (𝓡 n) c.symm p (e.symm u))
        (mfderiv (𝓡 n) (𝓡 n) c.symm p (e.symm v)) = _
      rw [← he]
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      exact congrArg (fun y : M => (G s).inner y u v) hp
    have hK : {(t, p)} ⊆ J ×ˢ (extChartAt (𝓡 n) x).target :=
      singleton_subset_iff.mpr ⟨ht, mem_extChartAt_target x⟩
    have h := (hread x L 1 _ isCompact_singleton hK).derivWithin_time_slice
      hJ (isOpen_extChartAt_target x) hK
      (Eventually.of_forall fun k =>
        L.contDiff.comp_contDiffOn (hsmooth (Fseq k).metric (Fseq k).smooth x))
      (L.contDiff.comp_contDiffOn (hsmooth g hg x))
    have hpoint := h.tendsto_at (mem_singleton (t, p))
    change Tendsto
      (fun k => derivWithin (fun s => L (B (Fseq k).metric x (s, p))) J t) atTop
      (𝓝 (derivWithin (fun s => L (B g x (s, p))) J t)) at hpoint
    simpa only [heval] using hpoint

end PoincareConjecture.RicciFlow
