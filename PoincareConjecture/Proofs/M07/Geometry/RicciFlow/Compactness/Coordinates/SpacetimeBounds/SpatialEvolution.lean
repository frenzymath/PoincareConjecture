import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Pullback
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.MixedDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.SpacetimeBounds

theorem exists_affine_spatialJet_evolution_bound
    (n q : ℕ) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {J : Set ℝ} (F : RicciFlow n M J), IsOpen J →
        ∀ {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        ∀ {t : ℝ}, t ∈ J → ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
        (∀ v, a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v) →
        (∀ v, (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ s ≤ q + 1, (F.connection t).curvatureDerivativeNorm s (e x) ≤ K s) →
        (∀ j, 1 ≤ j → j ≤ q →
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ A ^ j) →
        ‖deriv (fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x) t‖ ≤
          C * (1 + ‖iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients e) x‖) := by
  obtain ⟨C, hC, hric⟩ := exists_affine_pullback_ricci_component_jet_bound n q K hK ha hb A hA
  refine ⟨(n : ℝ) * n * (2 * C), by positivity, ?_⟩
  intro M _ _ _ J F hJ U hU e he hi t ht x hx hlower hupper hcurv hjets
  let B := fun z : ℝ × EuclideanSpace ℝ (Fin n) => (F.metric z.1).pullbackCoefficients e z.2
  have hB : ContDiffOn ℝ ∞ B (J ×ˢ U) := F.contDiffOn_pullbackCoefficients hJ hU he
  let k := fun y => deriv (fun s => B (s, y)) t
  have hk : ContDiffAt ℝ ∞ k x :=
    ((contDiffOn_timeDeriv hB hJ hU).contDiffAt (x := (t, x))
      ((hJ.prod hU).mem_nhds ⟨ht, hx⟩)).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hevol := hasDerivAt_spatialJet hB hJ hU ht
    (fun y hy => (F.differentiableAt_pullbackCoefficients_time hJ hU he ht hy).hasDerivAt)
    (q + 1) hx
  rw [hevol.deriv]
  have hcomponents (p r : Fin n) :
      ‖iteratedFDeriv ℝ (q + 1) (fun y => k y (EuclideanSpace.basisFun (Fin n) ℝ p)
        (EuclideanSpace.basisFun (Fin n) ℝ r)) x‖ ≤
        2 * C * (1 + ‖iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients e) x‖) := by
    let u := EuclideanSpace.basisFun (Fin n) ℝ p
    let v := EuclideanSpace.basisFun (Fin n) ℝ r
    let R := fun y => (F.connection t).ricci (e y)
      (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v)
    have hgerm : (fun y => k y u v) =ᶠ[𝓝 x] (fun y => -2 * R y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact F.deriv_pullbackCoefficients_apply hJ hU he ht hy u v
    have hscaled : R =ᶠ[𝓝 x] (fun y => (-1 / 2 : ℝ) * (k y u v)) := by
      filter_upwards [hgerm] with y hy
      rw [hy]
      ring
    have hR : ContDiffAt ℝ ∞ R x :=
      (contDiffAt_const.mul ((hk.clm_apply contDiffAt_const).clm_apply
        contDiffAt_const)).congr_of_eventuallyEq hscaled
    rw [(hgerm.iteratedFDeriv (𝕜 := ℝ) (q + 1)).eq_of_nhds]
    change ‖iteratedFDeriv ℝ (q + 1) (fun y => (-2 : ℝ) • R y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hR.of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_eq_abs]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hr := hric (F.connection t) hU he hi hx hlower hupper hcurv hjets p r
    calc
      _ ≤ 2 * (C * (1 + ‖iteratedFDeriv ℝ (q + 1)
          ((F.metric t).pullbackCoefficients e) x‖)) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = _ := by ring
  have h := norm_iteratedFDeriv_bilinear_le_of_components
    (EuclideanSpace.basisFun (Fin n) ℝ) hk (q + 1) hcomponents
  apply h.trans_eq
  ring

end PoincareConjecture.SpacetimeBounds
