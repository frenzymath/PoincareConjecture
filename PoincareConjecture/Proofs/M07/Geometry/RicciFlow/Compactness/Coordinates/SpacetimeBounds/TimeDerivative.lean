import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.Perturbation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


theorem differentiableAt_pullbackCoefficients_time (F : RicciFlow n M J)
    (hJ : IsOpen J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    DifferentiableAt ℝ (fun s => (F.metric s).pullbackCoefficients e x) t := by
  have hs := (F.contDiffOn_pullbackCoefficients hJ hU he).contDiffAt (x := (t, x))
    ((hJ.prod hU).mem_nhds ⟨ht, hx⟩)
  exact (hs.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)


theorem deriv_pullbackCoefficients_apply (F : RicciFlow n M J)
    (hJ : IsOpen J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (u v : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => (F.metric s).pullbackCoefficients e x) t u v =
      -2 * (F.connection t).ricci (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x u) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
  have hd := F.differentiableAt_pullbackCoefficients_time hJ hU he ht hx
  have hv := (hd.hasDerivAt.clm_apply (hasDerivAt_const t u)).clm_apply
    (hasDerivAt_const t v)
  have hv' : HasDerivAt (fun s => (F.metric s).pullbackCoefficients e x u v)
      (deriv (fun s => (F.metric s).pullbackCoefficients e x) t u v) t := by
    simpa using hv
  exact hv'.unique ((F.equation t ht (e x) _ _).hasDerivAt (hJ.mem_nhds ht))



theorem norm_deriv_pullbackCoefficients_le [T2Space M] (F : RicciFlow n M J)
    (hJ : IsOpen J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {b K : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hupper : ∀ v, (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : (F.connection t).curvatureTensorNorm (e x) ≤ K) :
    ‖deriv (fun s => (F.metric s).pullbackCoefficients e x) t‖ ≤
      2 * (n : ℝ) ^ 3 * K * b := by
  have hd := F.differentiableAt_pullbackCoefficients_time hJ hU he ht hx
  have happ (u v : EuclideanSpace ℝ (Fin n)) :
      HasDerivAt (fun s => (F.metric s).pullbackCoefficients e x u v)
        (deriv (fun s => (F.metric s).pullbackCoefficients e x) t u v) t := by
    simpa using (hd.hasDerivAt.clm_apply (hasDerivAt_const t u)).clm_apply
      (hasDerivAt_const t v)
  apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ (by positivity)
  · intro u v
    have heq : (fun s => (F.metric s).pullbackCoefficients e x u v) =
        (fun s => (F.metric s).pullbackCoefficients e x v u) :=
      funext fun s => (F.metric s).symm _ _ _
    have huv := happ u v
    rw [heq] at huv
    exact huv.unique (happ v u)
  · intro v
    rw [F.deriv_pullbackCoefficients_apply hJ hU he ht hx, abs_mul]
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) (e x)) = n := by
      rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
      simp
    have hric := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm
      (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
    simp only [Fintype.card_fin, hdim] at hric
    have hnonneg : 0 ≤ (F.metric t).pullbackCoefficients e x v v := by
      let w := mfderiv (𝓡 n) (𝓡 n) e x v
      change 0 ≤ (F.metric t).inner (e x) w w
      by_cases hw : w = 0
      · simp [hw]
      · exact ((F.metric t).pos (e x) w hw).le
    have hbound := hric.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hcurv (by positivity)) (hupper v)
      hnonneg (by positivity))
    calc
      _ ≤ 2 * ((n : ℝ) ^ 3 * K * (b * ‖v‖ ^ 2)) := by
        norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by ring

end PoincareConjecture.RicciFlow
