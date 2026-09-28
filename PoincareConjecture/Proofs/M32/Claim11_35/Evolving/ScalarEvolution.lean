import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.Realization
import PoincareConjecture.Proofs.M32.Claim11_35.ScalarLaplacianControl
import PoincareConjecture.Proofs.M32.Claim11_35.WorldlineMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.EuclideanModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem evolving_metric_scalar_jet_le_full
    (h g : RiemannianMetric 3 E3) (r : ℕ) (i j : Fin 3) :
    ‖iteratedFDeriv ℝ r (fun x => h.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)) 0 -
      iteratedFDeriv ℝ r (fun x => g.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)) 0‖ ≤
      ‖iteratedFDeriv ℝ r h.euclideanCoefficients 0 -
        iteratedFDeriv ℝ r g.euclideanCoefficients 0‖ := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hs (k : RiemannianMetric 3 E3) : ContDiffAt ℝ ∞
      (fun x => k.inner x (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0 :=
    ((k.contDiffAt_euclideanCoefficients 0).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  rw [← iteratedFDeriv_sub_apply ((hs h).of_le hr) ((hs g).of_le hr),
    ← iteratedFDeriv_sub_apply ((h.contDiffAt_euclideanCoefficients 0).of_le hr)
      ((g.contDiffAt_euclideanCoefficients 0).of_le hr)]
  let B := fun x => h.euclideanCoefficients x - g.euclideanCoefficients x
  have hB : ContDiffAt ℝ ∞ B 0 :=
    (h.contDiffAt_euclideanCoefficients 0).sub (g.contDiffAt_euclideanCoefficients 0)
  have hb (a : Fin 3) : ‖roundCylinderEuclideanBasis a‖ = 1 := by
    simp only [roundCylinderEuclideanBasis, Module.Basis.reindex_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.norm_eq_one]
  have hfirst := norm_iteratedFDeriv_clm_apply_const
    (c := roundCylinderEuclideanBasis i) hB hr
  have hsecond := norm_iteratedFDeriv_clm_apply_const
    (c := roundCylinderEuclideanBasis j)
    (hB.clm_apply (contDiffAt_const (c := roundCylinderEuclideanBasis i))) hr
  simp only [hb, one_mul] at hfirst hsecond
  exact hsecond.trans hfirst

private theorem evolving_model_scalar_laplacian
    (D : LeviCivitaData roundCylinderEuclideanMetric) :
    D.scalarCurvature 0 = 1 ∧ D.laplacian D.scalarCurvature 0 = 0 := by
  have heq : D.scalarCurvature = fun _ => (1 : ℝ) :=
    funext fun x => roundCylinderEuclideanMetric_scalarCurvature D x
  refine ⟨congrFun heq 0, ?_⟩
  rw [heq]
  simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
    LeviCivitaData.hessianOnFields, mvfderiv_const]

theorem exists_strongNeck_backward_scalarLaplacian_control :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
        ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ epsilon₀ →
          ∀ {tau : ℝ} (htau : tau ∈ Ioc (-1) 0), ∀ x ∈ N.carrier,
            let p := N.time_cylinder.pointMap tau htau x
            0 < F.scalar p ∧
              3 / 4 < (1 - tau) * normalizedCylinderScalar N.time_cylinder x tau ∧
              (1 - tau) * normalizedCylinderScalar N.time_cylinder x tau < 5 / 4 ∧
              |(F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2| ≤
                (F.scalar p) ^ 2 / 6 := by
  let D0 := roundCylinderEuclideanMetric.leviCivitaData
  obtain ⟨deltaS, hdeltaS, hscalar⟩ := D0.exists_scalar_ricci_control_of_metric_twoJet
    0 roundCylinderEuclideanBasis (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨deltaL, hdeltaL, hlaplacian⟩ := exists_scalar_laplacian_control_of_metric_fourJet
    D0 0 (by norm_num : (0 : ℝ) < 1 / 96)
  obtain ⟨epsilon₀, hpos, hsmall, hrealize⟩ :=
    exists_strongNeck_evolving_fourJet_realization.{u} (lt_min hdeltaS hdeltaL)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F t epsilon N hN tau htau x hx
  let q := (N.coordinate_inverse x).1
  let z := (N.coordinate_inverse x).2
  have hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := N.coordinate_inverse_mem x hx
  have hcoord : N.coordinate_map (q, z) = x := N.coordinate_inverse_right x hx
  obtain ⟨h, Dh, heq, hjets⟩ := hrealize N hN htau q hz
  have hS := (hscalar h Dh (fun r hr i j =>
    (evolving_metric_scalar_jet_le_full h roundCylinderEuclideanMetric r i j).trans_lt
      ((hjets r (by omega)).trans_le (min_le_left _ _)))).1
  have hL := hlaplacian h Dh (fun r hr => (hjets r hr).trans_le (min_le_right _ _))
  rw [(evolving_model_scalar_laplacian D0).1] at hS
  rw [(evolving_model_scalar_laplacian D0).2, sub_zero] at hL
  have hSlower : (3 / 4 : ℝ) < Dh.scalarCurvature 0 := by
    linarith [(abs_lt.mp hS).1]
  have hSupper : Dh.scalarCurvature 0 < (5 / 4 : ℝ) := by
    linarith [(abs_lt.mp hS).2]
  have hLsmall : |Dh.laplacian Dh.scalarCurvature 0| ≤ (Dh.scalarCurvature 0) ^ 2 / 6 := by
    have hgap : (1 / 96 : ℝ) < (Dh.scalarCurvature 0) ^ 2 / 6 := by nlinarith
    exact (hL.trans hgap).le
  have hscales := strongNeck_evolving_realization_curvatures N htau q hz Dh heq
  dsimp only at hscales
  rw [hcoord] at hscales
  let p := N.time_cylinder.pointMap tau htau x
  let Q := N.scale⁻¹ ^ 2
  let a := 1 - tau
  let R := F.scalar p
  let lap := (F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2
  have hQ : 0 < Q := N.time_cylinder.scale_pos
  have ha : 0 < a := by dsimp only [a]; linarith [htau.2]
  have hscaleS : Dh.scalarCurvature 0 = a * R / Q := hscales.1
  have hscaleL : Dh.laplacian Dh.scalarCurvature 0 = a ^ 2 * lap / Q ^ 2 := hscales.2
  have hR : 0 < R := by
    by_contra! hn
    have hnonpos := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ha.le hn) hQ.le
    rw [← hscaleS] at hnonpos
    linarith
  have hrho : a * normalizedCylinderScalar N.time_cylinder x tau = Dh.scalarCurvature 0 := by
    rw [hscaleS]
    simp only [normalizedCylinderScalar, dif_pos htau]
    change a * (R / Q) = a * R / Q
    ring
  have hlap : |lap| ≤ R ^ 2 / 6 := by
    rw [hscaleL, hscaleS] at hLsmall
    have hlapabs : |a ^ 2 * lap / Q ^ 2| = (a ^ 2 / Q ^ 2) * |lap| := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg Q)]
      ring
    have hscalarSq : (a * R / Q) ^ 2 / 6 = (a ^ 2 / Q ^ 2) * (R ^ 2 / 6) := by ring
    rw [hlapabs, hscalarSq] at hLsmall
    exact (mul_le_mul_iff_right₀ (div_pos (pow_pos ha 2) (pow_pos hQ 2))).mp hLsmall
  exact ⟨hR, hrho.symm ▸ hSlower, hrho.symm ▸ hSupper, hlap⟩

theorem exists_strongNeck_backward_scalarDerivative_comparison
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
        ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ epsilon₀ →
          ∀ x ∈ N.carrier,
            (∀ tau (htau : tau ∈ Ioc (-1) 0),
              let p := N.time_cylinder.pointMap tau htau x
              let Q := N.scale⁻¹ ^ 2
              let d := ((F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 +
                2 * (F.connection p.1).ricciNormSq p.2) / Q ^ 2
              HasDerivWithinAt (normalizedCylinderScalar N.time_cylinder x) d (Ioc (-1) 0) tau ∧
                (normalizedCylinderScalar N.time_cylinder x tau) ^ 2 / 2 ≤ d ∧ 0 < d) ∧
            MonotoneOn (normalizedCylinderScalar N.time_cylinder x) (Ioc (-1) 0) ∧
            ∀ tau (htau : tau ∈ Ioc (-1) 0),
              F.scalar (N.time_cylinder.pointMap tau htau x) ≤
                (F.connection t).scalarCurvature x := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ :=
    exists_strongNeck_backward_scalarLaplacian_control.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F t epsilon N hN x hx
  have hbound (tau : ℝ) (htau : tau ∈ Ioc (-1) 0) := hcontrol N hN htau x hx
  have hlap (tau : ℝ) (htau : tau ∈ Ioc (-1) 0) :
      |(F.connection (t + tau / (N.scale⁻¹ ^ 2))).laplacian
        (F.connection (t + tau / (N.scale⁻¹ ^ 2))).scalarCurvature
          (N.time_cylinder.forward tau htau x)| ≤
      ((F.connection (t + tau / (N.scale⁻¹ ^ 2))).scalarCurvature
        (N.time_cylinder.forward tau htau x)) ^ 2 / 6 := (hbound tau htau).2.2.2
  have hmono := normalizedCylinderScalar_monotoneOn_of_laplacian_bound hM04
    N.time_cylinder (convex_Ioc (-1) 0) hx hlap
  refine ⟨?_, hmono, ?_⟩
  · intro tau htau
    have hd := normalizedCylinderScalar_derivative_ge_half_sq hM04
      N.time_cylinder htau hx (hlap tau htau)
    have hrho : 0 < normalizedCylinderScalar N.time_cylinder x tau := by
      simp only [normalizedCylinderScalar, dif_pos htau]
      exact div_pos (hbound tau htau).1 N.time_cylinder.scale_pos
    refine ⟨hd.1, hd.2, ?_⟩
    exact (div_pos (sq_pos_of_pos hrho) (by norm_num)).trans_le hd.2
  · intro tau htau
    have hzero : (0 : ℝ) ∈ Ioc (-1) 0 := by constructor <;> norm_num
    have h := hmono htau hzero htau.2
    simp only [normalizedCylinderScalar, dif_pos htau, dif_pos hzero,
      N.cylinder_identity hzero x hx] at h
    exact (div_le_div_iff_of_pos_right N.time_cylinder.scale_pos).mp h

end PoincareConjecture.M32
