import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Flux
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.Stationary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.DivergenceEstimate

noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff NNReal ENNReal

namespace PoincareConjecture.HarmonicCoordinates

open Poincare.Parabolic.Interior

private theorem holderWith_half_of_norm_sub_le
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {H : ℝ≥0}
    (hf : ∀ x y, ‖f x - f y‖ ≤ (H : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ)) :
    HolderWith H (1 / 2) f := by
  intro x y
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ (show (0 : ℝ) ≤ ((1 / 2 : ℝ≥0) : ℝ) by positivity),
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat, dist_eq_norm] using hf x y

theorem exists_uniform_small_divergence_gradient_halfHolder {n : ℕ} (hn : 2 ≤ n) :
    let V := EuclideanSpace ℝ (Fin n)
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ L U M B : ℝ≥0,
      ∃ H : ℝ≥0, 0 < H ∧
      ∀ (E : V → V →L[ℝ] V) (u : V → ℝ),
        ContDiff ℝ ∞ E → ContDiff ℝ ∞ u → HasCompactSupport u →
        (∀ x, ‖E x‖ ≤ ε) → HolderWith L (1 / 2) E →
        (∀ x, ‖u x‖ ≤ U) → (∀ x, ‖fderiv ℝ u x‖ ≤ M) →
        (∀ x, ‖stationaryEllipticResidual u (coordinateErrorFlux E u)
          (EuclideanSpace.basisFun (Fin n) ℝ) x‖ ≤ B) →
        HolderWith H (1 / 2) (fderiv ℝ u) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨C, hC, hheat⟩ := exists_uniform_divergence_potential_gradient_halfHolder
    (V := EuclideanSpace ℝ (Fin n)) (F := ℝ) (ι := Fin n)
  obtain ⟨T, hT, hforce⟩ := exists_stationaryForcing_bound
    (V := EuclideanSpace ℝ (Fin n)) (F := ℝ)
  let c : ℝ≥0 := ⟨C, (zero_le_one.trans hC)⟩
  let d : ℝ≥0 := ⟨T, hT⟩
  have hc : 0 < c := by change (0 : ℝ) < C; linarith
  have hn' : 0 < (n : ℝ≥0) := by exact_mod_cast (show 0 < n by omega)
  let ε : ℝ≥0 := (2 * c * n)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : c * n * ε = 1 / 2 := by
    dsimp [ε]
    field_simp
    <;> ring
  refine ⟨ε, hε, fun L U M B => ?_⟩
  let b : ℝ≥0 := c * (d * U + B + n * L * M)
  refine ⟨max 1 (b / (1 - (1 / 2 : ℝ≥0))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun E u hE hu huc hEbound hEholder hubound hdu hres => ?_⟩
  have hfinal : HolderWith (b / (1 - (1 / 2 : ℝ≥0))) (1 / 2) (fderiv ℝ u) := by
    apply holderWith_half_fderiv_of_self_improving hu huc (by norm_num)
    intro H hH
    let Q := coordinateErrorFlux E u
    let e := EuclideanSpace.basisFun (Fin n) ℝ
    let G := stationaryEllipticResidual u Q e
    have hQ (i) : ContDiff ℝ ∞ (Q i) := contDiff_coordinateErrorFlux hE hu i
    have hQc (i) : HasCompactSupport (Q i) := hasCompactSupport_coordinateErrorFlux E huc i
    have hG : ContDiff ℝ ∞ G := contDiff_stationaryEllipticResidual e hu hQ
    have hGc : HasCompactSupport G := hasCompactSupport_stationaryEllipticResidual e huc hQc
    let K : ℝ≥0 := d * U + B
    let Qbound : ℝ≥0 := ε * H + L * M
    have hfbound (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) (x) :
        ‖stationaryForcing u G (x, s)‖ ≤ K := by
      exact hforce u G U B U.coe_nonneg B.coe_nonneg hubound hres (x, s)
    have hqholder (i : Fin n) (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) :
        HolderWith Qbound (1 / 2) (fun x => stationaryLift (Q i) (x, s)) :=
      holderWith_stationaryLift
        (holderWith_coordinateErrorFlux hEholder hH hEbound hdu i) s
    have hcoef : c * (K + n * Qbound) = (1 / 2 : ℝ≥0) * H + b := by
      calc
        _ = (c * n * ε) * H + b := by dsimp [K, Qbound, b]; ring
        _ = _ := by rw [hsmall]
    apply holderWith_half_of_norm_sub_le
    intro x y
    have h := hheat (stationaryLift u) (stationaryForcing u G)
      (fun i => stationaryLift (Q i)) e
      (contDiff_stationaryLift hu) (hasCompactSupport_stationaryLift huc)
      (stationaryLift_zero u) (contDiff_stationaryForcing hu hG)
      (hasCompactSupport_stationaryForcing huc hGc)
      (fun i => contDiff_stationaryLift (hQ i))
      (fun i => hasCompactSupport_stationaryLift (hQc i))
      (fun i => (e.norm_eq_one i).le)
      (heatResidual_stationaryLift_eq_forcing_sub_divergence e hu hQ)
      1 zero_lt_one le_rfl K Qbound hfbound hqholder x y
    have hslice : (fun z => stationaryLift u (z, 1)) = u := funext (stationaryLift_one u)
    rw [hslice, Fintype.card_fin] at h
    have hcoef' : C * ((K : ℝ) + (n : ℝ) * (Qbound : ℝ)) =
        (((1 / 2 : ℝ≥0) * H + b : ℝ≥0) : ℝ) := by
      have hc' := congrArg (fun z : ℝ≥0 => (z : ℝ)) hcoef
      rw [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_mul] at hc'
      dsimp [c] at hc'
      have hcc : (c : ℝ) = C := by rfl
      rw [hcc] at hc'
      exact hc'
    rwa [hcoef'] at h
  exact hfinal.mono (le_max_right _ _)

end PoincareConjecture.HarmonicCoordinates
