import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessEquation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance suCompactBoundsBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactBoundsBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactBoundsTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactBoundsTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace




theorem suAlphaHessianTerm_bound
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v : Fin 2 → E) (H : Fin 2 → Fin 2 → E)
    {d kappa K : ℝ} (hd : 0 < d) (hkappa : 0 < kappa) (hK : ‖G‖ ≤ K)
    (hcoer : ∀ w : E, kappa * ‖w‖ ^ 2 ≤ G w w)
    (hden : (∑ i : Fin 2, G (v i) (v i)) ≤ d) :
    ‖suAlphaHessianTerm G v H d‖ ≤
      (4 * K / kappa) * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j‖ ^ 2) := by
  let S := ∑ i : Fin 2, ‖v i‖ ^ 2
  let P := ‖v 0‖ + ‖v 1‖
  let T := Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j‖ ^ 2)
  have hK0 : 0 ≤ K := (norm_nonneg G).trans hK
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hS : kappa * S ≤ d := by
    calc
      _ = ∑ i : Fin 2, kappa * ‖v i‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin 2, G (v i) (v i) := Finset.sum_le_sum fun i _ => hcoer _
      _ ≤ d := hden
  have hP : P ^ 2 ≤ 2 * S := by
    dsimp [P, S]
    rw [Fin.sum_univ_two]
    nlinarith [sq_nonneg (‖v 0‖ - ‖v 1‖)]
  have hH (i j : Fin 2) : ‖H i j‖ ≤ T := by
    have hh : ‖H i j‖ ^ 2 ≤ ∑ a : Fin 2, ∑ b : Fin 2, ‖H a b‖ ^ 2 :=
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖H i k‖) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg ‖H k l‖)
          (Finset.mem_univ i))
    have ht : T ^ 2 = ∑ a : Fin 2, ∑ b : Fin 2, ‖H a b‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
    nlinarith [norm_nonneg (H i j)]
  have hsummand (i k : Fin 2) :
      ‖(G (v k) (H k i)) • v i‖ ≤ K * ‖v k‖ * T * ‖v i‖ := by
    rw [norm_smul]
    calc
      _ ≤ (‖G‖ * ‖v k‖ * ‖H k i‖) * ‖v i‖ := by
        gcongr
        exact G.le_opNorm₂ _ _
      _ ≤ K * ‖v k‖ * T * ‖v i‖ := by
        gcongr
        exact hH k i
  have hsum : ‖∑ i : Fin 2, ∑ k : Fin 2, (G (v k) (H k i)) • v i‖ ≤
      K * T * P ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 2, ∑ k : Fin 2, ‖(G (v k) (H k i)) • v i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i : Fin 2, ∑ k : Fin 2, K * ‖v k‖ * T * ‖v i‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hsummand i k
      _ = K * T * P ^ 2 := by simp only [Fin.sum_univ_two, P]; ring
  have hquot : S / d ≤ 1 / kappa := (div_le_div_iff₀ hd hkappa).mpr (by nlinarith)
  calc
    _ = (2 / d) * ‖∑ i : Fin 2, ∑ k : Fin 2, (G (v k) (H k i)) • v i‖ := by
      rw [suAlphaHessianTerm, norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (2 / d) * (K * T * P ^ 2) := by gcongr
    _ ≤ (2 / d) * (K * T * (2 * S)) := by gcongr
    _ = (4 * K * T) * (S / d) := by ring
    _ ≤ (4 * K * T) * (1 / kappa) := by gcongr
    _ = (4 * K / kappa) * T := by ring




theorem suAlphaLowerTerm_bound
    (Gamma : E →L[ℝ] E →L[ℝ] E) (G : E →L[ℝ] E →L[ℝ] ℝ)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v : Fin 2 → E) (dlambda : Fin 2 → ℝ)
    {lambda d c kappa J C D L N : ℝ}
    (hlambda : 0 < lambda) (hd : 0 < d) (hc : 0 ≤ c) (hkappa : 0 < kappa)
    (hGamma : ‖Gamma‖ ≤ C) (hDG : ‖DG‖ ≤ J)
    (hcoer : ∀ w : E, kappa * ‖w‖ ^ 2 ≤ G w w)
    (hden : (∑ i : Fin 2, G (v i) (v i)) ≤ d)
    (hv : ∀ i, ‖v i‖ ≤ D) (hl : lambda⁻¹ ≤ L) (hdlambda : ∀ i, ‖dlambda i‖ ≤ N) :
    ‖suAlphaLowerTerm Gamma G DG v lambda dlambda d c‖ ≤
      2 * C * D ^ 2 + c * (2 * J * D ^ 2 / kappa + 2 * L * N * D) := by
  let S := ∑ i : Fin 2, ‖v i‖ ^ 2
  let Q := ∑ i : Fin 2, G (v i) (v i)
  have hC : 0 ≤ C := (norm_nonneg Gamma).trans hGamma
  have hJ : 0 ≤ J := (norm_nonneg DG).trans hDG
  have hD : 0 ≤ D := (norm_nonneg (v 0)).trans (hv 0)
  have hL : 0 ≤ L := (inv_pos.mpr hlambda).le.trans hl
  have hN : 0 ≤ N := (norm_nonneg (dlambda 0)).trans (hdlambda 0)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSq : kappa * S ≤ Q := by
    dsimp only [S]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hcoer _
  have hQ : 0 ≤ Q := (mul_nonneg hkappa.le hS).trans hSq
  have hSD : S ≤ 2 * D ^ 2 := by
    simp only [S, Fin.sum_univ_two]
    nlinarith [sq_le_sq₀ (norm_nonneg (v 0)) hD |>.mpr (hv 0),
      sq_le_sq₀ (norm_nonneg (v 1)) hD |>.mpr (hv 1)]
  have hquot : S / d ≤ 1 / kappa :=
    (div_le_div_iff₀ hd hkappa).mpr (by nlinarith [hSq.trans hden])
  have hQquot : Q / d ≤ 1 := (div_le_one hd).mpr hden
  have hGsum : ‖∑ i : Fin 2, Gamma (v i) (v i)‖ ≤ C * S := by
    calc
      _ ≤ ∑ i : Fin 2, ‖Gamma (v i) (v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, C * ‖v i‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        calc
          _ ≤ ‖Gamma‖ * ‖v i‖ * ‖v i‖ := Gamma.le_opNorm₂ _ _
          _ ≤ C * ‖v i‖ ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_right hGamma (sq_nonneg ‖v i‖)]
      _ = C * S := (Finset.mul_sum _ _ _).symm
  have hDGi (i : Fin 2) : ‖∑ k : Fin 2, DG (v i) (v k) (v k)‖ ≤ J * ‖v i‖ * S := by
    calc
      _ ≤ ∑ k : Fin 2, ‖DG (v i) (v k) (v k)‖ := norm_sum_le _ _
      _ ≤ ∑ k : Fin 2, J * ‖v i‖ * ‖v k‖ ^ 2 := Finset.sum_le_sum fun k _ => by
        calc
          _ ≤ ‖DG (v i)‖ * ‖v k‖ * ‖v k‖ := (DG (v i)).le_opNorm₂ _ _
          _ ≤ (‖DG‖ * ‖v i‖) * ‖v k‖ * ‖v k‖ := by
            gcongr
            exact DG.le_opNorm _
          _ ≤ (J * ‖v i‖) * ‖v k‖ * ‖v k‖ := by gcongr
          _ = J * ‖v i‖ * ‖v k‖ ^ 2 := by ring
      _ = J * ‖v i‖ * S := (Finset.mul_sum _ _ _).symm
  have hsource (i : Fin 2) : ‖Q * dlambda i / lambda‖ ≤ Q * N * L := by
    rw [norm_div, norm_mul, Real.norm_of_nonneg hQ, Real.norm_of_nonneg hlambda.le,
      div_eq_mul_inv]
    gcongr
    exact hdlambda i
  have hsum : ‖∑ i : Fin 2, ((∑ k : Fin 2, DG (v i) (v k) (v k)) -
      Q * dlambda i / lambda) • v i‖ ≤ J * S ^ 2 + 2 * Q * N * L * D := by
    calc
      _ ≤ ∑ i : Fin 2, ‖((∑ k : Fin 2, DG (v i) (v k) (v k)) -
          Q * dlambda i / lambda) • v i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, (J * ‖v i‖ * S + Q * N * L) * ‖v i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right
          ((norm_sub_le _ _).trans (add_le_add (hDGi i) (hsource i))) (norm_nonneg _)
      _ = J * S ^ 2 + Q * N * L * (‖v 0‖ + ‖v 1‖) := by
        simp only [Fin.sum_univ_two, S]
        ring
      _ ≤ J * S ^ 2 + 2 * Q * N * L * D := by
        nlinarith [mul_le_mul_of_nonneg_left (hv 0) (show 0 ≤ Q * N * L by positivity),
          mul_le_mul_of_nonneg_left (hv 1) (show 0 ≤ Q * N * L by positivity)]
  calc
    _ ≤ ‖∑ i : Fin 2, Gamma (v i) (v i)‖ +
        ‖(c / d) • ∑ i : Fin 2, ((∑ k : Fin 2, DG (v i) (v k) (v k)) -
          Q * dlambda i / lambda) • v i‖ := by
      simpa only [suAlphaLowerTerm, norm_neg, Q] using norm_sub_le
        (-(∑ i : Fin 2, Gamma (v i) (v i)))
        ((c / d) • ∑ i : Fin 2, ((∑ k : Fin 2, DG (v i) (v k) (v k)) -
          Q * dlambda i / lambda) • v i)
    _ ≤ C * S + (c / d) * (J * S ^ 2 + 2 * Q * N * L * D) := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hc hd.le)]
      exact add_le_add hGsum (mul_le_mul_of_nonneg_left hsum (div_nonneg hc hd.le))
    _ = C * S + c * (J * S * (S / d) + 2 * N * L * D * (Q / d)) := by ring
    _ ≤ C * S + c * (J * S * (1 / kappa) + 2 * N * L * D * 1) := by gcongr
    _ ≤ C * (2 * D ^ 2) + c * (J * (2 * D ^ 2) * (1 / kappa) +
        2 * N * L * D * 1) := by gcongr
    _ = _ := by ring

end PoincareConjecture.M60
