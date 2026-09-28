import PoincareConjecture.Proofs.M47.BlowupControlsCapJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

local notation "E" => StandardCapSpace
local notation "V" => MetricCoefficient 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance capDerivativeCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capDerivativeCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace

theorem exists_standardCap_intrinsic_derivative_bound {g0 : StandardInitialMetric}
    (S : MaximalStandardCapFlow g0) {theta : ℝ} (htheta : theta < S.base.lifetime)
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 theta,
      ∀ U : Set E, IsOpen U → ∀ A : E → V, ContDiffOn ℝ ∞ A U →
      ∀ x ∈ K, x ∈ U → ∀ rho : ℝ, 0 ≤ rho →
      (∀ j ≤ m, (S.metric t).tensorNorm
        ((S.connection t).iteratedCovariantTensorDerivative (k := 2)
          (fun y v => A y (v 0) (v 1) - (S.metric t).inner y (v 0) (v 1)) j) x ≤ rho) →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j A x -
        iteratedFDeriv ℝ j (S.metric t).euclideanCoefficients x‖ ≤ C * rho := by
  classical
  obtain ⟨a, ha, B, hmodel⟩ :=
    M44.exists_standard_family_ellipticity_jet_bound S.base htheta hK (m + 1)
  let L : ℝ := max B 1
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  choose C hC hbound using fun j : Fin (m + 1) =>
    M44.exists_uniform_bilinear_error_jet_bound j ha hL B
  let C0 : ℝ := 1 + ∑ j : Fin (m + 1), C j
  have hC0 : 0 < C0 := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun j _ => (hC j).le)
    dsimp only [C0]
    linarith
  refine ⟨C0, hC0, ?_⟩
  intro t ht U hU A hA x hx hxU rho hrho hnorm
  obtain ⟨hell, hjets⟩ := hmodel t ht x hx
  have hframe (b : Fin 3) : (S.metric t).tangentNorm x (e b) ≤ L := by
    have hzero := hjets 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hzero
    have hinner : (S.metric t).inner x (e b) (e b) ≤ B := by
      calc
        _ ≤ ‖(S.metric t).euclideanCoefficients x (e b) (e b)‖ := le_abs_self _
        _ ≤ ‖(S.metric t).euclideanCoefficients x‖ * ‖e b‖ * ‖e b‖ :=
          ((S.metric t).euclideanCoefficients x).le_opNorm₂ (e b) (e b)
        _ = ‖(S.metric t).euclideanCoefficients x‖ := by
          rw [OrthonormalBasis.norm_eq_one, mul_one, mul_one]
        _ ≤ B := hzero
    unfold RiemannianMetric.tangentNorm
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hL.le, ?_⟩
    have hBL : B ≤ L := le_max_left _ _
    nlinarith
  intro j hj
  have hCsum : C ⟨j, by omega⟩ ≤ C0 := by
    have hs := Finset.single_le_sum (f := C) (fun k _ => (hC k).le)
      (Finset.mem_univ (⟨j, by omega⟩ : Fin (m + 1)))
    dsimp only [C0]
    linarith
  have hconvert := hbound ⟨j, by omega⟩ (S.connection t) A U hU hA rho hrho x hxU hell
    (fun k hk => hjets k (by omega)) hframe (fun k hk => hnorm k (hk.trans hj))
  change ‖iteratedFDeriv ℝ j (fun y => A y - (S.metric t).euclideanCoefficients y) x‖ ≤
    C ⟨j, by omega⟩ * rho at hconvert
  rw [fun_iteratedFDeriv_sub_apply
    ((hA.contDiffAt (hU.mem_nhds hxU)).of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))
    (((S.metric t).contDiffAt_euclideanCoefficients x).of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))] at hconvert
  exact hconvert.trans (mul_le_mul_of_nonneg_right hCsum hrho)

end PoincareConjecture.M47
