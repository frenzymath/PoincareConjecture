import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_ScalarTolerance
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJetsBounds
import PoincareConjecture.Proofs.M36.JetProductBounds

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M46

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "V" => MetricCoefficient 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance intrinsicScalarCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance intrinsicScalarCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance intrinsicScalarTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance intrinsicScalarTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace

theorem exists_standardCap_intrinsic_twoJet_bound {g0 : StandardInitialMetric}
    (S : MaximalStandardCapFlow g0) {theta : ℝ} (htheta : theta < S.base.lifetime)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 theta,
      ∀ U : Set E, IsOpen U → ∀ A : E → V, ContDiffOn ℝ ∞ A U →
      ∀ x ∈ K, x ∈ U → ∀ rho : ℝ, 0 ≤ rho →
      (∀ j ≤ 2, (S.metric t).tensorNorm
        ((S.connection t).iteratedCovariantTensorDerivative (k := 2)
          (fun y v => A y (v 0) (v 1) - (S.metric t).inner y (v 0) (v 1)) j) x ≤ rho) →
      ‖metricTwoJet A x - metricTwoJet (S.metric t).euclideanCoefficients x‖ ≤
        C * rho := by
  obtain ⟨a, ha, B, hmodel⟩ :=
    M44.exists_standard_family_ellipticity_jet_bound S.base htheta hK 3
  let L : ℝ := max B 1
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  choose C hC hbound using fun j : Fin 3 =>
    M44.exists_uniform_bilinear_error_jet_bound j ha hL B
  let C0 : ℝ := 1 + ∑ j : Fin 3, C j
  have hC0 : 0 < C0 := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun j _ => (hC j).le)
    dsimp [C0]
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
  rw [← M36.metricTwoJet_sub_of_contDiffAt
    (hA.contDiffAt (hU.mem_nhds hxU)) ((S.metric t).contDiffAt_euclideanCoefficients x)]
  apply M36.norm_metricTwoJet_le_iff.mpr
  intro j hj
  have hj3 : j < 3 := by omega
  have hCsum : C ⟨j, hj3⟩ ≤ C0 := by
    have hs := Finset.single_le_sum (f := C) (fun k _ => (hC k).le)
      (Finset.mem_univ (⟨j, hj3⟩ : Fin 3))
    dsimp [C0]
    linarith
  exact (hbound ⟨j, hj3⟩ (S.connection t) A U hU hA rho hrho x hxU hell
    (fun m hm => hjets m (by omega)) hframe
    (fun m hm => hnorm m (hm.trans hj))).trans
      (mul_le_mul_of_nonneg_right hCsum hrho)

theorem exists_standardCap_intrinsic_scalarRate_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {c theta : ℝ}
    (hc : 0 < c) (htheta : theta < 1)
    (hrate : ∀ t ∈ Ico 0 P.standard_cap.flow.base.lifetime, ∀ x : E,
      c / (1 - t) ≤ (P.standard_cap.flow.connection t).scalarCurvature x)
    {K : Set E} (hK : IsCompact K) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 / 2 ∧ ∀ t ∈ Icc 0 theta,
      ∀ U : Set E, IsOpen U → ∀ A : E → V, ContDiffOn ℝ ∞ A U →
      ∀ x ∈ K, x ∈ U →
      (∀ j ≤ 2, (P.standard_cap.flow.metric t).tensorNorm
        ((P.standard_cap.flow.connection t).iteratedCovariantTensorDerivative (k := 2)
          (fun y v => A y (v 0) (v 1) -
            (P.standard_cap.flow.metric t).inner y (v 0) (v 1)) j) x ≤ eta) →
      c / (2 * (1 - t)) ≤ M44.jetScalarCurvature (metricTwoJet A x) := by
  obtain ⟨delta, hdelta, hscalar⟩ :=
    exists_standardCap_scalarRate_tolerance P hc htheta hrate hK
  obtain ⟨C, hC, hbound⟩ := exists_standardCap_intrinsic_twoJet_bound
    P.standard_cap.flow (by simpa only [P.standard_cap.lifetime_one] using htheta) hK
  let eta : ℝ := min (1 / 2) (delta / C)
  have heta : 0 < eta := lt_min (by norm_num) (div_pos hdelta hC)
  refine ⟨eta, heta, min_le_left _ _, ?_⟩
  intro t ht U hU A hA x hx hxU hnorm
  apply hscalar t ht x hx
  apply (hbound t ht U hU A hA x hx hxU eta heta.le hnorm).trans
  have h : eta ≤ delta / C := min_le_right _ _
  have := (le_div_iff₀ hC).mp h
  nlinarith

end PoincareConjecture.Proofs.M46
