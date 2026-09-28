import PoincareConjecture.Proofs.M28.Sec10_3_Tube.TubeSourceMinimizer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CappedSourceMinimizer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CappedReverseSourceMinimizer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CappedTwoNeckSourceMinimizer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CompactBranchMinimizers
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapAlternatives

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

theorem exists_region_source_minimizer_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (H : ConnectedNeckCapCover g) (_R : RepairedNeckCapTopologyData g H),
        H.epsilon ≤ epsilon₀ →
        ∀ (Q A : ℝ) (η : ℝ → M) (a b : ℝ), 0 < Q → a ≤ b →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b) → MapsTo η (Icc a b) H.X →
          g.pathELength η a b < ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) →
          D.scalarCurvature (η a) = 8 * Q →
          32 * (max H.cap_constant 2) ^ 4 * Q < D.scalarCurvature (η b) →
          ∃ U : Set M, IsOpen U ∧ H.X ⊆ U ∧
            ∃ γ : ℝ → M,
              D.scalarCurvature (γ 0) ≤ 8 * max H.cap_constant 2 * Q ∧
              32 * (max H.cap_constant 2) ^ 3 * Q < D.scalarCurvature (γ 1) ∧
              D.scalarCurvature (η b) ≤ max H.cap_constant 2 * D.scalarCurvature (γ 1) ∧
              ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
              MapsTo γ (Icc (0 : ℝ) 1) U ∧
              g.pathELength γ 0 1 = intrinsicEDist g U (γ 0) (γ 1) ∧
              g.pathELength γ 0 1 ≠ ⊤ ∧
              g.pathELength γ 0 1 <
                ENNReal.ofReal ((A + 2 * endpointConnectorBudget H.epsilon H.cap_constant) *
                  Q ^ (-1 / 2 : ℝ)) := by
  classical
  obtain ⟨epsilonT, hTpos, hTthreshold, htube⟩ := exists_tube_source_minimizer_accuracy.{u}
  obtain ⟨epsilonL, hLpos, _, hlowcap⟩ := exists_low_cap_high_neck_source_minimizer_accuracy.{u}
  obtain ⟨epsilonH, hHpos, _, hhighcap⟩ := exists_low_neck_high_cap_source_minimizer_accuracy.{u}
  obtain ⟨epsilonN, hNpos, _, htwonecks⟩ := exists_capped_two_neck_source_minimizer_accuracy.{u}
  let epsilon₀ := min epsilonT (min epsilonL (min epsilonH epsilonN))
  refine ⟨epsilon₀, lt_min hTpos (lt_min hLpos (lt_min hHpos hNpos)),
    (min_le_left _ _).trans hTthreshold, ?_⟩
  intro M _ _ _ _ _ _ _ g D H R hsmall Q A η a b hQ hab hη hηX hηL hz hy
  have hsmallT : H.epsilon ≤ epsilonT := hsmall.trans (min_le_left _ _)
  have hsmallL : H.epsilon ≤ epsilonL :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallH : H.epsilon ≤ epsilonH :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallN : H.epsilon ≤ epsilonN :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let B := max H.cap_constant 2
  have hB : 1 ≤ B := le_trans (by norm_num) (le_max_right H.cap_constant 2)
  have hBnonneg : 0 ≤ B := le_trans zero_le_one hB
  have hC2 : H.cap_constant ^ 2 ≤ B ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self H.cap_constant_pos.le (le_max_left H.cap_constant 2)
  have hB24 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB (by norm_num)
  have hB34 : B ^ 3 ≤ B ^ 4 := pow_le_pow_right₀ hB (by norm_num)
  have hlarge : H.cap_constant ^ 2 * D.scalarCurvature (η a) < D.scalarCurvature (η b) := by
    calc
      H.cap_constant ^ 2 * D.scalarCurvature (η a) = H.cap_constant ^ 2 * (8 * Q) := by
        rw [hz]
      _ ≤ B ^ 2 * (8 * Q) := mul_le_mul_of_nonneg_right hC2 (by positivity)
      _ ≤ B ^ 4 * (8 * Q) := mul_le_mul_of_nonneg_right hB24 (by positivity)
      _ ≤ 32 * B ^ 4 * Q := by nlinarith only [mul_nonneg (pow_nonneg hBnonneg 4) hQ.le]
      _ < D.scalarCurvature (η b) := hy
  have hshape := regionHasTubeOrFibration_of_scalar_ratio H D R
    (hηX (left_mem_Icc.mpr hab)) (hηX (right_mem_Icc.mpr hab)) hlarge
  have hfinite : g.pathELength η a b ≠ ⊤ := ne_top_of_lt (hηL.trans_le le_top)
  have hlow : D.scalarCurvature (η a) ≤ 8 * B * Q := by
    rw [hz]
    nlinarith only [mul_le_mul_of_nonneg_right hB hQ.le]
  have hhigh : 32 * B ^ 3 * Q < D.scalarCurvature (η b) :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB34 (by norm_num : (0 : ℝ) ≤ 32)) hQ.le).trans_lt hy
  have hhighpos : 0 < D.scalarCurvature (η b) :=
    lt_of_le_of_lt (by positivity : 0 ≤ 32 * B ^ 4 * Q) hy
  have hcomparison : D.scalarCurvature (η b) ≤ B * D.scalarCurvature (η b) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB hhighpos.le
  have hlength : g.pathELength η a b <
      ENNReal.ofReal ((A + 2 * endpointConnectorBudget H.epsilon H.cap_constant) *
        Q ^ (-1 / 2 : ℝ)) := by
    apply hηL.trans_le
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
    linarith only [endpointConnectorBudget_pos (C := H.cap_constant) H.epsilon_pos]
  rcases R with ⟨region, hcompat⟩
  cases region with
  | twoCaps _ _ _ _ _ _ => exact False.elim hshape
  | singleCap _ _ => exact False.elim hshape
  | doubleCappedTube T _ _ hcontains =>
      obtain ⟨γ, hγ0, hγ1, hγ, hγU, hmin, hγfinite, hle⟩ :=
        T.exists_intrinsic_minimizer hab hη (fun t ht => hcontains (hηX ht)) hfinite
      refine ⟨T.carrier, T.isOpen_carrier, hcontains, γ, ?_, ?_, ?_,
        hγ, hγU, ?_, hγfinite, hle.trans_lt hlength⟩
      · simpa only [hγ0] using hlow
      · simpa only [hγ1] using hhigh
      · simpa only [hγ1] using hcomparison
      · simpa only [hγ0, hγ1] using hmin
  | fibration T =>
      have hcontains : H.X ⊆ T.carrier := hcompat.2
      obtain ⟨γ, hγ0, hγ1, hγ, hγU, hmin, hγfinite, hle⟩ :=
        T.exists_intrinsic_minimizer hab hη (fun t ht => hcontains (hηX ht)) hfinite
      refine ⟨T.carrier, T.isOpen_carrier, hcontains, γ, ?_, ?_, ?_,
        hγ, hγU, ?_, hγfinite, hle.trans_lt hlength⟩
      · simpa only [hγ0] using hlow
      · simpa only [hγ1] using hhigh
      · simpa only [hγ1] using hcomparison
      · simpa only [hγ0, hγ1] using hmin
  | tube T =>
      have hepsilon : T.epsilon = H.epsilon := hcompat
      obtain ⟨_, _, _, _, γ, _, _, hlo, hhi, hcompare, hγ, hγU, hmin, hγfinite, hbound⟩ :=
        htube M g D H.X T (hepsilon.trans_le hsmallT) H.cap_constant Q A η a b hQ hab hη
          (fun t ht => T.contains_X (hηX ht)) hηL hz hy
      refine ⟨T.carrier, T.carrier_open, T.contains_X, γ, hlo, hhi, hcompare,
        hγ, hγU, hmin, hγfinite, ?_⟩
      simpa only [hepsilon] using hbound
  | cappedTube T hcontains =>
      obtain ⟨_, hepsilon, hcap, _⟩ := hcompat
      have hopen : IsOpen T.carrier := by
        rw [T.carrier_eq_union]
        exact T.cap.carrier_open.union T.tube.carrier_open
      have hηU : MapsTo η (Icc a b) T.carrier := fun t ht => hcontains (hηX ht)
      have hpa : η a ∈ T.cap.carrier ∪ T.tube.carrier := by
        rw [← T.carrier_eq_union]
        exact hηU (left_mem_Icc.mpr hab)
      have hpb : η b ∈ T.cap.carrier ∪ T.tube.carrier := by
        rw [← T.carrier_eq_union]
        exact hηU (right_mem_Icc.mpr hab)
      by_cases hzcap : η a ∈ T.cap.carrier
      · by_cases hycap : η b ∈ T.cap.carrier
        · have hbound := T.cap.scalar_le_sq_mul_on_union T.cap D hcap hcap
            ⟨η a, hzcap, hzcap⟩ (Or.inl hzcap) (Or.inl hycap)
          exact False.elim ((not_lt_of_ge hbound) hlarge)
        · obtain ⟨_, _, _, _, γ, _, _, hlo, hhi, hcompare, hγ, hγU, hmin, hγfinite, hbound⟩ :=
            hlowcap M g D T (hepsilon.trans_le hsmallL) H.cap_constant Q A η a b
              hcap hQ hab hη hηU hzcap (hpb.resolve_left hycap) hηL hz hy
          refine ⟨T.carrier, hopen, hcontains, γ, hlo, hhi, hcompare,
            hγ, hγU, hmin, hγfinite, ?_⟩
          simpa only [hepsilon] using hbound
      · by_cases hycap : η b ∈ T.cap.carrier
        · obtain ⟨_, _, _, _, γ, _, _, hlo, hhi, hcompare, hγ, hγU, hmin, hγfinite, hbound⟩ :=
            hhighcap M g D T (hepsilon.trans_le hsmallH) H.cap_constant Q A η a b
              hcap hQ hab hη hηU (hpa.resolve_left hzcap) hycap hηL hz hy
          refine ⟨T.carrier, hopen, hcontains, γ, hlo, hhi, hcompare,
            hγ, hγU, hmin, hγfinite, ?_⟩
          simpa only [hepsilon] using hbound
        · obtain ⟨_, _, _, _, γ, _, _, hlo, hhi, hcompare, hγ, hγU, hmin, hγfinite, hbound⟩ :=
            htwonecks M g D T (hepsilon.trans_le hsmallN) H.cap_constant Q A η a b
              hcap hQ hab hη hηU (hpa.resolve_left hzcap) (hpb.resolve_left hycap) hηL hz hy
          refine ⟨T.carrier, hopen, hcontains, γ, hlo, hhi, hcompare,
            hγ, hγU, hmin, hγfinite, ?_⟩
          simpa only [hepsilon] using hbound

end PoincareConjecture.M28
