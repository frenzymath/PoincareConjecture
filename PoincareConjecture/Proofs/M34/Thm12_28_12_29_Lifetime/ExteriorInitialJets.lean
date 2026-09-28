import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem partialFlow_exists_exterior_initial_jet_bounds
    (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    (e : StandardCylindricalEnd g0.metric) (hL : F.lifetime < 1) :
    ∃ a H : ℝ, 0 < a ∧ ∀ T ∈ Ioo 0 F.lifetime,
      ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc 0 T,
        ∀ x ∈ endClosedSlab e (17 / 5) (23 / 5),
          (∀ j ≤ 2, ‖iteratedFDeriv ℝ j ((F.flow.metric t).pullbackCoefficients
            (endAxialTranslation e (k + 1 : ℕ))) x‖ ≤ H) ∧
          (∀ v : StandardCapSpace, a * ‖v‖ ^ 2 ≤
            (F.flow.metric t).pullbackCoefficients
              (endAxialTranslation e (k + 1 : ℕ)) x v v) := by
  classical
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FH 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FA 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FS 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let p : endReferenceRegion e := Classical.choice inferInstance
  have hcompact : IsCompact (endClosedSlab e (17 / 5) (23 / 5)) :=
    endClosedSlab_isCompact e (by norm_num)
  have hsubset : endClosedSlab e (17 / 5) (23 / 5) ⊆ endReferenceRegion e :=
    endClosedSlab_subset_reference e (by norm_num) (by norm_num)
  obtain ⟨a, M, ha, _hM, hmodel⟩ := endCylinderFlow_compact_bounds e hL hcompact 2
  let d : ℝ := min 1 (a / 2)
  have hd : 0 < d := lt_min zero_lt_one (half_pos ha)
  refine ⟨a / 2, M + 1, half_pos ha, ?_⟩
  intro T hT
  have hT' : T ∈ Ico 0 F.lifetime ∩ Ico 0 1 :=
    ⟨⟨hT.1.le, hT.2⟩, ⟨hT.1.le, hT.2.trans hL⟩⟩
  choose N hN using fun j : Fin 3 =>
    partialFlow_endCylinderDifferenceCoefficients_iteratedFDeriv_tendsto
      P E0 F e qH qA qS p hT' j.val hd
  refine ⟨∑ j, N j, ?_⟩
  intro k hk t ht x hx
  have hxU := hsubset hx
  have htL : t ∈ Icc 0 F.lifetime := ⟨ht.1, ht.2.trans hT.2.le⟩
  have htI : t ∈ Ico 0 1 := ⟨ht.1, htL.2.trans_lt hL⟩
  have hkpos : -3 < ((k + 1 : ℕ) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (k + 1)
    linarith
  have hcA : ContDiffAt ℝ ∞ ((F.flow.metric t).pullbackCoefficients
      (endAxialTranslation e (k + 1 : ℕ))) x :=
    (F.flow.metric t).contDiffAt_pullbackCoefficients
      (((endReferenceTranslation_contMDiffOn e hkpos) x hxU).contMDiffAt
        ((endReferenceRegion_isOpen e).mem_nhds hxU))
  have hcB : ContDiffAt ℝ ∞ (endCylinderCoefficients e t) x :=
    ((endCylinderCoefficients_contDiff e).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt
  have herror (j : ℕ) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ j ((F.flow.metric t).pullbackCoefficients
          (endAxialTranslation e (k + 1 : ℕ))) x -
        iteratedFDeriv ℝ j (endCylinderCoefficients e t) x‖ < d := by
    let i : Fin 3 := ⟨j, by omega⟩
    have hi : N i ≤ k :=
      (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)).trans hk
    have hh := hN i k hi t ht x hx
    change ‖iteratedFDeriv ℝ j
      ((F.flow.metric t).pullbackCoefficients (endAxialTranslation e (k + 1 : ℕ)) -
        endCylinderCoefficients e t) x‖ < d at hh
    rwa [iteratedFDeriv_sub_apply (hcA.of_le (by exact_mod_cast le_top))
      (hcB.of_le (by exact_mod_cast le_top))] at hh
  constructor
  · intro j hj
    have hb := (hmodel t htL p x hx hxU).1 j hj
    rw [endCylinderFlow_iteratedFDeriv e t htI p j x hxU] at hb
    have he := (herror j hj).le.trans (min_le_left 1 (a / 2))
    calc
      ‖iteratedFDeriv ℝ j ((F.flow.metric t).pullbackCoefficients
          (endAxialTranslation e (k + 1 : ℕ))) x‖ ≤
          ‖iteratedFDeriv ℝ j ((F.flow.metric t).pullbackCoefficients
              (endAxialTranslation e (k + 1 : ℕ))) x -
            iteratedFDeriv ℝ j (endCylinderCoefficients e t) x‖ +
          ‖iteratedFDeriv ℝ j (endCylinderCoefficients e t) x‖ :=
            norm_le_norm_sub_add _ _
      _ ≤ M + 1 := by linarith
  · intro v
    have hb := (hmodel t htL p x hx hxU).2 v
    rw [endCylinderFlow_chart_coefficients e t htI p x hxU] at hb
    have he := hN ⟨0, by decide⟩ k
      ((Finset.single_le_sum (fun j _ => Nat.zero_le (N j))
        (Finset.mem_univ ⟨0, by decide⟩)).trans hk) t ht x hx
    rw [norm_iteratedFDeriv_zero] at he
    have heval := (endCylinderDifferenceCoefficients e F.flow (k + 1) t x).le_opNorm₂ v v
    have hnorm : ‖endCylinderDifferenceCoefficients e F.flow (k + 1) t x‖ ≤ a / 2 :=
      he.le.trans (min_le_right 1 (a / 2))
    have hbound := heval.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)) (norm_nonneg v))
    simp only [endCylinderDifferenceCoefficients, Pi.sub_apply,
      sub_apply, Real.norm_eq_abs] at hbound
    have hlo := (abs_le.mp hbound).1
    nlinarith [sq_nonneg ‖v‖]

end PoincareConjecture.M34
