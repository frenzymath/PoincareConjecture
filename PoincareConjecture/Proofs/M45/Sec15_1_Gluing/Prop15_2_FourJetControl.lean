import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_EvolvingJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_FiniteScalarBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace
noncomputable local instance : NormedAddCommGroup (ScalarMetricFourJet 3) :=
  Prod.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (ScalarMetricFourJet 3) := Prod.normedSpace



theorem metricTwoJet_sub_of_two_derivatives {F G : E → MetricCoefficient 3} {x : E}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G x) :
    metricTwoJet (fun p => F p - G p) x = metricTwoJet F x - metricTwoJet G x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact fderiv_fun_sub (hF.differentiableAt (by norm_num))
      (hG.differentiableAt (by norm_num))
  change fderiv ℝ (fderiv ℝ (fun p => F p - G p)) x =
    fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x
  ext u v : 2
  have h := congrArg (fun L => L ![u, v]) (fun_iteratedFDeriv_sub_apply hF hG)
  simpa only [iteratedFDeriv_two_apply, sub_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using h




theorem scalarMetricFourJet_sub_of_contDiffAt {F G : E → MetricCoefficient 3} {x : E}
    (hF : ContDiffAt ℝ ∞ F x) (hG : ContDiffAt ℝ ∞ G x) :
    scalarMetricFourJet (fun p => F p - G p) x =
      scalarMetricFourJet F x - scalarMetricFourJet G x := by
  have hJ : metricTwoJet (fun p => F p - G p) =ᶠ[𝓝 x]
      (fun p => metricTwoJet F p - metricTwoJet G p) := by
    filter_upwards [(hF.of_le (show (2 : ℕ∞ω) ≤ ∞ by decide)).eventually (by decide),
      (hG.of_le (show (2 : ℕ∞ω) ≤ ∞ by decide)).eventually (by decide)] with p hpF hpG
    exact metricTwoJet_sub_of_two_derivatives hpF hpG
  have hJF := contDiffAt_metricTwoJet hF
  have hJG := contDiffAt_metricTwoJet hG
  apply Prod.ext
  · exact metricTwoJet_sub_of_contDiffAt hF hG
  apply Prod.ext
  · funext i
    change fderiv ℝ (metricTwoJet (fun p => F p - G p)) x _ = _
    rw [hJ.fderiv_eq, fderiv_fun_sub (hJF.differentiableAt (by simp))
      (hJG.differentiableAt (by simp))]
    rfl
  · funext i j
    change fderiv ℝ (fderiv ℝ (metricTwoJet (fun p => F p - G p))) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        fderiv ℝ (fderiv ℝ (metricTwoJet F)) x
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) -
        fderiv ℝ (fderiv ℝ (metricTwoJet G)) x
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
    have h := congrArg
      (fun L => L ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j])
      ((hJ.iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds.trans
        (fun_iteratedFDeriv_sub_apply
          (hJF.of_le (by decide)) (hJG.of_le (by decide))))
    simpa only [iteratedFDeriv_two_apply, sub_apply,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using h

set_option maxHeartbeats 800000 in




theorem exists_evolvingCylinder_fourJet_error :
    ∃ C : ℝ, 0 < C ∧
      ∀ {epsilon t : ℝ}, 0 < epsilon → t ∈ Set.Icc (-1 : ℝ) 0 →
      ∀ {B : RoundCylinderTwoTensor}, RoundCylinderClose epsilon t B →
      4 ≤ ⌊epsilon⁻¹⌋₊ → ∀ z : RoundCylinderSpace,
      z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ‖scalarMetricFourJet (centeredCylinderMetric B z.1 z.2) 0 -
          scalarMetricFourJet (evolvingCylinderModelField t) 0‖ ≤ C * epsilon := by
  choose A hA hAbound using fun j : Fin 5 => exists_evolvingCylinderError_jet_bound j
  let C : ℝ := 1 + ∑ j : Fin 5, A j
  have hsum : 0 ≤ ∑ j : Fin 5, A j := Finset.sum_nonneg fun j _ => (hA j).le
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro epsilon t hepsilon ht B hB horder z hz
  have hF := evolving_centeredCylinderMetric_contDiffAt hB z hz
  have hG := (evolvingCylinderModelField_contDiff t).contDiffAt (x := (0 : E))
  rw [← scalarMetricFourJet_sub_of_contDiffAt hF hG]
  apply norm_scalarMetricFourJet_le (hF.sub hG)
  intro j hj
  let k : Fin 5 := ⟨j, by omega⟩
  apply (hAbound k hepsilon ht hB (hj.trans horder) z hz).trans
  apply mul_le_mul_of_nonneg_right _ hepsilon.le
  have ha := Finset.single_le_sum (fun l _ => (hA l).le) (Finset.mem_univ k)
  dsimp [C]
  linarith

end PoincareConjecture.M45
