import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.SweptDerivatives
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FlowMetricScaling
import PoincareConjecture.Proofs.M58.Mathlib.TwoVectorArea









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65AreaDensity_le_column_norms (g : RiemannianMetric n M)
    (f : LoopPlane → M) (p : LoopPlane) :
    m60AreaDensity g f p ≤
      g.tangentNorm (f p) (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) *
        g.tangentNorm (f p) (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let u := mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let v := mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have harea : m60AreaDensity g f p = Proofs.M58.twoVectorArea u v := by
    unfold m60AreaDensity m60AreaGram Proofs.M58.twoVectorArea
    dsimp only
    erw [Matrix.det_fin_two]
    change Real.sqrt (max 0 (inner ℝ u u * inner ℝ v v - inner ℝ u v * inner ℝ v u)) = _
    rw [real_inner_comm v u, pow_two]
  rw [harea]
  exact Proofs.M58.twoVectorArea_le u v

variable {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}



theorem m65SweptDensity_le {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b) (x y : ℝ) :
    m60AreaDensity (F.metric (s + (t - s) * Real.smoothTransition y))
        (m65SweptMap c s t) (annulusPoint x y) ≤
      ((t - s) * deriv Real.smoothTransition y) *
        m62Curvature F c (s + (t - s) * Real.smoothTransition y) x *
          curveSpeed F c (s + (t - s) * Real.smoothTransition y) x := by
  let tau := s + (t - s) * Real.smoothTransition y
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric tau).toRiemannianMetric⟩
  have h := m65AreaDensity_le_column_norms (F.metric tau) (m65SweptMap c s t)
    (annulusPoint x y)
  rw [m65SweptMap_angular_derivative hc has hst htb,
    m65SweptMap_time_derivative hc has hst htb] at h
  change _ ≤ ‖curveVelocity (n := n) (fun r => c r tau) x‖ *
    ‖((t - s) * deriv Real.smoothTransition y) • m62CurvatureVector F c tau x‖ at h
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.affine_smoothTransition_deriv_nonneg hst y)] at h
  change _ ≤ ((t - s) * deriv Real.smoothTransition y) *
    ‖m62CurvatureVector F c tau x‖ * ‖curveVelocity (n := n) (fun r => c r tau) x‖
  exact h.trans_eq (by ring)




theorem m65SweptDensity_fixedMetric_le {K0 K1 K2 : ℝ}
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2) (hK2 : 0 ≤ K2)
    {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t q : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b)
    (hq : q ∈ Set.Icc a b) (x y : ℝ) :
    m60AreaDensity (F.metric q) (m65SweptMap c s t) (annulusPoint x y) ≤
      Real.exp ((2 * K2) * (b - a)) *
        (((t - s) * deriv Real.smoothTransition y) *
          m62Curvature F c (s + (t - s) * Real.smoothTransition y) x *
            curveSpeed F c (s + (t - s) * Real.smoothTransition y) x) := by
  let tau := s + (t - s) * Real.smoothTransition y
  have htau : tau ∈ Set.Icc a b :=
    ⟨has.le.trans (m65SweptTime_mem hst y).1, (m65SweptTime_mem hst y).2.trans htb.le⟩
  have hdist : |q - tau| ≤ b - a := abs_le.mpr ⟨by linarith [htau.2, hq.1],
    by linarith [htau.1, hq.2]⟩
  have hexp : Real.exp ((2 * K2) * |q - tau|) ≤ Real.exp ((2 * K2) * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdist (mul_nonneg (by norm_num) hK2))
  have hnonneg : 0 ≤ ((t - s) * deriv Real.smoothTransition y) *
      m62Curvature F c tau x * curveSpeed F c tau x :=
    mul_nonneg (mul_nonneg (Real.affine_smoothTransition_deriv_nonneg hst y)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  exact (m65FlowAreaDensity_scaling F bounds htau hq (m65SweptMap c s t)
    (annulusPoint x y)).trans
      ((mul_le_mul_of_nonneg_left (m65SweptDensity_le hc has hst htb x y)
        (Real.exp_nonneg _)).trans (mul_le_mul_of_nonneg_right hexp hnonneg))

end PoincareConjecture
