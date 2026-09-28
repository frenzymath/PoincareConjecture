import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.PotentialLevels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Regularity.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

def potentialGradientScale (S : GradientShrinkingSolitonData 3 M) (q : M) : ℝ :=
  S.metric.tangentNorm q (S.connection.gradient S.potential q)

def normalizedPotential (S : GradientShrinkingSolitonData 3 M) (q x : M) : ℝ :=
  (S.potential x - S.potential q) / S.potentialGradientScale q

theorem potentialGradientScale_nonneg (S : GradientShrinkingSolitonData 3 M) (q : M) :
    0 ≤ S.potentialGradientScale q := Real.sqrt_nonneg _

theorem potentialGradientScale_sq (S : GradientShrinkingSolitonData 3 M) (q : M) :
    S.potentialGradientScale q ^ 2 = S.metric.inner q
      (S.connection.gradient S.potential q) (S.connection.gradient S.potential q) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨S.metric.toRiemannianMetric⟩
  change ‖S.connection.gradient S.potential q‖ ^ 2 =
    inner ℝ (S.connection.gradient S.potential q) (S.connection.gradient S.potential q)
  exact (real_inner_self_eq_norm_sq _).symm

@[simp] theorem normalizedPotential_center (S : GradientShrinkingSolitonData 3 M) (q : M) :
    S.normalizedPotential q q = 0 := by simp [normalizedPotential]

theorem normalizedPotential_contMDiff (S : GradientShrinkingSolitonData 3 M) (q : M) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (S.normalizedPotential q) := by
  change ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
    (fun x => (S.potential x - S.potential q) / S.potentialGradientScale q)
  exact (S.potential_contMDiff.sub contMDiff_const).div_const (S.potentialGradientScale q)

theorem gradient_normalizedPotential (S : GradientShrinkingSolitonData 3 M) (q x : M) :
    S.connection.gradient (S.normalizedPotential q) x =
      (S.potentialGradientScale q)⁻¹ • S.connection.gradient S.potential x := by
  apply (S.metric.inner_isInvertible x).injective
  ext v
  rw [S.connection.inner_gradient]
  have heq : S.normalizedPotential q = fun y =>
      (S.potentialGradientScale q)⁻¹ * (S.potential y - S.potential q) := by
    funext y
    simp only [normalizedPotential, div_eq_mul_inv, mul_comm]
  rw [heq, mvfderiv_const_mul,
    mvfderiv_fun_sub ((S.potential_contMDiff x).mdifferentiableAt (by simp))
      mdifferentiableAt_const]
  simp only [mvfderiv_const, sub_zero, map_smul, smul_apply, smul_eq_mul,
    S.connection.inner_gradient]

theorem normalizedPotential_gradient_sq_center (S : GradientShrinkingSolitonData 3 M)
    {q : M} (hq : 0 < S.potentialGradientScale q) :
    S.metric.inner q (S.connection.gradient (S.normalizedPotential q) q)
      (S.connection.gradient (S.normalizedPotential q) q) = 1 := by
  simp only [S.gradient_normalizedPotential, map_smul, smul_apply,
    smul_eq_mul, ← S.potentialGradientScale_sq]
  field_simp [hq.ne']

theorem hessian_normalizedPotential (S : GradientShrinkingSolitonData 3 M) (q x : M)
    (u v : TangentSpace (𝓡 3) x) :
    S.connection.hessian (S.normalizedPotential q) x u v =
      (S.potentialGradientScale q)⁻¹ * S.connection.hessian S.potential x u v := by
  have heq : S.normalizedPotential q = fun y =>
      (S.potentialGradientScale q)⁻¹ * (-S.potential q + S.potential y) := by
    funext y
    simp only [normalizedPotential, div_eq_mul_inv]
    ring
  rw [heq, S.connection.hessian_const_mul,
    S.connection.hessian_const_add_at (S.potential_contMDiff x)]

theorem potential_tendsto_atTop_of_escape (S : GradientShrinkingSolitonData 3 M)
    (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop) :
    Tendsto (fun k => S.potential (q k)) atTop atTop := by
  obtain ⟨C, hC, hbound⟩ := S.exists_potential_distance_lower_bound p
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hescape.eventually_ge_atTop (8 * C + 8 * |B - S.potential p| + 1)]
    with k hk
  have hd : 0 ≤ (S.metric.edist p (q k)).toReal := ENNReal.toReal_nonneg
  have hCd : 0 ≤ (S.metric.edist p (q k)).toReal *
      ((S.metric.edist p (q k)).toReal - 8 * C) :=
    mul_nonneg hd (by linarith [abs_nonneg (B - S.potential p)])
  have hdd : 0 ≤ (S.metric.edist p (q k)).toReal *
      ((S.metric.edist p (q k)).toReal - 1) :=
    mul_nonneg hd (by linarith [abs_nonneg (B - S.potential p)])
  have ha := le_abs_self (B - S.potential p)
  have hb := hbound (q k)
  nlinarith

theorem potentialGradientScale_tendsto_atTop_of_escape
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop) :
    Tendsto (fun k => S.potentialGradientScale (q k)) atTop atTop := by
  have hf := S.potential_tendsto_atTop_of_escape p q hescape
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨a, ha⟩ := S.exists_gradient_sq_gt_on_superlevel hD ((max B 0) ^ 2)
  filter_upwards [hf.eventually_ge_atTop a] with k hk
  have h := ha (q k) hk
  rw [← S.potentialGradientScale_sq] at h
  have hn := S.potentialGradientScale_nonneg (q k)
  have hm : 0 ≤ max B 0 := le_max_right _ _
  have hB : B ≤ max B 0 := le_max_left _ _
  nlinarith

theorem exists_normalizedPotential_hessian_bound
    (S : GradientShrinkingSolitonData 3 M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q x : M, ∀ v : TangentSpace (𝓡 3) x,
      |S.connection.hessian (S.normalizedPotential q) x v v| ≤
        C / S.potentialGradientScale q * S.metric.inner x v v := by
  obtain ⟨C, hC, hbound⟩ := S.exists_hessian_quadratic_bound
  refine ⟨C, hC, fun q x v => ?_⟩
  rw [S.hessian_normalizedPotential, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (S.potentialGradientScale_nonneg q))]
  calc
    (S.potentialGradientScale q)⁻¹ * |S.connection.hessian S.potential x v v| ≤
        (S.potentialGradientScale q)⁻¹ * (C * S.metric.inner x v v) :=
      mul_le_mul_of_nonneg_left (hbound x v)
        (inv_nonneg.mpr (S.potentialGradientScale_nonneg q))
    _ = C / S.potentialGradientScale q * S.metric.inner x v v := by ring

theorem normalizedPotential_hessian_eventually_lt
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      S.metric.inner x v v ≤ 1 →
      |S.connection.hessian (S.normalizedPotential (q k)) x v v| < ε := by
  obtain ⟨C, hC, hbound⟩ := S.exists_normalizedPotential_hessian_bound
  have ha := S.potentialGradientScale_tendsto_atTop_of_escape hD p q hescape
  filter_upwards [ha.eventually_gt_atTop (C / ε + 1)] with k hk
  have hscale : 0 < S.potentialGradientScale (q k) := by
    linarith [div_nonneg hC hε.le]
  have hsmall : C / S.potentialGradientScale (q k) < ε := by
    apply (div_lt_iff₀ hscale).mpr
    have hm := (div_lt_iff₀ hε).mp (show C / ε < S.potentialGradientScale (q k) by linarith)
    nlinarith
  intro x v hv
  exact (hbound (q k) x v).trans_lt
    ((mul_le_of_le_one_right (div_nonneg hC hscale.le) hv).trans_lt hsmall)

end PoincareConjecture.GradientShrinkingSolitonData
