import PoincareConjecture.Proofs.M08.PathBasics
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture.M08

private theorem component_sq_le_sum {d : ℕ}
    (A : Fin d → Fin d → Fin d → Fin d → ℝ) (i j k l : Fin d) :
    A i j k l ^ 2 ≤ ∑ a, ∑ b, ∑ c, ∑ e, A a b c e ^ 2 := by
  calc
    A i j k l ^ 2 ≤ ∑ e, A i j k e ^ 2 :=
      Finset.single_le_sum (f := fun e ↦ A i j k e ^ 2)
        (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ l)
    _ ≤ ∑ c, ∑ e, A i j c e ^ 2 :=
      Finset.single_le_sum (f := fun c ↦ ∑ e, A i j c e ^ 2)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ b, ∑ c, ∑ e, A i b c e ^ 2 :=
      Finset.single_le_sum (f := fun b ↦ ∑ c, ∑ e, A i b c e ^ 2)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ e, A a b c e ^ 2 :=
      Finset.single_le_sum (f := fun a ↦ ∑ b, ∑ c, ∑ e, A a b c e ^ 2)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        (Finset.mem_univ i)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]


theorem scalarCurvature_abs_le_tensorNorm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) :
    |D.scalarCurvature x| ≤ (n : ℝ) ^ 2 * D.curvatureTensorNorm x := by
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let A : Fin d → Fin d → Fin d → Fin d → ℝ :=
    fun i j k l ↦ D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hdim : d = n := finrank_euclideanSpace_fin
  have hcomp (i j : Fin d) : |A i j i j| ≤ D.curvatureTensorNorm x := by
    have h := Real.sqrt_le_sqrt (component_sq_le_sum A i j i j)
    rw [Real.sqrt_sq_eq_abs] at h
    exact h
  change |∑ i, ∑ j, A i j i j| ≤ _
  calc
    |∑ i, ∑ j, A i j i j| ≤ ∑ i, ∑ j, |A i j i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, D.curvatureTensorNorm x :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hcomp i j
    _ = (n : ℝ) ^ 2 * D.curvatureTensorNorm x := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      ring


noncomputable def backwardLPotential {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (τ : ℝ) : ℝ :=
  Real.sqrt τ * (F.connection (T - τ)).scalarCurvature (γ τ)


noncomputable def backwardLKinetic {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (τ : ℝ) : ℝ :=
  Real.sqrt τ * (F.metric (T - τ)).inner (γ τ)
    (curveVelocity (n := n) γ τ) (curveVelocity (n := n) γ τ)

theorem backwardLKinetic_nonneg {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (τ : ℝ) : 0 ≤ backwardLKinetic F T γ τ := by
  apply mul_nonneg (Real.sqrt_nonneg τ)
  by_cases hv : curveVelocity (n := n) γ τ = 0
  · simp [hv]
  · exact ((F.metric (T - τ)).pos (γ τ) _ hv).le

theorem backwardLIntegrand_eq_potential_add_kinetic {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M) (τ : ℝ) :
    backwardLIntegrand F T γ τ =
      backwardLPotential F T γ τ + backwardLKinetic F T γ τ := by
  exact mul_add _ _ _


theorem backwardLPotential_continuousOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (p : BackwardTimePath F T τ₁ τ₂) :
    ContinuousOn (backwardLPotential F T p.curve) (Set.Icc τ₁ τ₂) := by
  have hscalar := (hM04.scalar_regular n M J F).continuousOn.comp
    ((continuous_const.sub continuous_id).continuousOn.prodMk p.continuous)
    (fun τ hτ ↦ ⟨p.time_mem τ hτ, Set.mem_univ _⟩)
  exact Real.continuous_sqrt.continuousOn.mul hscalar

theorem backwardLPotential_intervalIntegrable {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (p : BackwardTimePath F T τ₁ τ₂) :
    IntervalIntegrable (backwardLPotential F T p.curve) MeasureTheory.volume τ₁ τ₂ := by
  apply ContinuousOn.intervalIntegrable
  simpa only [Set.uIcc_of_le p.ordered.le] using backwardLPotential_continuousOn hM04 p

theorem backwardLKinetic_intervalIntegrable {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (p : BackwardTimePath F T τ₁ τ₂) :
    IntervalIntegrable (backwardLKinetic F T p.curve) MeasureTheory.volume τ₁ τ₂ := by
  have h := p.l_integrable.sub (backwardLPotential_intervalIntegrable hM04 p)
  convert h using 1
  funext τ
  rw [backwardLIntegrand_eq_potential_add_kinetic]
  ring

theorem backwardLPotential_abs_le {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ K : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (hτ₂ : τ₂ ≤ τmax)
    (hbound : ∀ t ∈ Set.Icc (T - τmax) T, ∀ x : M,
      |(F.connection t).curvatureTensorNorm x| ≤ K)
    {τ : ℝ} (hτ : τ ∈ Set.Icc τ₁ τ₂) :
    |backwardLPotential F T p.curve τ| ≤ Real.sqrt τ₂ * (n : ℝ) ^ 2 * K := by
  have hscalar : |(F.connection (T - τ)).scalarCurvature (p.curve τ)| ≤
      (n : ℝ) ^ 2 * K :=
    (scalarCurvature_abs_le_tensorNorm _ _).trans
      (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans
          (hbound _ (backwardTime_mem_window p.nonnegative hτ₂ hτ) _)) (sq_nonneg _))
  rw [backwardLPotential, abs_mul, abs_of_nonneg (Real.sqrt_nonneg τ)]
  calc
    Real.sqrt τ * |(F.connection (T - τ)).scalarCurvature (p.curve τ)| ≤
        Real.sqrt τ₂ * |(F.connection (T - τ)).scalarCurvature (p.curve τ)| :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hτ.2) (abs_nonneg _)
    _ ≤ Real.sqrt τ₂ * ((n : ℝ) ^ 2 * K) :=
      mul_le_mul_of_nonneg_left hscalar (Real.sqrt_nonneg _)
    _ = _ := by ring


theorem backwardLLength_coercive {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ K : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (p : BackwardTimePath F T τ₁ τ₂) (hτ₂ : τ₂ ≤ τmax)
    (hbound : ∀ t ∈ Set.Icc (T - τmax) T, ∀ x : M,
      |(F.connection t).curvatureTensorNorm x| ≤ K) :
    let C := Real.sqrt τ₂ * (n : ℝ) ^ 2 * K;
    -C * (τ₂ - τ₁) ≤ backwardLLength F T τ₁ τ₂ p.curve ∧
      (∫ τ in τ₁..τ₂, backwardLKinetic F T p.curve τ) ≤
        backwardLLength F T τ₁ τ₂ p.curve + C * (τ₂ - τ₁) := by
  dsimp only
  let C := Real.sqrt τ₂ * (n : ℝ) ^ 2 * K
  have hp := backwardLPotential_intervalIntegrable hM04 p
  have hk := backwardLKinetic_intervalIntegrable hM04 p
  have heq : backwardLLength F T τ₁ τ₂ p.curve =
      (∫ τ in τ₁..τ₂, backwardLPotential F T p.curve τ) +
      (∫ τ in τ₁..τ₂, backwardLKinetic F T p.curve τ) := by
    unfold backwardLLength
    simp_rw [backwardLIntegrand_eq_potential_add_kinetic]
    exact intervalIntegral.integral_add hp hk
  have hpot : -C * (τ₂ - τ₁) ≤
      ∫ τ in τ₁..τ₂, backwardLPotential F T p.curve τ := by
    have h := intervalIntegral.integral_mono_on p.ordered.le
      (intervalIntegrable_const (c := -C)) hp
      (fun τ hτ ↦ (abs_le.mp (backwardLPotential_abs_le p hτ₂ hbound hτ)).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hkin : 0 ≤ ∫ τ in τ₁..τ₂, backwardLKinetic F T p.curve τ :=
    intervalIntegral.integral_nonneg p.ordered.le (fun τ _ ↦ backwardLKinetic_nonneg F T _ τ)
  constructor <;> change _ ≤ _ <;> linarith

end PoincareConjecture.M08
