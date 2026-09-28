import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Coefficients

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture.CoordinateMetric

variable {n : ℕ}

def matrixForm (A : Fin n → Fin n → ℝ) : Form n :=
  ∑ i, ∑ j, A i j • (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (EuclideanSpace.proj i)

theorem matrixForm_apply (A : Fin n → Fin n → ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    matrixForm A v w = ∑ i, ∑ j, A i j * v j * w i := by
  simp [matrixForm, mul_assoc]

theorem continuous_matrixForm : Continuous (matrixForm (n := n)) := by
  let : ContinuousAdd (Form n) :=
    (inferInstance : IsTopologicalAddGroup (Form n)).toContinuousAdd
  unfold matrixForm
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (continuous_apply_apply i j).smul continuous_const

theorem exists_eventually_uniform_ellipticity
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {A : X → Fin n → Fin n → ℝ} (hA : ContinuousOn A K)
    (hpos : ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < ∑ i, ∑ j, A x i j * v j * v i)
    {Aseq : ℕ → X → Fin n → Fin n → ℝ}
    (hconv : TendstoUniformlyOn Aseq A atTop K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ w : Fin n → ℝ,
      c * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ j, Aseq k x i j * w j * w i := by
  have hcont : ContinuousOn (fun x => matrixForm (A x)) K :=
    continuous_matrixForm.comp_continuousOn hA
  obtain ⟨c, hc, hcoercive⟩ := exists_uniform_bilinear_family_lower_bound hK hcont
    (fun x hx v hv => by simpa only [matrixForm_apply] using hpos x hx v hv)
  have hform := tendstoUniformlyOn_comp_of_compact
    (Y := Fin n → Fin n → ℝ) (Z := Form n) (H := matrixForm)
    hK isOpen_univ hA (mapsTo_univ _ _) hconv continuous_matrixForm.continuousOn
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff (α := Form n)).mp hform (c / 2) (half_pos hc)]
    with k hk x hx w
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 w
  have hdiff : ‖matrixForm (Aseq k x) - matrixForm (A x)‖ ≤ c / 2 := by
    have hd := (hk x hx).le
    rw [dist_eq_norm (matrixForm (A x)) (matrixForm (Aseq k x))] at hd
    rwa [norm_sub_rev (matrixForm (A x)) (matrixForm (Aseq k x))] at hd
  have herr : |(matrixForm (Aseq k x) - matrixForm (A x)) v v| ≤
      c / 2 * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖matrixForm (Aseq k x) - matrixForm (A x)‖ * ‖v‖ * ‖v‖ :=
        (matrixForm (Aseq k x) - matrixForm (A x)).le_opNorm₂ v v
      _ ≤ c / 2 * ‖v‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdiff (norm_nonneg v)) (norm_nonneg v)
  have hl := hcoercive x hx v
  have he : c / 2 * ‖v‖ ^ 2 ≤ matrixForm (Aseq k x) v v := by
    simp only [sub_apply] at herr
    linarith [(abs_le.mp herr).1]
  simpa only [matrixForm_apply, EuclideanSpace.real_norm_sq_eq, v, WithLp.ofLp_toLp]
    using he

end PoincareConjecture.CoordinateMetric
