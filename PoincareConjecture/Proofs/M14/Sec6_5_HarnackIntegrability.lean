import PoincareConjecture.Proofs.M14.Sec6_5_SquareScalarEnergy
import PoincareConjecture.Proofs.M14.Sec6_2_SquarePullback

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem scalar_transport_smul {q r : G.Point} (h : q = r)
    (v : G.Horizontal r) (c : ℝ) :
    M14HorizontalScalarDifferential G q (h.symm ▸ (c • v)).val =
      c * M14HorizontalScalarDifferential G r v.val := by
  cases h
  change M14HorizontalScalarDifferential G q (c • v.val) = _
  rw [map_smul, smul_eq_mul]

private theorem ricci_transport_smul (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {q r : G.Point} (h : q = r) (v : G.Horizontal r) (c : ℝ) :
    horizontalRicci G.leafwise q (h.symm ▸ (c • v)) (h.symm ▸ (c • v)) =
      c ^ 2 * horizontalRicci G.leafwise r v v := by
  cases h
  rw [horizontalRicci_smul_left hM12, horizontalRicci_smul_right hM12]
  ring

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}

theorem squareRoot_weightedHarnack_eq
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hEuler : ∀ W, M14SquareRootEulerResidual G R E s W = 0) :
    s ^ 2 * s * M14GeneralizedHarnackDensity G p
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          (p.curve t)) (s ^ 2) =
      -s * horizontalScalarCurvature G.leafwise (R.curve s) -
        (s ^ 2 / 2) * derivWithin
          (fun r => horizontalScalarCurvature G.leafwise (R.curve r))
          (M14SqrtParameterInterval τ₁ τ₂) s -
        derivWithin (fun r => G.spacetime.horizontalMetric.inner (R.curve r)
          (R.horizontal_velocity r) (R.horizontal_velocity r))
          (M14SqrtParameterInterval τ₁ τ₂) s / 8 := by
  have hsC : s ∈ M14SqrtParameterInterval τ₁ τ₂ := Ioo_subset_Icc_self hs
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hS := (squareRoot_scalar_hasDerivWithinAt hM12 R hsC).derivWithin (hC s hsC)
  have hE := (squareRoot_energy_hasDerivWithinAt R E hsC hEuler).derivWithin (hC s hsC)
  have hbase := R.agrees s hsC
  have hscalar : M14HorizontalScalarDifferential G (R.curve s) (R.horizontal_velocity s).val =
      (2 * s) * M14HorizontalScalarDifferential G (p.curve (s ^ 2))
        (p.horizontal_velocity (s ^ 2)).val := by
    rw [R.horizontal_agrees s hs]
    exact scalar_transport_smul hbase _ _
  have hricci : horizontalRicci G.leafwise (R.curve s)
      (R.horizontal_velocity s) (R.horizontal_velocity s) =
        (2 * s) ^ 2 * horizontalRicci G.leafwise (p.curve (s ^ 2))
          (p.horizontal_velocity (s ^ 2)) (p.horizontal_velocity (s ^ 2)) := by
    rw [R.horizontal_agrees s hs]
    exact ricci_transport_smul hM12 hbase _ _
  rw [hS, hE, hscalar, hricci, hbase]
  unfold M14GeneralizedHarnackDensity M14HorizontalScalarDifferential
  have hs0 : s ≠ 0 := ((Real.sqrt_nonneg τ₁).trans_lt hs.1).ne'
  field_simp [hs0]
  ring

theorem squareRoot_weightedHarnack_intervalIntegrable
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity)
    (hEuler : ∀ s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      ∀ W, M14SquareRootEulerResidual G R E s W = 0) :
    IntervalIntegrable (fun t => t * Real.sqrt t * M14GeneralizedHarnackDensity G p
      (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
        (p.curve r)) t) MeasureTheory.volume τ₁ τ₂ := by
  let C := M14SqrtParameterInterval τ₁ τ₂
  let S : ℝ → ℝ := fun s => horizontalScalarCurvature G.leafwise (R.curve s)
  let K : ℝ → ℝ := fun s => G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (R.horizontal_velocity s)
  let H : ℝ → ℝ := fun s => -s * S s - (s ^ 2 / 2) * derivWithin S C s -
    derivWithin K C s / 8
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hS : ContDiffOn ℝ ∞ S C := squareRoot_scalar_contDiffOn hM12 R
  have hK : ContDiffOn ℝ ∞ K C := squareRoot_energy_contDiffOn R
  have hH : ContinuousOn H C :=
    ((continuousOn_id.neg.mul hS.continuousOn).sub
      (((continuousOn_id.pow 2).div_const 2).mul
        (hS.derivWithin hC (m := ∞) (by simp)).continuousOn)).sub
          ((hK.derivWithin hC (m := ∞) (by simp)).continuousOn.div_const 8)
  have hcomp : ContinuousOn (fun t => H (Real.sqrt t)) (Icc τ₁ τ₂) :=
    hH.comp Real.continuous_sqrt.continuousOn
      (fun _ ht => ⟨Real.sqrt_le_sqrt ht.1, Real.sqrt_le_sqrt ht.2⟩)
  apply (hcomp.intervalIntegrable_of_Icc p.tau_lt.le).congr_uIoo
  intro t ht
  rw [uIoo_of_le p.tau_lt.le] at ht
  have ht0 : 0 < t := p.tau_nonneg.trans_lt ht.1
  have hs : Real.sqrt t ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) :=
    ⟨Real.sqrt_lt_sqrt p.tau_nonneg ht.1, Real.sqrt_lt_sqrt ht0.le ht.2⟩
  have h := squareRoot_weightedHarnack_eq hM12 R E hs (hEuler _ hs)
  simpa only [H, S, K, C, Real.sq_sqrt ht0.le] using h.symm

end PoincareConjecture.M14
