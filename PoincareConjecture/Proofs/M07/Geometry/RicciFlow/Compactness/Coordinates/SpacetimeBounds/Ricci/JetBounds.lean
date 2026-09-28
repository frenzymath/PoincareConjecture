import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Curvature.MetricBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.Ricci

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

open CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem norm_iteratedFDeriv_inverseCoefficients_le
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (q : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ‖iteratedFDeriv ℝ q (fun y => g.inverseCoefficients y i j) x‖ ≤
      ‖iteratedFDeriv ℝ q (fun y => (g.euclideanCoefficients y).inverse) x‖ := by
  have hi : (g.euclideanCoefficients x).IsInvertible := g.inner_isInvertible x
  have hI := hi.contDiffAt_map_inverse.comp x
    (g.contDiffAt_euclideanCoefficients x)
  have hp (k : Fin n) : ‖EuclideanSpace.proj (𝕜 := ℝ) k‖ = 1 := by
    have heq : EuclideanSpace.proj (𝕜 := ℝ) k =
        innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      ext v
      simp only [PiLp.proj_apply, innerSL_apply_apply, EuclideanSpace.basisFun_inner]
    rw [heq, innerSL_apply_norm, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one]
  have hq : (q : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have h₁ := (EuclideanSpace.proj (𝕜 := ℝ) j).norm_iteratedFDeriv_comp_left
    (hI.clm_apply (contDiffAt_const (c := EuclideanSpace.proj (𝕜 := ℝ) i))) hq
  have h₂ := norm_iteratedFDeriv_clm_apply_const (c := EuclideanSpace.proj (𝕜 := ℝ) i) hI hq
  rw [hp j, one_mul] at h₁
  rw [hp i, one_mul] at h₂
  exact h₁.trans h₂

theorem exists_affine_ricci_component_jet_bound
    (n q : ℕ) (c : ℝ) (hc : 0 ≤ c) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a : ℝ} (ha : 0 < a) (b A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
        (x : EuclideanSpace ℝ (Fin n)),
        ‖g.euclideanCoefficients x‖ ≤ b →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v) →
        (∀ v, g.tangentNorm x v ≤ c * ‖v‖) →
        (∀ s ≤ q + 1, D.curvatureDerivativeNorm s x ≤ K s) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ A ^ j) →
        ∀ p r : Fin n, ‖iteratedFDeriv ℝ (q + 1)
          (fun y => D.ricci y (EuclideanSpace.basisFun (Fin n) ℝ p)
            (EuclideanSpace.basisFun (Fin n) ℝ r)) x‖ ≤
          C * (1 + ‖iteratedFDeriv ℝ (q + 1) g.euclideanCoefficients x‖) := by
  classical
  obtain ⟨I, hI, hinv⟩ := exists_uniform_inverse_metric_jet_bound
    (E := EuclideanSpace ℝ (Fin n)) q ha b A hA
  obtain ⟨I', hI', hinv'⟩ := exists_affine_inverse_metric_jet_bound
    (E := EuclideanSpace ℝ (Fin n)) q ha b A hA
  obtain ⟨R, hR, hrm⟩ := exists_uniform_coordinate_curvature_jet_bound_of_metric
    n q 0 c hc K hK ha b A hA
  obtain ⟨R', hR', hrm'⟩ := exists_affine_coordinate_curvature_jet_bound
    n q 0 c hc K hK ha b A hA
  let L := ContinuousLinearMap.mul ℝ ℝ
  let S : ℝ := ∑ i ∈ Finset.range (q + 2), ((q + 1).choose i : ℝ)
  let C : ℝ := ‖L‖ * (I * R' + I' * R + I * R) * S
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨(n : ℝ) * (n * C), by positivity, ?_⟩
  intro g D x hnorm hell hm hcurv hjets p r
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let T : ℝ := 1 + ‖iteratedFDeriv ℝ (q + 1) g.euclideanCoefficients x‖
  have hT : 1 ≤ T := le_add_of_nonneg_right (norm_nonneg _)
  have hinv₀ := hinv g.euclideanCoefficients x (g.contDiffAt_euclideanCoefficients x)
    hnorm hell hjets
  have hinv₁ := hinv' g.euclideanCoefficients x (g.contDiffAt_euclideanCoefficients x)
    hnorm hell hjets
  have hrm₀ := hrm g D e x hnorm hell hm (fun s hs => hcurv s (by omega)) hjets
  have hrm₁ := hrm' g D e x hnorm hell hm (fun s hs => hcurv s (by omega)) hjets
  let f (i j : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    g.inverseCoefficients y i j * coordinateCurvatureComponent D 0
      (fun k => e (![p, i, r, j] k)) y
  have hf (i j : Fin n) : ContDiffAt ℝ ∞ (f i j) x :=
    (g.contDiff_inverseCoefficients i j).contDiffAt.mul
      (contDiff_coordinateCurvatureComponent D 0 _).contDiffAt
  have hbound (i j : Fin n) : ‖iteratedFDeriv ℝ (q + 1) (f i j) x‖ ≤ C * T := by
    apply norm_iteratedFDeriv_bilinear_le_affine_highest L
      (g.contDiff_inverseCoefficients i j).contDiffAt
      (contDiff_coordinateCurvatureComponent D 0 _).contDiffAt q hI hR hI' hR' hT
    · intro s hs
      exact (norm_iteratedFDeriv_inverseCoefficients_le g s x i j).trans (hinv₀ s hs)
    · intro s hs
      exact hrm₀ s hs _
    · exact (norm_iteratedFDeriv_inverseCoefficients_le g (q + 1) x i j).trans hinv₁
    · exact hrm₁ _
  have heq : (fun y => D.ricci y (e p) (e r)) = fun y => ∑ i, ∑ j, f i j y := by
    funext y
    rw [D.ricci_eq_sum_inverseCoefficients_curvatureTensor]
    rfl
  rw [heq]
  have hsum (i : Fin n) := norm_iteratedFDeriv_sum_le_const
    (fun j => (hf i j).of_le (by exact_mod_cast le_top)) (hbound i)
  have hsmooth (i : Fin n) : ContDiffAt ℝ (q + 1) (fun y => ∑ j, f i j y) x :=
    ContDiffAt.sum (fun j _ => (hf i j).of_le (by exact_mod_cast le_top))
  have hsum₂ := norm_iteratedFDeriv_sum_le_const hsmooth hsum
  apply hsum₂.trans_eq
  simp only [Fintype.card_fin]
  ring

end PoincareConjecture.SpacetimeBounds
