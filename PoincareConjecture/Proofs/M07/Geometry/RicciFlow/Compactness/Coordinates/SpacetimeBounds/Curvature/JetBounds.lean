import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Curvature.Recurrence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

open CoordinateExponential LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem abs_coordinateCurvatureComponent_le (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (l : ℕ) (J : Fin (4 + l) → Fin n) (x : EuclideanSpace ℝ (Fin n))
    {c K : ℝ} (_hc : 0 ≤ c) (hK : 0 ≤ K)
    (hmetric : ∀ v, g.tangentNorm x v ≤ c * ‖v‖)
    (hcurv : D.curvatureDerivativeNorm l x ≤ K) :
    |coordinateCurvatureComponent D l (fun j => b (J j)) x| ≤ K * c ^ (4 + l) := by
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model l).1 x
  have heval := abs_tensor_evaluation_le_tensorNorm g _ x A hA (fun j => b (J j))
  have hprod : (∏ j : Fin (4 + l), g.tangentNorm x (b (J j))) ≤ c ^ (4 + l) := by
    calc
      _ ≤ ∏ _j : Fin (4 + l), c := Finset.prod_le_prod
        (fun _ _ => Real.sqrt_nonneg _) (fun j _ => by
          simpa only [RiemannianMetric.tangentNorm, b.norm_eq_one, mul_one] using
            hmetric (b (J j)))
      _ = _ := by simp
  exact heval.trans (mul_le_mul hcurv hprod
    (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) hK)

theorem norm_iteratedFDeriv_coordinateCurvatureComponent_succ_le
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (l q : ℕ) (B C C' : ℕ → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hB : ∀ j ≤ q, ∀ i a u, ‖iteratedFDeriv ℝ j
      (fun y => b.repr (christoffelBilinear g.euclideanCoefficients y u (b i)) a) x‖ ≤
        B j * ‖u‖)
    (hC : ∀ j ≤ q, ∀ J : Fin (4 + l) → Fin n,
      ‖iteratedFDeriv ℝ j (coordinateCurvatureComponent D l (fun i => b (J i))) x‖ ≤ C j)
    (hC' : ∀ J : Fin (4 + (l + 1)) → Fin n,
      ‖iteratedFDeriv ℝ q (coordinateCurvatureComponent D (l + 1) (fun i => b (J i))) x‖ ≤ C' q)
    (J : Fin (4 + l) → Fin n) :
    ‖iteratedFDeriv ℝ (q + 1) (coordinateCurvatureComponent D l (fun i => b (J i))) x‖ ≤
      n * |C' q| + n * (4 + l) * scalarJetProductBound q B C := by
  classical
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  have hq : (q : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl q
  let K (m : ℕ) (Q : Fin (4 + m) → Fin n) :=
    coordinateCurvatureComponent D m (fun j => b (Q j))
  have hK (m : ℕ) (Q : Fin (4 + m) → Fin n) : ContDiff ℝ q (K m Q) :=
    (contDiff_coordinateCurvatureComponent D m _).of_le hq
  have hω (i a u) : ContDiff ℝ q (fun y => b.repr (Γ y u (b i)) a) := by
    have h := (innerSL ℝ (b a)).contDiff.comp
      ((hΓ.clm_apply (contDiff_const (c := u))).clm_apply (contDiff_const (c := b i)))
    simpa only [OrthonormalBasis.repr_apply_apply, innerSL_apply_apply,
      Function.comp_def] using h.of_le hq
  apply norm_iteratedFDeriv_succ_le_of_directional isOpen_univ
    (contDiff_coordinateCurvatureComponent D l _).contDiffOn (mem_univ x) q
    (by have := scalarJetProductBound_nonneg q B C; positivity)
  intro u
  let f₁ (a : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    b.repr u a * K (l + 1) (Fin.cons a J) y
  let f₂ (i : Fin (4 + l)) (a : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    b.repr (Γ y u (b (J i))) a * K l (Function.update J i a) y
  have hf₁ (a) : ContDiff ℝ q (f₁ a) := contDiff_const.mul (hK _ _)
  have hf₂ (i a) : ContDiff ℝ q (f₂ i a) := (hω (J i) a u).mul (hK _ _)
  have h₁ (a) : ‖iteratedFDeriv ℝ q (f₁ a) x‖ ≤ |C' q| * ‖u‖ := by
    have hrepr : |b.repr u a| ≤ ‖u‖ := by
      simpa only [OrthonormalBasis.repr_apply_apply, b.norm_eq_one, one_mul] using
        abs_real_inner_le_norm (b a) u
    change ‖iteratedFDeriv ℝ q (fun y => b.repr u a • K (l + 1) (Fin.cons a J) y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hK _ _).contDiffAt, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ ‖u‖ * |C' q| := mul_le_mul hrepr ((hC' _).trans (le_abs_self _))
        (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have h₂ (i a) : ‖iteratedFDeriv ℝ q (f₂ i a) x‖ ≤ scalarJetProductBound q B C * ‖u‖ :=
    norm_iteratedFDeriv_mul_le_scaled_bound isOpen_univ (hω (J i) a u).contDiffOn
      (hK _ _).contDiffOn (mem_univ x) B C (norm_nonneg _)
      (fun j hj => hB j hj (J i) a u) (fun j hj => hC j hj _)
  have hs₁ : ContDiffAt ℝ q (fun y => ∑ a, f₁ a y) x :=
    ContDiffAt.sum (fun a _ => (hf₁ a).contDiffAt)
  have hs₂ (i) : ContDiffAt ℝ q (fun y => ∑ a, f₂ i a y) x :=
    ContDiffAt.sum (fun a _ => (hf₂ i a).contDiffAt)
  have hsum₁ := norm_iteratedFDeriv_sum_le_const (fun a => (hf₁ a).contDiffAt) h₁
  have hsum₂ (i) := norm_iteratedFDeriv_sum_le_const (fun a => (hf₂ i a).contDiffAt) (h₂ i)
  have hsum₃ := norm_iteratedFDeriv_sum_le_const hs₂ hsum₂
  have heq : (fun y => fderiv ℝ (K l J) y u) =
      (fun y => (∑ a, f₁ a y) + ∑ i, ∑ a, f₂ i a y) := by
    funext y
    exact fderiv_coordinateCurvatureComponent_eq_sum D b l J y u
  change ‖iteratedFDeriv ℝ q (fun y => fderiv ℝ (K l J) y u) x‖ ≤ _
  rw [heq, fun_iteratedFDeriv_add_apply hs₁ (ContDiffAt.sum (fun i _ => hs₂ i))]
  refine (norm_add_le _ _).trans ((add_le_add hsum₁ hsum₃).trans_eq ?_)
  simp only [Fintype.card_fin]
  push_cast
  ring

end PoincareConjecture.SpacetimeBounds
