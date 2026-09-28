import PoincareConjecture.Proofs.M04.CurvatureFirstVariation
import PoincareConjecture.Proofs.M04.RicciTraceVariation
import PoincareConjecture.Proofs.M04.ScalarTraceVariation
import PoincareConjecture.Proofs.M04.ScalarContractions








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_scalarCurvature_evolution (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    HasDerivAt (fun s ↦ (F.connection s).scalarCurvature x)
      ((F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x) t := by
  classical
  let g := F.metric t
  let D := F.connection t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) x
  let e := g.orthonormalBasis x
  let H := D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
  let V (a b c d : E) :=
    -2 * D.ricci x (D.curvature x a b d) c - H ![a, b, d, c] - H ![a, d, b, c] +
      H ![a, c, b, d] + H ![b, a, d, c] + H ![b, d, a, c] - H ![b, c, a, d]
  let r (a b : E) := (∑ j, V a (e j) b (e j)) +
    2 * (∑ j, ∑ k, D.ricci x (e j) (e k) * D.curvatureTensor x a (e j) b (e k))
  have hr (a b : E) : HasDerivAt (fun s ↦ (F.connection s).ricci x a b) (r a b) t := by
    apply hasDerivAt_ricci_of_curvature_derivative F x a b (fun c d ↦ V a c b d) ht
    intro c d
    exact hasDerivAt_curvatureTensor_first_variation F ht x a c b d
  have hscalar := hasDerivAt_scalarCurvature_of_ricci_derivative F x r ht hr
  have hRicExpand (a b : E) :
      D.ricci x a b = ∑ k, g.inner x (e k) a * D.ricci x (e k) b := by
    obtain ⟨R, hR⟩ := (isSmoothCovariantTensor_ricciEvaluation D).1 x
    have hu (z : E) : Function.update ![0, b] 0 z = ![z, b] := by
      funext i
      fin_cases i <;> simp [Function.update]
    let L := R.toLinearMap ![0, b] 0
    have hL (z : E) : L z = D.ricci x z b := by
      change R (Function.update ![0, b] 0 z) = D.ricci x z b
      rw [hu]
      exact (hR ![z, b]).symm
    calc
      D.ricci x a b = L a := (hL a).symm
      _ = L (∑ i, inner ℝ (e i) a • e i) := congrArg L (e.sum_repr' a).symm
      _ = ∑ i, inner ℝ (e i) a * D.ricci x (e i) b := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        calc
          L (inner ℝ (e i) a • e i) = inner ℝ (e i) a • L (e i) :=
            L.map_smul (inner ℝ (e i) a) (e i)
          _ = _ := by rw [hL]; rfl
      _ = _ := rfl
  have hmetric :
      (∑ i, ∑ j, D.ricci x (D.curvature x (e i) (e j) (e j)) (e i)) =
        D.ricciNormSq x := by
    have he (i j) : D.ricci x (D.curvature x (e i) (e j) (e j)) (e i) =
        ∑ k, D.curvatureTensor x (e i) (e j) (e k) (e j) * D.ricci x (e k) (e i) := by
      rw [hRicExpand]
      apply Finset.sum_congr rfl
      intro k _
      rw [g.symm]
      rfl
    simp_rw [he]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul]
    change D.ricci x (e i) (e k) * D.ricci x (e k) (e i) =
      D.ricci x (e i) (e k) ^ 2
    rw [ricci_symm D x (e k) (e i)]
    ring
  have hcurvTrace (a b : E) :
      (∑ i, D.curvatureTensor x (e i) a (e i) b) = D.ricci x a b := by
    change (∑ i, D.curvatureTensor x (e i) a (e i) b) =
      ∑ i, D.curvatureTensor x a (e i) b (e i)
    apply Finset.sum_congr rfl
    intro i _
    rw [curvatureTensor_swap_first D x a (e i) (e i) b,
      curvatureTensor_swap_last D x a (e i) (e i) b]
    ring
  have hcorrection :
      (∑ i, ∑ j, ∑ k, D.ricci x (e j) (e k) * D.curvatureTensor x (e i) (e j) (e i) (e k)) =
        D.ricciNormSq x := by
    calc
      _ = ∑ j, ∑ k, D.ricci x (e j) (e k) *
          (∑ i, D.curvatureTensor x (e i) (e j) (e i) (e k)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = _ := by
        simp only [hcurvTrace, LeviCivitaData.ricciNormSq, e, g, D, pow_two]
  have htraceH : (∑ i, ∑ j, H ![e i, e i, e j, e j]) = D.laplacian D.scalarCurvature x := by
    apply Finset.sum_congr rfl
    intro i _
    exact ricci_secondCovariantDerivative_metric_trace D x (e i) (e i)
  have htraceH' : (∑ i, ∑ j, H ![e j, e j, e i, e i]) = D.laplacian D.scalarCurvature x := by
    rw [Finset.sum_comm]
    exact htraceH
  have hdivH : (∑ i, ∑ j, H ![e i, e j, e j, e i]) =
      (1 / 2 : ℝ) * D.laplacian D.scalarCurvature x := by
    rw [LeviCivitaData.laplacian, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ricci_secondCovariantDerivative_contracted D x (e i) (e i)
  have hV (i j) : V (e i) (e j) (e i) (e j) =
      -2 * D.ricci x (D.curvature x (e i) (e j) (e j)) (e i) -
        2 * H ![e i, e j, e j, e i] + H ![e i, e i, e j, e j] +
          H ![e j, e j, e i, e i] := by
    have hsym : H ![e j, e i, e j, e i] = H ![e j, e i, e i, e j] :=
      ricci_secondCovariantDerivative_symm D x (e j) (e i) (e j) (e i)
    dsimp only [V]
    rw [hsym]
    ring
  have hsumV : (∑ i, ∑ j, V (e i) (e j) (e i) (e j)) =
      -2 * D.ricciNormSq x + D.laplacian D.scalarCurvature x := by
    simp only [hV, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hmetric, hdivH, htraceH, htraceH']
    ring
  have htraceR : (∑ i, r (e i) (e i)) = D.laplacian D.scalarCurvature x := by
    simp only [r, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsumV, hcorrection]
    ring
  apply hscalar.congr_deriv
  change (∑ i, r (e i) (e i)) + 2 * D.ricciNormSq x = _
  rw [htraceR]

end PoincareConjecture.M04

