import PoincareConjecture.Proofs.M35.Thm12_28.CurvatureMetricJets
import PoincareConjecture.Proofs.M35.Thm12_28.InverseGramMetricJets









set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter
open scoped Manifold ContDiff Bundle BigOperators Topology Matrix.Norms.Elementwise

namespace PoincareConjecture.M35

local notation:max "E" n:max => EuclideanSpace ℝ (Fin n)

private theorem ricci_formula {n : ℕ} {g : RiemannianMetric n (E n)}
    (D : LeviCivitaData g) (x u v : E n) (b : Module.Basis (Fin n) ℝ (E n)) :
    D.ricci x u v = ∑ i, ∑ j,
      (Matrix.of (fun a c => g.inner x (b a) (b c)))⁻¹ i j *
        D.curvatureTensor x u (b i) v (b j) :=
  D.ricci_eq_inverse_gram x b (D.exists_multilinear_curvatureTensor x).choose
    (D.exists_multilinear_curvatureTensor x).choose_spec u v


theorem ricci_contDiffAt_euclidean {n : ℕ} {g : RiemannianMetric n (E n)}
    (D : LeviCivitaData g) (x u v : E n) :
    ContDiffAt ℝ ∞ (fun y => D.ricci y u v) x := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  simp_rw [ricci_formula D _ u v b]
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (inverseGram_contDiffAt g x b i j).mul
      (curvatureTensor_contDiffAt_euclidean D x u (b i) v (b j))



theorem ricci_jets_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p u v : E n) (r : ℕ)
    (hjet : ∀ m ≤ r + 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (Dseq k).ricci y u v) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun y => D.ricci y u v) p)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let term (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g')
      (i j : Fin n) (y : E n) :=
    (Matrix.of (fun a c => g'.inner y (b a) (b c)))⁻¹ i j *
      D'.curvatureTensor y u (b i) v (b j)
  have hs (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g')
      (x : E n) (i j : Fin n) : ContDiffAt ℝ ∞ (term g' D' i j) x :=
    (inverseGram_contDiffAt g' x b i j).mul
      (curvatureTensor_contDiffAt_euclidean D' x u (b i) v (b j))
  have heq (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g') (x : E n) :
      iteratedFDeriv ℝ r (fun y => D'.ricci y u v) x =
        ∑ i, ∑ j, iteratedFDeriv ℝ r (term g' D' i j) x := by
    have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    simp_rw [ricci_formula D' _ u v b]
    change iteratedFDeriv ℝ r (fun y => ∑ i, ∑ j, term g' D' i j y) x = _
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (ContDiffAt.sum fun j _ => hs g' D' x i j).of_le hr)]
    apply Finset.sum_congr rfl
    intro i _
    exact iteratedFDeriv_fun_sum_apply (fun j _ => (hs g' D' x i j).of_le hr)
  simp_rw [heq]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact tendsto_iteratedFDeriv_mul_of_jets r (inverseGram_contDiffAt g p b i j)
    (curvatureTensor_contDiffAt_euclidean D p u (b i) v (b j))
    (Eventually.of_forall fun k => inverseGram_contDiffAt (gseq k) (pseq k) b i j)
    (Eventually.of_forall fun k =>
      curvatureTensor_contDiffAt_euclidean (Dseq k) (pseq k) u (b i) v (b j))
    (fun m hm => inverseGram_jets_tendsto_of_metric_jets pseq p b i j m
      (fun l hl => hjet l (by omega)))
    (fun m hm => curvatureTensor_jets_tendsto_of_metric_jets Dseq D pseq p u (b i) v (b j)
      m (fun l hl => hjet l (by omega)))


theorem scalarCurvature_contDiffAt_euclidean {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) :
    ContDiffAt ℝ ∞ D.scalarCurvature x := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  change ContDiffAt ℝ ∞ (fun y => D.scalarCurvature y) x
  simp_rw [scalarCurvature_eq_inverse_gram D _ b]
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (inverseGram_contDiffAt g x b i j).mul (ricci_contDiffAt_euclidean D x (b i) (b j))



theorem scalarCurvature_jets_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p : E n) (r : ℕ)
    (hjet : ∀ m ≤ r + 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (Dseq k).scalarCurvature (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ r D.scalarCurvature p)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let term (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g')
      (i j : Fin n) (y : E n) :=
    (Matrix.of (fun a c => g'.inner y (b a) (b c)))⁻¹ i j * D'.ricci y (b i) (b j)
  have hs (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g')
      (x : E n) (i j : Fin n) : ContDiffAt ℝ ∞ (term g' D' i j) x :=
    (inverseGram_contDiffAt g' x b i j).mul (ricci_contDiffAt_euclidean D' x (b i) (b j))
  have heq (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g') (x : E n) :
      iteratedFDeriv ℝ r D'.scalarCurvature x =
        ∑ i, ∑ j, iteratedFDeriv ℝ r (term g' D' i j) x := by
    have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    change iteratedFDeriv ℝ r (fun y => D'.scalarCurvature y) x = _
    simp_rw [scalarCurvature_eq_inverse_gram D' _ b]
    change iteratedFDeriv ℝ r (fun y => ∑ i, ∑ j, term g' D' i j y) x = _
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (ContDiffAt.sum fun j _ => hs g' D' x i j).of_le hr)]
    apply Finset.sum_congr rfl
    intro i _
    exact iteratedFDeriv_fun_sum_apply (fun j _ => (hs g' D' x i j).of_le hr)
  simp_rw [heq]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact tendsto_iteratedFDeriv_mul_of_jets r (inverseGram_contDiffAt g p b i j)
    (ricci_contDiffAt_euclidean D p (b i) (b j))
    (Eventually.of_forall fun k => inverseGram_contDiffAt (gseq k) (pseq k) b i j)
    (Eventually.of_forall fun k => ricci_contDiffAt_euclidean (Dseq k) (pseq k) (b i) (b j))
    (fun m hm => inverseGram_jets_tendsto_of_metric_jets pseq p b i j m
      (fun l hl => hjet l (by omega)))
    (fun m hm => ricci_jets_tendsto_of_metric_jets Dseq D pseq p (b i) (b j) m
      (fun l hl => hjet l (by omega)))

end PoincareConjecture.M35
