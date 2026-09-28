import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.CurvatureJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Limit.RicciConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

private theorem scalarCurvature_eq_inverse_gram
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have h := bilinear_sum_basis_eq_inverse_gram (E := TangentSpace (𝓡 n) x)
    B b (g.orthonormalBasis x)
  change (∑ i, B (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * B (b i) (b j) at h
  simpa only [B, LinearMap.sum_apply, curvatureTensor_bilinear_first_third_apply,
    ricci, scalarCurvature] using h

theorem tendsto_scalarCurvature_of_moving_scalar_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (xseq : α → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) (xseq i)) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (Dseq i).scalarCurvature (xseq i)) l (𝓝 (D.scalarCurvature x)) := by
  classical
  obtain ⟨hzero, hone, htwo⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets_at_points xseq x b hjets
  let Gseq : α → Matrix ι ι ℝ := fun k i j => (gseq k).inner (xseq k) (b i) (b j)
  let G : Matrix ι ι ℝ := fun i j => g.inner x (b i) (b j)
  have hmatrix : Tendsto Gseq l (𝓝 G) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact ((ContinuousLinearMap.apply ℝ ℝ (b j)).continuous.continuousAt.tendsto.comp
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (b i)).continuous.continuousAt.tendsto.comp hzero))
  have hdet : G.det ≠ 0 := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change (Matrix.gram ℝ (show Module.Basis ι ℝ (TangentSpace (𝓡 n) x) from b)).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  have hinv : Tendsto (fun k => (Gseq k)⁻¹) l (𝓝 G⁻¹) := by
    apply (continuousAt_matrix_inv G ?_).tendsto.comp hmatrix
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hdet
  have hricci (u v : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun i => (Dseq i).ricci (xseq i) u v) l (𝓝 (D.ricci x u v)) := by
    have heq (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D' : LeviCivitaData g') (y : EuclideanSpace ℝ (Fin n)) :=
      D'.ricci_eq_inverse_gram y b (D'.exists_multilinear_curvatureTensor y).choose
        (D'.exists_multilinear_curvatureTensor y).choose_spec u v
    simp_rw [heq]
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i)) j).mul
      (tendsto_curvatureTensor_of_metric_jets_at_points Dseq D xseq x u (b i) v (b j)
        hzero hone htwo)
  simp_rw [scalarCurvature_eq_inverse_gram _ _ b]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i)) j).mul (hricci (b i) (b j))

end PoincareConjecture.LeviCivitaData
