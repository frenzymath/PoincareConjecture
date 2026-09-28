import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence
import PoincareConjecture.Proofs.M13.CurvatureContractions











set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData



theorem scalarCurvature_eq_inverse_gram
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact bilinear_sum_basis_eq_inverse_gram (M13.ricciLinear D x) b (g.orthonormalBasis x)



theorem tendsto_scalarCurvature_of_finite_scalar_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (Dseq i).scalarCurvature x) l (𝓝 (D.scalarCurvature x)) := by
  classical
  let := Fintype.ofFinite ι
  have hzero := (RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b h).1
  let Gseq : α → Matrix ι ι ℝ := fun a i j => (gseq a).inner x (b i) (b j)
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
  have hinv : Tendsto (fun a => (Gseq a)⁻¹) l (𝓝 G⁻¹) := by
    apply (continuousAt_matrix_inv G ?_).tendsto.comp hmatrix
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hdet
  simp_rw [scalarCurvature_eq_inverse_gram _ x b]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i)) j).mul
    (tendsto_ricci_of_scalar_metric_jets Dseq D x (b i) (b j) b h)

end PoincareConjecture.LeviCivitaData
