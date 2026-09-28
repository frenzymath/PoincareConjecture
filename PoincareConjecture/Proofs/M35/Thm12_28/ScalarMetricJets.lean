import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence
import PoincareConjecture.Proofs.M13.CurvatureContractions

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35

theorem scalarCurvature_eq_inverse_gram
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact bilinear_sum_basis_eq_inverse_gram (M13.ricciLinear D x) b (g.orthonormalBasis x)

theorem scalarCurvature_tendsto_of_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hjet : ∀ r : ℕ, r ≤ 2 → ∀ a c : Fin n,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (Dseq i).scalarCurvature x) l (𝓝 (D.scalarCurvature x)) := by
  obtain ⟨hzero, _, _⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b hjet
  let Gseq : α → Matrix (Fin n) (Fin n) ℝ := fun a i j => (gseq a).inner x (b i) (b j)
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j => g.inner x (b i) (b j)
  have hmatrix : Tendsto Gseq l (𝓝 G) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have heval : Continuous (fun B : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => B (b i) (b j)) := by fun_prop
    exact heval.continuousAt.tendsto.comp hzero
  have hdet : G.det ≠ 0 := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change (Matrix.gram ℝ (show Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)
      from b)).det ≠ 0
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
    (LeviCivitaData.tendsto_ricci_of_scalar_metric_jets Dseq D x (b i) (b j) b hjet)

theorem scalarCurvature_eq_pullback_euclidean
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {h : RiemannianMetric n M} (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v)) :
    D.scalarCurvature x = D'.scalarCurvature (f x) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  obtain ⟨e, he⟩ := hinv.self_of_nhds
  let e' : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) (f x) :=
    e.toLinearEquiv.isometryOfInner (fun u v => by
      change h.inner (f x) (e u) (e v) = g.inner x u v
      exact (congrArg₂ (fun a b => h.inner (f x) a b)
        (congrArg (fun A => A u) he) (congrArg (fun A => A v) he)).trans
          (hmetric.self_of_nhds u v).symm)
  rw [M13.scalarCurvature_eq_sum_basis D' (f x) ((g.orthonormalBasis x).map e')]
  change (∑ i, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact (D.ricci_eq_pullback_euclidean D' hf hinv hmetric _ _).trans
    (congrArg₂ (D'.ricci (f x))
      (congrArg (fun A => A (g.orthonormalBasis x i)) he).symm
      (congrArg (fun A => A (g.orthonormalBasis x i)) he).symm)

end PoincareConjecture.M35
