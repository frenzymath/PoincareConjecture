import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Trace

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture Filter
open scoped ContDiff Topology Manifold Bundle InnerProductSpace BigOperators

namespace Poincare.Geometry.Curvature.Hypersurface

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

private theorem exists_orthonormalBasis_adjoin
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] W) (hL : ∀ u v, ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ)
    (N : W) (hN : ⟪N, N⟫_ℝ = 1) (hNT : ∀ u, ⟪N, L u⟫_ℝ = 0)
    (hdim : Module.finrank ℝ W = Fintype.card ι + 1) :
    ∃ B : OrthonormalBasis (Option ι) ℝ W,
      B none = N ∧ ∀ i, B (some i) = L (b i) := by
  classical
  let v : Option ι → W := fun i => i.elim N (fun j => L (b j))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hN
      | some j => exact hNT (b j)
    | some i =>
      cases j with
      | none => exact (real_inner_comm _ _).trans (hNT (b i))
      | some j => simpa only [v, Option.elim_some, hL, Option.some.injEq]
          using b.inner_eq_ite i j
  have hcard : Fintype.card (Option ι) = Module.finrank ℝ W := by
    simpa using hdim.symm
  let a := basisOfOrthonormalOfCardEqFinrank hv hcard
  have ha : Orthonormal ℝ a := by simpa [a] using hv
  refine ⟨a.toOrthonormalBasis ha, ?_, ?_⟩ <;> simp [a, v]

theorem gauss_scalarCurvature_of_eventually {m : ℕ}
    {g : RiemannianMetric (m + 1) (EuclideanSpace ℝ (Fin (m + 1)))}
    {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (m + 1))}
    {x : EuclideanSpace ℝ (Fin m)}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (N : EuclideanSpace ℝ (Fin (m + 1))) (hN : g.inner (F x) N N = 1)
    (hNT : ∀ a, g.inner (F x) N (fderiv ℝ F x a) = 0) :
    let b := h.orthonormalBasis x
    let A := shapeOperator D D' F x N
    D'.scalarCurvature x = D.scalarCurvature (F x) - 2 * D.ricci (F x) N N +
      (∑ i, h.inner x (A (b i)) (b i)) ^ 2 -
        ∑ i, ∑ j, (h.inner x (A (b i)) (b j)) ^ 2 := by
  classical
  dsimp only
  let b := h.orthonormalBasis x
  let A := shapeOperator D D' F x N
  let L : E m →ₗ[ℝ] E (m + 1) := (fderiv ℝ F x).toLinearMap
  have hL := fderiv_injective_of_pullback_metric hmetric.self_of_nhds
  have hpair (a b c d : E m) :
      g.inner (F x) (secondFundamentalForm D D' F x a b)
        (secondFundamentalForm D D' F x c d) =
      h.inner x (A a) b * h.inner x (A c) d := by
    rw [metric_inner_normals_eq_mul g (F x) L hL N hN hNT
      _ _ (secondFundamentalForm_normal D D' hF.self_of_nhds hmetric c d)]
    rw [g.symm (F x) (secondFundamentalForm D D' F x a b),
      g.symm (F x) (secondFundamentalForm D D' F x c d),
      inner_shapeOperator, inner_shapeOperator]
  have hgauss (i j) :
      D'.curvatureTensor x (b i) (b j) (b i) (b j) =
      D.curvatureTensor (F x) (L (b i)) (L (b j)) (L (b i)) (L (b j)) +
        h.inner x (A (b i)) (b i) * h.inner x (A (b j)) (b j) -
          (h.inner x (A (b i)) (b j)) ^ 2 := by
    rw [gauss_curvatureTensor_of_eventually D D' hF hmetric,
      secondFundamentalForm_symm D D' hF.self_of_nhds (b j) (b i), hpair, hpair]
    simp only [pow_two]
    rfl
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : E m → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : E (m + 1) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨B, hB0, hBi⟩ := exists_orthonormalBasis_adjoin b
    (show TangentSpace (𝓡 m) x →ₗ[ℝ] TangentSpace (𝓡 (m + 1)) (F x)
      from L)
    (fun u v => (hmetric.self_of_nhds u v).symm) N hN hNT (by
      change Module.finrank ℝ (E (m + 1)) =
        Fintype.card (Fin (Module.finrank ℝ (E m))) + 1
      simp [E])
  change ∀ i, B (some i) = L (b i) at hBi
  have hzero : D.curvatureTensor (F x) N N N N = 0 := by
    have hz := D.curvatureTensor_swap_first (F x) N N N N
    linarith
  have hricci : D.ricci (F x) N N =
      ∑ i, D.curvatureTensor (F x) N (L (b i)) N (L (b i)) := by
    have ht := bilinear_sum_orthonormalBasis_eq
      (D.curvatureTensor_bilinear_first_third (F x) N N) (g.orthonormalBasis (F x)) B
    simp only [LeviCivitaData.curvatureTensor_bilinear_first_third_apply] at ht
    simp_rw [← D.curvatureTensor_diagonal_pair_swap (F x) N] at ht
    simpa only [LeviCivitaData.ricci, Fintype.sum_option, hB0, hBi, hzero, zero_add]
      using ht
  have hambient :
      (∑ i, ∑ j, D.curvatureTensor (F x) (L (b i)) (L (b j)) (L (b i)) (L (b j))) =
        D.scalarCurvature (F x) - 2 * D.ricci (F x) N N := by
    have hs := D.scalarCurvature_eq_sum_orthonormalBasis (F x) B
    simp only [Fintype.sum_option, hB0, hBi, hzero, zero_add,
      Finset.sum_add_distrib] at hs
    simp_rw [← D.curvatureTensor_diagonal_pair_swap (F x) N] at hs
    rw [← hricci] at hs
    linarith
  change (∑ i, ∑ j, D'.curvatureTensor x (b i) (b j) (b i) (b j)) = _
  simp_rw [hgauss, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hambient]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two, b, A]

end Poincare.Geometry.Curvature.Hypersurface
