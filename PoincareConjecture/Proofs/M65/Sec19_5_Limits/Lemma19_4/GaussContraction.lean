import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussEquation
import PoincareConjecture.Proofs.M13.CurvatureContractions
import PoincareConjecture.Proofs.M04.CurvatureSymmetries









noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Manifold Bundle Topology InnerProductSpace BigOperators

namespace PoincareConjecture.M65Gauss



theorem exists_orthonormalBasis_adjoin
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



theorem gauss_scalarCurvature {m : ℕ}
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
    let B := secondFundamentalForm D D' F x
    D'.scalarCurvature x = D.scalarCurvature (F x) - 2 * D.ricci (F x) N N +
      g.inner (F x) (∑ i, B (b i) (b i)) (∑ i, B (b i) (b i)) -
        ∑ i, ∑ j, g.inner (F x) (B (b i) (b j)) (B (b i) (b j)) := by
  classical
  dsimp only
  let b := h.orthonormalBasis x
  let L := (fderiv ℝ F x).toLinearMap
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 m) : EuclideanSpace ℝ (Fin m) → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨e, he0, hei⟩ := exists_orthonormalBasis_adjoin b
    (show TangentSpace (𝓡 m) x →ₗ[ℝ] TangentSpace (𝓡 (m + 1)) (F x) from L)
    (fun u v => (hmetric.self_of_nhds u v).symm) N hN hNT (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) =
        Fintype.card (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))) + 1
      simp)
  change ∀ i, e (some i) = L (b i) at hei
  have hzero : D.curvatureTensor (F x) N N N N = 0 := by
    have hz := M04.curvatureTensor_swap_first D (F x) N N N N
    linarith
  have hswap (u v : EuclideanSpace ℝ (Fin (m + 1))) :
      D.curvatureTensor (F x) u v u v = D.curvatureTensor (F x) v u v u := by
    have ha := M04.curvatureTensor_swap_first D (F x) u v u v
    have hb := M04.curvatureTensor_swap_last D (F x) v u u v
    linarith
  have hr : D.ricci (F x) N N =
      ∑ i, D.curvatureTensor (F x) N (L (b i)) N (L (b i)) := by
    simpa only [Fintype.sum_option, he0, hei, hzero, zero_add] using
      M13.ricci_eq_sum_basis D (F x) e N N
  have ha :
      (∑ i, ∑ j, D.curvatureTensor (F x) (L (b i)) (L (b j)) (L (b i)) (L (b j))) =
        D.scalarCurvature (F x) - 2 * D.ricci (F x) N N := by
    have hs := M13.scalarCurvature_eq_sum_basis D (F x) e
    simp_rw [M13.ricci_eq_sum_basis D (F x) e] at hs
    simp only [Fintype.sum_option, he0, hei, hzero, zero_add,
      Finset.sum_add_distrib] at hs
    simp_rw [← hswap N] at hs
    rw [← hr] at hs
    linarith
  have hg (i j) : D'.curvatureTensor x (b i) (b j) (b i) (b j) =
      D.curvatureTensor (F x) (L (b i)) (L (b j)) (L (b i)) (L (b j)) +
        g.inner (F x) (secondFundamentalForm D D' F x (b i) (b i))
          (secondFundamentalForm D D' F x (b j) (b j)) -
        g.inner (F x) (secondFundamentalForm D D' F x (b i) (b j))
          (secondFundamentalForm D D' F x (b i) (b j)) := by
    rw [gauss_curvatureTensor D D' hF hmetric,
      secondFundamentalForm_symm D D' hF.self_of_nhds (b j) (b i)]
    rfl
  change (∑ i, ∑ j, D'.curvatureTensor x (b i) (b j) (b i) (b j)) = _
  simp_rw [hg, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [ha]
  simp only [map_sum, sum_apply, b]
  congr 2
  exact Finset.sum_comm

end PoincareConjecture.M65Gauss
