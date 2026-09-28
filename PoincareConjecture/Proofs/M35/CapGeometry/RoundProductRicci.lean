import PoincareConjecture.Proofs.M35.CapGeometry.RoundProductCurvature
import PoincareConjecture.Proofs.M35.CapGeometry.RoundSurfaceRicci
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence
import Mathlib.LinearAlgebra.Basis.Prod









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem product_ricci
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    (hmetric : ∀ x u v : V,
      g.inner x u v = h.inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    (x u v : V) :
    D.ricci x u v = Dh.ricci (cylinderCoordinateEquiv x).1
      (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 := by
  classical
  let a := (cylinderCoordinateEquiv x).1
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : E2 → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) a) = 2 := finrank_euclideanSpace_fin
  let b2 := (h.orthonormalBasis a).reindex (finCongr hdim)
  let b : Module.Basis (Fin 2 ⊕ Unit) ℝ (TangentSpace (𝓡 3) x) :=
    (b2.toBasis.prod (Module.Basis.singleton Unit ℝ)).map
      cylinderCoordinateEquiv.symm.toLinearEquiv
  have hbL (i : Fin 2) : cylinderCoordinateEquiv (b (Sum.inl i)) = (b2 i, 0) := by
    dsimp only [b]
    rw [Module.Basis.map_apply, Module.Basis.prod_apply]
    simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply,
      OrthonormalBasis.coe_toBasis]
    exact cylinderCoordinateEquiv.apply_symm_apply _
  have hbR (i : Unit) : cylinderCoordinateEquiv (b (Sum.inr i)) = (0, 1) := by
    dsimp only [b]
    rw [Module.Basis.map_apply, Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
      Module.Basis.singleton_apply]
    exact cylinderCoordinateEquiv.apply_symm_apply _
  have hgram : Matrix.of (fun i j => g.inner x (b i) (b j)) = 1 := by
    ext i j
    rw [Matrix.of_apply, hmetric]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [hbL, zero_mul, add_zero]
        change h.inner a (b2 i) (b2 j) = _
        have hi : h.inner a (b2 i) (b2 j) = if i = j then 1 else 0 :=
          b2.inner_eq_ite i j
        simpa only [Matrix.one_apply, Sum.inl.injEq] using hi
      | inr j => simp [hbL, hbR]
    | inr i =>
      cases j with
      | inl j => simp [hbL, hbR]
      | inr j => simp [hbR]
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor x
  rw [D.ricci_eq_inverse_gram x b A hA u v, hgram, inv_one]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_sum_type]
  simp only [product_curvatureTensor D Dh hmetric, hbL, hbR, Fintype.sum_unique]
  have hz : Dh.curvatureTensor a (cylinderCoordinateEquiv u).1 0
      (cylinderCoordinateEquiv v).1 0 = 0 := by
    rw [← M13.curvatureTensorLinear_apply]
    simp only [map_zero, LinearMap.zero_apply]
  change (∑ i : Fin 2, Dh.curvatureTensor a (cylinderCoordinateEquiv u).1
    (b2 i) (cylinderCoordinateEquiv v).1 (b2 i)) +
      Dh.curvatureTensor a (cylinderCoordinateEquiv u).1 0
        (cylinderCoordinateEquiv v).1 0 = _
  rw [hz, add_zero]
  exact (M13.ricci_eq_sum_basis Dh a b2 _ _).symm



theorem round_product_ricci
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    (hmetric : ∀ x u v : V,
      g.inner x u v = h.inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    (c : ℝ)
    (hround : ∀ x u v, h.inner x u u = 1 → h.inner x v v = 1 →
      h.inner x u v = 0 → Dh.sectionalCurvature x u v = c)
    (x u v : V) :
    D.ricci x u v = c * h.inner (cylinderCoordinateEquiv x).1
      (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 := by
  rw [product_ricci D Dh hmetric]
  exact surface_ricci_of_sectional Dh _ c (hround _) _ _

end PoincareConjecture.M35
