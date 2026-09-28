import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M03.CurvatureTrilinear

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle BigOperators

universe u v

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ricci_eq_sum_basis_of_curvature_pairing {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x)
    {ι : Type v} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.ricci x u v = ∑ k, b.repr (D.curvature x (b k) u v) k := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨R, hR⟩ := exists_curvature_trilinearMap D x
  let A : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x := {
    toFun := fun w => R w u v
    map_add' := fun w z => by simp only [map_add, LinearMap.add_apply]
    map_smul' := fun c w => by
      simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hA (w : TangentSpace (𝓡 n) x) : A w = D.curvature x w u v := hR w u v
  let c := g.orthonormalBasis x
  have hdiag : (∑ j, c.toBasis.repr (A (c j)) j) =
      ∑ i, b.repr (A (b i)) i := by
    calc
      _ = ∑ j, ∑ i, b.repr (c j) i * c.toBasis.repr (A (b i)) j := by
        apply Finset.sum_congr rfl
        intro j _
        conv_lhs => rw [← b.sum_repr (c j)]
        simp only [map_sum, map_smul, Finset.sum_apply',
          Finsupp.smul_apply, smul_eq_mul]
      _ = ∑ i, ∑ j, b.repr (c j) i * c.toBasis.repr (A (b i)) j :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact b.sum_repr_mul_repr c.toBasis (A (b i)) i
  calc
    D.ricci x u v = ∑ j, c.toBasis.repr (A (c j)) j := by
      change (∑ j, g.inner x (D.curvature x u (c j) (c j)) v) = _
      apply Finset.sum_congr rfl
      intro j _
      have hswap : D.curvature x u (c j) v = -D.curvature x (c j) u v := by
        delta LeviCivitaData.curvature
        exact curvatureOnFields_swap D _ _ _ x
      rw [curvature_pair_skew, hswap, map_neg, neg_neg,
        c.coe_toBasis_repr_apply, c.repr_apply_apply, hA]
      rfl
    _ = ∑ i, b.repr (A (b i)) i := hdiag
    _ = _ := by simp only [hA]

theorem hasDerivWithinAt_metric_difference_basis
    {J J' : Set ℝ} (F : RicciFlow n M J) (F' : RicciFlow n M J')
    {t : ℝ} (ht : t ∈ J ∩ J') (x : M)
    {ι : Type v} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt
      (fun s => (F.metric s).inner x u v - (F'.metric s).inner x u v)
      (-2 * ∑ k, b.repr ((F.connection t).curvature x (b k) u v -
        (F'.connection t).curvature x (b k) u v) k) (J ∩ J') t := by
  have hd := ((F.equation t ht.1 x u v).mono Set.inter_subset_left).sub
    ((F'.equation t ht.2 x u v).mono Set.inter_subset_right)
  rw [ricci_eq_sum_basis_of_curvature_pairing (F.connection t) x u v b,
    ricci_eq_sum_basis_of_curvature_pairing (F'.connection t) x u v b] at hd
  apply hd.congr_deriv
  simp only [map_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

theorem metric_difference_basis_energy_rate
    {J J' : Set ℝ} (F : RicciFlow n M J) (F' : RicciFlow n M J')
    {t : ℝ} (ht : t ∈ J ∩ J') (x : M)
    {ι : Type v} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    let h := fun s i j =>
      (F.metric s).inner x (b i) (b j) - (F'.metric s).inner x (b i) (b j)
    let S := fun k i j => b.repr
      ((F.connection t).curvature x (b k) (b i) (b j) -
        (F'.connection t).curvature x (b k) (b i) (b j)) k
    HasDerivWithinAt (fun s => ∑ i, ∑ j, h s i j ^ 2)
      (-4 * ∑ i, ∑ j, h t i j * ∑ k, S k i j) (J ∩ J') t ∧
      -4 * (∑ i, ∑ j, h t i j * ∑ k, S k i j) ≤
        (∑ i, ∑ j, h t i j ^ 2) +
          4 * (Fintype.card ι : ℝ) * ∑ i, ∑ j, ∑ k, S k i j ^ 2 := by
  classical
  dsimp only
  let h := fun s i j =>
    (F.metric s).inner x (b i) (b j) - (F'.metric s).inner x (b i) (b j)
  let S := fun k i j => b.repr
    ((F.connection t).curvature x (b k) (b i) (b j) -
      (F'.connection t).curvature x (b k) (b i) (b j)) k
  have hd (i j : ι) : HasDerivWithinAt (fun s => h s i j ^ 2)
      (-4 * (h t i j * ∑ k, S k i j)) (J ∩ J') t := by
    have he := (hasDerivWithinAt_metric_difference_basis F F' ht x b (b i) (b j)).fun_pow 2
    apply he.congr_deriv
    change (2 : ℝ) * h t i j ^ 1 * (-2 * ∑ k, S k i j) = _
    ring
  constructor
  · have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
      HasDerivWithinAt.fun_sum (u := Finset.univ) fun j _ => hd i j
    simpa only [Finset.mul_sum] using hsum
  · have hpoint (i j : ι) : -4 * (h t i j * ∑ k, S k i j) ≤
        h t i j ^ 2 + 4 * (Fintype.card ι : ℝ) * ∑ k, S k i j ^ 2 := by
      have hcs : (∑ k, S k i j) ^ 2 ≤
          (Fintype.card ι : ℝ) * ∑ k, S k i j ^ 2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _ : ι => (1 : ℝ)) (fun k => S k i j)
      nlinarith [sq_nonneg (h t i j + 2 * ∑ k, S k i j)]
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
    simpa only [Finset.sum_add_distrib, Finset.mul_sum] using hsum

end PoincareConjecture.Proofs.M03
