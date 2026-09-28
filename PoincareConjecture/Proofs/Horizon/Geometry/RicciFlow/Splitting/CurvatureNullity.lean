import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem ricci_eq_zero_of_nonneg_of_self_eq_zero
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    {v : TangentSpace (𝓡 n) x} (hv : D.ricci x v v = 0)
    (w : TangentSpace (𝓡 n) x) : D.ricci x v w = 0 := by
  let B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x) :=
    ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have hB (u z : TangentSpace (𝓡 n) x) : B u z = D.ricci x u z := by
    simp [B, LeviCivitaData.ricci, LinearMap.sum_apply]
  have hsym : LinearMap.IsSymm B := by
    constructor
    intro u z
    change B u z = B z u
    rw [hB, hB]
    exact (hD.2.2.2.1 x u z u z).2.2.2
  have hk := (B.apply_apply_same_eq_zero_iff (by simpa only [hB] using hRic) hsym).mp
    (by simpa only [hB] using hv)
  have heq := LinearMap.congr_fun (LinearMap.mem_ker.mp hk) w
  simpa only [hB, LinearMap.zero_apply] using heq

theorem curvatureTensor_radial_eq_zero_of_ricci_self_eq_zero
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x u w u w)
    {v : TangentSpace (𝓡 n) x} (hv : D.ricci x v v = 0)
    (u w : TangentSpace (𝓡 n) x) : D.curvatureTensor x u v w v = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x) :=
    D.curvatureTensor_bilinear_first_third x v v
  let b := g.orthonormalBasis x
  have hB (z q : TangentSpace (𝓡 n) x) : B z q = D.curvatureTensor x z v q v := rfl
  have hsym : LinearMap.IsSymm B := ⟨fun z q => (hD.2.2.2.1 x z v q v).2.1⟩
  have hnonneg : ∀ z, 0 ≤ B z z := fun z => hsec z v
  have htrace : (∑ i, B (b i) (b i)) = 0 := by
    have heq (i) : B (b i) (b i) = D.curvatureTensor x v (b i) v (b i) := by
      rw [hB, D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]
    simp_rw [heq]
    exact hv
  have hzero (i) : B (b i) = 0 := by
    apply LinearMap.mem_ker.mp
    apply (B.apply_apply_same_eq_zero_iff hnonneg hsym).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg (b j))).mp htrace i
      (Finset.mem_univ i)
  rw [← hB, ← b.sum_repr' u]
  simp only [map_sum, map_smul, hzero, smul_zero, Finset.sum_const_zero,
    LinearMap.zero_apply]

theorem curvatureTensor_eq_zero_of_ricci_self_eq_zero
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x u w u w)
    {v : TangentSpace (𝓡 n) x} (hv : D.ricci x v v = 0)
    (u w z : TangentSpace (𝓡 n) x) : D.curvatureTensor x v u w z = 0 := by
  have hdiag (y : TangentSpace (𝓡 n) x) : D.curvatureTensor x v y v y = 0 := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]
    exact curvatureTensor_radial_eq_zero_of_ricci_self_eq_zero D hD x hsec hv y y
  have hrad (y q : TangentSpace (𝓡 n) x) : D.curvatureTensor x v y q y = 0 := by
    let B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x) :=
      D.curvatureTensor_bilinear_first_third x y y
    have hsym : LinearMap.IsSymm B := ⟨fun c d => (hD.2.2.2.1 x c y d y).2.1⟩
    have hk := (B.apply_apply_same_eq_zero_iff (fun c => hsec c y) hsym).mp (hdiag y)
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hk) q
  have hcross (y q r : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x v y q r + D.curvatureTensor x v r q y = 0 := by
    have h := hrad (y + r) q
    simp only [D.curvatureTensor_add_second, D.curvatureTensor_add_last] at h
    rw [hrad y q, hrad r q] at h
    linarith
  have hbianchi := (hD.2.2.2.1 x v u w z).2.2.1
  have h1 := hcross u w z
  have h2 := hcross w u z
  have h3 := (hD.2.2.2.1 x u w v z).2.1
  have h4 := D.curvatureTensor_swap_first x w v u z
  have h5 := D.curvatureTensor_swap_last x v z w u
  linarith

theorem ricciReaction_eq_zero_of_ricci_self_eq_zero
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ u w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x u w u w)
    {v : TangentSpace (𝓡 n) x} (hv : D.ricci x v v = 0)
    (w : TangentSpace (𝓡 n) x) : D.ricciReaction x v w = 0 := by
  have hRic : ∀ u : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x u u :=
    fun u => Finset.sum_nonneg fun i _ => hsec u (g.orthonormalBasis x i)
  unfold LeviCivitaData.ricciReaction
  simp only [curvatureTensor_eq_zero_of_ricci_self_eq_zero D hD x hsec hv,
    ricci_eq_zero_of_nonneg_of_self_eq_zero D hD x hRic hv,
    zero_mul, Finset.sum_const_zero, mul_zero, sub_self]

end PoincareConjecture.RicciFlow.Splitting
