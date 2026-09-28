import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bilinear
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.M07.Geometry.Manifold.VectorField.Commutator
import PoincareConjecture.Proofs.M07.Geometry.Manifold.PartitionOfUnity.Derivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Operator











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem exists_orthonormal_changeBasis_local
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) (hxy : LinearIndependent ℝ ![x, y]) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧
      (inner ℝ (a • x + b • y) (a • x + b • y) : ℝ) = 1 ∧
      (inner ℝ (c • x + d • y) (c • x + d • y) : ℝ) = 1 ∧
      (inner ℝ (a • x + b • y) (c • x + d • y) : ℝ) = 0 := by
  classical
  have hx0 : x ≠ 0 := by
    intro h
    rw [linearIndependent_fin2] at hxy
    exact hxy.2 0 (by simp [h])
  have hxx : (0 : ℝ) < inner ℝ x x := real_inner_self_pos.2 hx0
  have hxxne : (inner ℝ x x : ℝ) ≠ 0 := ne_of_gt hxx
  set μ : ℝ := (inner ℝ x y : ℝ) / (inner ℝ x x : ℝ) with hμ
  set z : V := y - μ • x with hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [hz] at h
    exact ((LinearIndependent.pair_iff' hx0).mp hxy) μ (sub_eq_zero.mp h).symm
  have hzz : (0 : ℝ) < inner ℝ z z := real_inner_self_pos.2 hz0
  have hxz : (inner ℝ x z : ℝ) = 0 := by
    rw [hz, inner_sub_right, real_inner_smul_right, hμ,
      div_mul_cancel₀ _ hxxne, sub_self]
  set nx : ℝ := Real.sqrt (inner ℝ x x : ℝ)
  set nz : ℝ := Real.sqrt (inner ℝ z z : ℝ)
  have hnxpos : 0 < nx := Real.sqrt_pos.2 hxx
  have hnzpos : 0 < nz := Real.sqrt_pos.2 hzz
  have hnx2 : nx * nx = (inner ℝ x x : ℝ) := Real.mul_self_sqrt hxx.le
  have hnz2 : nz * nz = (inner ℝ z z : ℝ) := Real.mul_self_sqrt hzz.le
  have hxe : (nx⁻¹ • x + (0 : ℝ) • y) = nx⁻¹ • x := by simp
  have hye : (-(nz⁻¹ * μ) • x + nz⁻¹ • y) = nz⁻¹ • z := by
    rw [hz, smul_sub, smul_smul]
    module
  refine ⟨nx⁻¹, 0, -(nz⁻¹ * μ), nz⁻¹, ?_, ?_, ?_, ?_⟩
  · have hd : nx⁻¹ * nz⁻¹ - 0 * (-(nz⁻¹ * μ)) = nx⁻¹ * nz⁻¹ := by ring
    rw [hd]
    positivity
  · rw [hxe, real_inner_smul_left, real_inner_smul_right, ← hnx2]
    field_simp
  · rw [hye, real_inner_smul_left, real_inner_smul_right, ← hnz2]
    field_simp
  · rw [hxe, hye, real_inner_smul_left, real_inner_smul_right, hxz]
    ring

private lemma curvature_inner_self
    (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    g.inner x (D.curvatureOnFields X Y Z x) (Z x) = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let h : M → ℝ := fun q => g.inner q (Z q) (Z q)
  have hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ h x := hZ.inner_bundle hZ
  have hcovX := D.contMDiffAt_covariantDerivativeOnFields hX hZ
  have hcovY := D.contMDiffAt_covariantDerivativeOnFields hY hZ
  have heq (W : (x : M) → TangentSpace (𝓡 n) x)
      (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
      (fun q => g.inner q (D.covariantDerivativeOnFields W Z q) (Z q)) =ᶠ[𝓝 x]
        (fun q => (1 / 2 : ℝ) * mvfderiv (𝓡 n) h q (W q)) := by
    filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hW,
      eventually_mdifferentiableAt_of_contMDiffAt hZ] with q hWq hZq
    have hc := D.mvfderiv_inner_on_fields W hZq hZq
    dsimp [h]
    rw [g.symm q (Z q) (D.covariantDerivativeOnFields W Z q)] at hc
    linarith [hc]
  have hψX : mvfderiv (𝓡 n)
      (fun q => g.inner q (D.covariantDerivativeOnFields X Z q) (Z q)) x (Y x) =
      (1 / 2 : ℝ) * mvfderiv (𝓡 n) (fun q => mvfderiv (𝓡 n) h q (X q)) x (Y x) := by
    rw [Poincare.mvfderiv_eq_of_eventuallyEq (heq X hX)]
    simp only [PoincareConjecture.mvfderiv_const_mul]
  have hψY : mvfderiv (𝓡 n)
      (fun q => g.inner q (D.covariantDerivativeOnFields Y Z q) (Z q)) x (X x) =
      (1 / 2 : ℝ) * mvfderiv (𝓡 n) (fun q => mvfderiv (𝓡 n) h q (Y q)) x (X x) := by
    rw [Poincare.mvfderiv_eq_of_eventuallyEq (heq Y hY)]
    simp only [PoincareConjecture.mvfderiv_const_mul]
  have hI1 := D.mvfderiv_inner_on_fields Y
    (hcovX.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
  have hI2 := D.mvfderiv_inner_on_fields X
    (hcovY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
  have hcomm := Poincare.Manifold.VectorField.mfderiv_mlieBracket_eq_commutator_of_contMDiffAt
    X Y x hh (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
  have hφ := D.mvfderiv_inner_on_fields (VectorField.mlieBracket (𝓡 n) X Y)
    (hZ.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
  rw [hψX] at hI1
  rw [hψY] at hI2
  rw [hcomm] at hφ
  simp only [covariantDerivativeOnFields] at hI1 hI2 hφ
  unfold curvatureOnFields
  change g.inner x
    (D.connection (D.covariantDerivativeOnFields Y Z) x (X x) -
      D.connection (D.covariantDerivativeOnFields X Z) x (Y x) -
      D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x)) (Z x) = 0
  simp only [map_sub, sub_apply]
  rw [g.symm x (Z x) (D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x))] at hφ
  rw [g.symm x (D.connection Z x (X x)) (D.connection Z x (Y x))] at hI1
  linarith

private lemma curvatureOnFields_add_right
    (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    D.curvatureOnFields X Y (Z + W) x =
      D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y W x := by
  have hZW := hZ.add_section hW
  have hYZ := D.contMDiffAt_covariantDerivativeOnFields hY hZ
  have hYW := D.contMDiffAt_covariantDerivativeOnFields hY hW
  have hYZW := D.contMDiffAt_covariantDerivativeOnFields hY hZW
  have heqY : (fun y => D.connection (Z + W) y (Y y)) =ᶠ[𝓝 x]
      (fun y => D.connection Z y (Y y)) + (fun y => D.connection W y (Y y)) := by
    filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hZ,
      eventually_mdifferentiableAt_of_contMDiffAt hW] with y hyZ hyW
    exact congrArg (fun L => L (Y y)) (D.connection.isCovariantDerivativeOn.add hyZ hyW)
  have houterY := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
    (hYZW.mdifferentiableAt (by simp))
    ((hYZ.add_section hYW).mdifferentiableAt (by simp)) Filter.univ_mem heqY
  have heqX : (fun y => D.connection (Z + W) y (X y)) =ᶠ[𝓝 x]
      (fun y => D.connection Z y (X y)) + (fun y => D.connection W y (X y)) := by
    filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hZ,
      eventually_mdifferentiableAt_of_contMDiffAt hW] with y hyZ hyW
    exact congrArg (fun L => L (X y)) (D.connection.isCovariantDerivativeOn.add hyZ hyW)
  have houterX := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
    (D.contMDiffAt_covariantDerivativeOnFields hX hZW |>.mdifferentiableAt (by simp))
    ((D.contMDiffAt_covariantDerivativeOnFields hX hZ |>.add_section
      (D.contMDiffAt_covariantDerivativeOnFields hX hW)).mdifferentiableAt (by simp))
    Filter.univ_mem heqX
  have hbr := D.connection.isCovariantDerivativeOn.add
    (hZ.mdifferentiableAt (by simp)) (hW.mdifferentiableAt (by simp))
  have hsumY := D.connection.isCovariantDerivativeOn.add
    (hYZ.mdifferentiableAt (by simp)) (hYW.mdifferentiableAt (by simp))
  have hsumX := D.connection.isCovariantDerivativeOn.add
    (D.contMDiffAt_covariantDerivativeOnFields hX hZ |>.mdifferentiableAt (by simp))
    (D.contMDiffAt_covariantDerivativeOnFields hX hW |>.mdifferentiableAt (by simp))
  unfold curvatureOnFields
  change D.connection (D.covariantDerivativeOnFields Y (Z + W)) x (X x) -
      D.connection (D.covariantDerivativeOnFields X (Z + W)) x (Y x) -
      D.connection (Z + W) x (VectorField.mlieBracket (𝓡 n) X Y x) =
    (D.connection (D.covariantDerivativeOnFields Y Z) x (X x) -
      D.connection (D.covariantDerivativeOnFields X Z) x (Y x) -
      D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x)) +
    (D.connection (D.covariantDerivativeOnFields Y W) x (X x) -
      D.connection (D.covariantDerivativeOnFields X W) x (Y x) -
      D.connection W x (VectorField.mlieBracket (𝓡 n) X Y x))
  rw [congrArg (fun L => L (X x)) houterY,
    congrArg (fun L => L (Y x)) houterX,
    congrArg (fun L => L (VectorField.mlieBracket (𝓡 n) X Y x)) hbr,
    congrArg (fun L => L (X x)) hsumY,
    congrArg (fun L => L (Y x)) hsumX]
  simp only [ContinuousLinearMap.add_apply, LinearMap.add_apply, add_apply]
  module

private lemma curvatureOnFields_swap_first
    (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    D.curvatureOnFields X Y Z x = -D.curvatureOnFields Y X Z x := by
  unfold curvatureOnFields
  have hbr : VectorField.mlieBracket (𝓡 n) Y X x =
      -VectorField.mlieBracket (𝓡 n) X Y x := by
    simpa only [Pi.neg_apply] using
      congrArg (fun F => F x) (VectorField.mlieBracket_swap (I := 𝓡 n) (V := Y) (W := X))
  rw [hbr]
  simp only [map_neg]
  module

theorem curvatureTensor_swap_first
    (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = -D.curvatureTensor x v u w z := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold curvatureTensor curvature
  rw [curvatureOnFields_swap_first]
  change inner ℝ (-D.curvatureOnFields
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) w = _
  change inner ℝ (-D.curvatureOnFields
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) w =
    -inner ℝ (D.curvatureOnFields
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) w
  rw [inner_neg_left]

private lemma abs_component_le_sqrt_sum_sq {I : Type*} [Fintype I]
    (f : I → I → I → I → ℝ) (i j k l : I) :
    |f i j k l| ≤ Real.sqrt (∑ a, ∑ b, ∑ c, ∑ d, (f a b c d) ^ 2) := by
  have hsq : (f i j k l) ^ 2 ≤
      ∑ a : I, ∑ b : I, ∑ c : I, ∑ d : I, (f a b c d) ^ 2 := by
    calc
      (f i j k l) ^ 2 ≤ ∑ d : I, (f i j k d) ^ 2 := by
        exact Finset.single_le_sum (s := Finset.univ)
          (fun d _ => sq_nonneg _) (Finset.mem_univ _)
      _ ≤ ∑ c : I, ∑ d : I, (f i j c d) ^ 2 := by
        exact Finset.single_le_sum (s := Finset.univ)
          (fun c _ => Finset.sum_nonneg (fun d _ => sq_nonneg _)) (Finset.mem_univ _)
      _ ≤ ∑ b : I, ∑ c : I, ∑ d : I, (f i b c d) ^ 2 := by
        exact Finset.single_le_sum (s := Finset.univ)
          (fun b _ => Finset.sum_nonneg (fun c _ =>
            Finset.sum_nonneg (fun d _ => sq_nonneg _))) (Finset.mem_univ _)
      _ ≤ ∑ a : I, ∑ b : I, ∑ c : I, ∑ d : I, (f a b c d) ^ 2 := by
        exact Finset.single_le_sum (s := Finset.univ)
          (fun a _ => Finset.sum_nonneg (fun b _ =>
            Finset.sum_nonneg (fun c _ =>
              Finset.sum_nonneg (fun d _ => sq_nonneg _)))) (Finset.mem_univ _)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  have hnonneg : 0 ≤ ∑ a : I, ∑ b : I, ∑ c : I, ∑ d : I,
      (f a b c d) ^ 2 := by
    exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun d _ =>
        sq_nonneg _))))
  rw [sq_abs, Real.sq_sqrt hnonneg]
  exact hsq



theorem abs_curvatureTensor_orthonormal_component_le_norm
    (D : LeviCivitaData g) (x : M)
    (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |D.curvatureTensor x (g.orthonormalBasis x i)
      (g.orthonormalBasis x j) (g.orthonormalBasis x k)
      (g.orthonormalBasis x l)| ≤ D.curvatureTensorNorm x := by
  let e := g.orthonormalBasis x
  let f : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ :=
    fun a b c d => D.curvatureTensor x (e a) (e b) (e c) (e d)
  change |f i j k l| ≤ Real.sqrt (∑ a, ∑ b, ∑ c, ∑ d, (f a b c d) ^ 2)
  exact abs_component_le_sqrt_sum_sq f i j k l



theorem abs_curvatureTensor_orthonormal_component_le_max_one
    (D : LeviCivitaData g) (x : M) (k : ℝ)
    (hk : D.curvatureTensorNorm x ≤ k)
    (i j p q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |D.curvatureTensor x (g.orthonormalBasis x i)
      (g.orthonormalBasis x j) (g.orthonormalBasis x p)
      (g.orthonormalBasis x q)| ≤ max 1 k := by
  exact (abs_curvatureTensor_orthonormal_component_le_norm D x i j p q).trans
    (hk.trans (le_max_right 1 k))


theorem abs_sectionalCurvature_orthonormalBasis_pair_le_norm
    (D : LeviCivitaData g) (x : M)
    (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |D.sectionalCurvature x (g.orthonormalBasis x i)
      (g.orthonormalBasis x j)| ≤ D.curvatureTensorNorm x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 := by
    change inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1
    rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one, one_pow]
  have hj : g.inner x (g.orthonormalBasis x j) (g.orthonormalBasis x j) = 1 := by
    change inner ℝ (g.orthonormalBasis x j) (g.orthonormalBasis x j) = 1
    rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one, one_pow]
  have hij : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x j) =
      if i = j then 1 else 0 := by
    change inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x j) = _
    exact (g.orthonormalBasis x).inner_eq_ite i j
  unfold sectionalCurvature
  rw [hi, hj, hij]
  split_ifs with h
  · simp [h]
    unfold curvatureTensorNorm
    positivity
  · simpa using abs_curvatureTensor_orthonormal_component_le_norm D x i j i j


theorem sectionalCurvature_eq_zero_of_gramDet_eq_zero
    (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x)
    (hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0) :
    D.sectionalCurvature x u v = 0 := by
  unfold sectionalCurvature
  rw [hgram, div_zero]

theorem curvatureTensor_swap_last
    (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = -D.curvatureTensor x u v z w := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) u
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) v
  have hZ := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) w
  have hW := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) z
  have hZW := curvatureOnFields_add_right D hX hY hZ hW
  have hselfZ := curvature_inner_self D hX hY hZ
  have hselfW := curvature_inner_self D hX hY hW
  have hselfZW := curvature_inner_self D hX hY (hZ.add_section hW)
  rw [hZW] at hselfZW
  simp only [Pi.add_apply, map_add, add_apply, ContinuousLinearMap.add_apply] at hselfZW
  have hcross :
      g.inner x (D.curvatureOnFields X Y Z x) (W x) =
        -g.inner x (D.curvatureOnFields X Y W x) (Z x) := by
    linarith
  have hcross' :
      g.inner x (D.curvatureOnFields X Y W x) (Z x) =
        -g.inner x (D.curvatureOnFields X Y Z x) (W x) := by
    linarith [hcross]
  unfold curvatureTensor curvature
  simpa [X, Y, Z, W] using hcross'

theorem curvatureTensor_add_first
    (D : LeviCivitaData g) (x : M) (p q y r z) :
    D.curvatureTensor x (p + q) y r z =
      D.curvatureTensor x p y r z + D.curvatureTensor x q y r z := by
  have h := congrArg (fun L => L r)
    ((D.curvatureTensor_bilinear_first_third x y z).map_add p q)
  simpa only [curvatureTensor_bilinear_first_third_apply, LinearMap.add_apply] using h

theorem curvatureTensor_smul_first
    (D : LeviCivitaData g) (x : M) (c : ℝ) (p y r z) :
    D.curvatureTensor x (c • p) y r z = c * D.curvatureTensor x p y r z := by
  have h := congrArg (fun L => L r)
    ((D.curvatureTensor_bilinear_first_third x y z).map_smul c p)
  simpa only [curvatureTensor_bilinear_first_third_apply, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply] using h

theorem curvatureTensor_add_third
    (D : LeviCivitaData g) (x : M) (p y r z w) :
    D.curvatureTensor x p y (r + w) z =
      D.curvatureTensor x p y r z + D.curvatureTensor x p y w z := by
  have h := (D.curvatureTensor_bilinear_first_third x y z p).map_add r w
  simpa only [curvatureTensor_bilinear_first_third_apply, LinearMap.add_apply] using h

theorem curvatureTensor_smul_third
    (D : LeviCivitaData g) (x : M) (c : ℝ) (p y r z) :
    D.curvatureTensor x p y (c • r) z = c * D.curvatureTensor x p y r z := by
  have h := (D.curvatureTensor_bilinear_first_third x y z p).map_smul c r
  simpa only [curvatureTensor_bilinear_first_third_apply, smul_eq_mul,
    RingHom.id_apply] using h

theorem curvatureTensor_add_second
    (D : LeviCivitaData g) (x : M) (p q y r z) :
    D.curvatureTensor x p (q + y) r z =
      D.curvatureTensor x p q r z + D.curvatureTensor x p y r z := by
  have hpy := D.curvatureTensor_swap_first x p (q + y) r z
  have hq := D.curvatureTensor_swap_first x p q r z
  have hy := D.curvatureTensor_swap_first x p y r z
  have h := D.curvatureTensor_add_first x q y p r z
  rw [hpy, h, hq, hy]
  ring

theorem curvatureTensor_smul_second
    (D : LeviCivitaData g) (x : M) (c : ℝ) (p q r z) :
    D.curvatureTensor x p (c • q) r z = c * D.curvatureTensor x p q r z := by
  have hp := D.curvatureTensor_swap_first x p (c • q) r z
  have hq := D.curvatureTensor_swap_first x p q r z
  have h := D.curvatureTensor_smul_first x c q p r z
  rw [hp, h, hq]
  ring

theorem curvatureTensor_add_last
    (D : LeviCivitaData g) (x : M) (p q r z w) :
    D.curvatureTensor x p q r (z + w) =
      D.curvatureTensor x p q r z + D.curvatureTensor x p q r w := by
  have hz := D.curvatureTensor_swap_last x p q r z
  have hw := D.curvatureTensor_swap_last x p q r w
  have hzw := D.curvatureTensor_swap_last x p q r (z + w)
  have h := D.curvatureTensor_add_third x p q z r w
  rw [hzw, h, hz, hw]
  ring

theorem curvatureTensor_smul_last
    (D : LeviCivitaData g) (x : M) (c : ℝ) (p q r z) :
    D.curvatureTensor x p q r (c • z) = c * D.curvatureTensor x p q r z := by
  have hz := D.curvatureTensor_swap_last x p q r z
  have hcz := D.curvatureTensor_swap_last x p q r (c • z)
  have h := D.curvatureTensor_smul_third x c p q z r
  rw [hcz, h, hz]
  ring

theorem curvatureTensor_zero_first
    (D : LeviCivitaData g) (x : M) (p r z) :
    D.curvatureTensor x p p r z = 0 := by
  have h := D.curvatureTensor_swap_first x p p r z
  linarith

theorem curvatureTensor_zero_last
    (D : LeviCivitaData g) (x : M) (p q r) :
    D.curvatureTensor x p q r r = 0 := by
  have h := D.curvatureTensor_swap_last x p q r r
  linarith

private theorem exists_multilinear_curvatureTensor_local
    (D : LeviCivitaData g) (x : M) :
    ∃ A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) = A v := by
  let A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ :=
    { toFun := fun v => D.curvatureTensor x (v 0) (v 1) (v 2) (v 3)
      map_update_add' := by
        classical
        intro _ v i a b
        fin_cases i
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_first x a b (v 1) (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_second x (v 0) a b (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_third x (v 0) (v 1) a (v 3) b
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_add_last x (v 0) (v 1) (v 2) a b
      map_update_smul' := by
        classical
        intro _ v i c a
        fin_cases i
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_first x c a (v 1) (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_second x c (v 0) a (v 2) (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_third x c (v 0) (v 1) a (v 3)
        · simpa [Function.update, Fin.ext_iff] using
            D.curvatureTensor_smul_last x c (v 0) (v 1) (v 2) a }
  exact ⟨A, by intro v; rfl⟩



theorem abs_sectionalCurvature_le_curvatureTensorNorm
    (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    |D.sectionalCurvature x u v| ≤ D.curvatureTensorNorm x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := exists_multilinear_curvatureTensor_local D x
  by_cases hxy : LinearIndependent ℝ ![u, v]
  · obtain ⟨a, b, c, d, hdet, hx1, hy1, hxy0⟩ :=
      exists_orthonormal_changeBasis_local u v hxy
    let p := a • u + b • v
    let q := c • u + d • v
    have hnum : D.curvatureTensor x p q p q =
        (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
      simp only [p, q, curvatureTensor_add_first, curvatureTensor_add_second,
        curvatureTensor_add_third, curvatureTensor_add_last,
        curvatureTensor_smul_first, curvatureTensor_smul_second,
        curvatureTensor_smul_third, curvatureTensor_smul_last,
        curvatureTensor_zero_first, curvatureTensor_zero_last]
      rw [curvatureTensor_swap_first, curvatureTensor_swap_last,
        D.curvatureTensor_swap_first x v u u v]
      ring
    have hgram : g.inner x p p * g.inner x q q - (g.inner x p q) ^ 2 =
        (a * d - b * c) ^ 2 *
          (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
      change ((inner ℝ p p) * inner ℝ q q - (inner ℝ p q) ^ 2) =
        (a * d - b * c) ^ 2 *
          (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2)
      simp only [p, q, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_comm]
      ring
    have hchange : D.sectionalCurvature x p q = D.sectionalCurvature x u v := by
      unfold sectionalCurvature
      rw [hnum, hgram]
      field_simp [hdet]
    have hp1 : g.inner x p p = 1 := by
      change inner ℝ p p = 1
      simpa [p] using hx1
    have hq1 : g.inner x q q = 1 := by
      change inner ℝ q q = 1
      simpa [q] using hy1
    have hpq : g.inner x p q = 0 := by
      change inner ℝ p q = 0
      simpa [p, q] using hxy0
    have hsec : D.sectionalCurvature x p q = D.curvatureTensor x p q p q := by
      unfold sectionalCurvature
      rw [hp1, hq1, hpq]
      simp
    have hpnorm : g.tangentNorm x p = 1 := by
      change Real.sqrt (g.inner x p p) = 1
      rw [hp1, Real.sqrt_one]
    have hqnorm : g.tangentNorm x q = 1 := by
      change Real.sqrt (g.inner x q q) = 1
      rw [hq1, Real.sqrt_one]
    have hbound := PoincareConjecture.LeviCivitaData.abs_curvatureTensor_le_of_multilinear
      D x A hA p q p q
    have hbound' : |D.curvatureTensor x p q p q| ≤ D.curvatureTensorNorm x := by
      simpa [hpnorm, hqnorm] using hbound
    rw [← hchange, hsec]
    exact hbound'
  · rw [linearIndependent_fin2] at hxy
    have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0 := by
      by_cases hv : v = 0
      · simp [hv]
      · obtain ⟨k, hk⟩ : ∃ k : ℝ, k • v = u := by
          by_contra hn
          push_neg at hn
          exact (hxy ⟨hv, hn⟩).elim
        rw [← hk]
        change inner ℝ (k • v) (k • v) * inner ℝ v v -
          (inner ℝ (k • v) v) ^ 2 = 0
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
    rw [D.sectionalCurvature_eq_zero_of_gramDet_eq_zero x u v hgram]
    simp
    unfold curvatureTensorNorm
    positivity

theorem abs_sectionalCurvature_le_max_one
    (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) (k : ℝ)
    (hk : D.curvatureTensorNorm x ≤ k) :
    |D.sectionalCurvature x u v| ≤ max 1 k := by
  exact (D.abs_sectionalCurvature_le_curvatureTensorNorm x u v).trans
    (hk.trans (le_max_right 1 k))

end PoincareConjecture.LeviCivitaData
