import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Contact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.SupportingLaplacian










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology
open Matrix

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {I : Type} [Fintype I]



lemma laplacian_quadratic_at_null
    (D : LeviCivitaData g) {A : M → Matrix I I ℝ} {z : M → I → ℝ}
    (hA : ∀ i j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => A y i j))
    (hz : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => z y i))
    {x : M} (hpos : (A x).PosSemidef)
    (hnull : z x ⬝ᵥ (A x *ᵥ z x) = 0) :
    D.laplacian (fun y => z y ⬝ᵥ (A y *ᵥ z y)) x =
      (∑ i, ∑ j, z x i * D.laplacian (fun y => A y i j) x * z x j) +
      2 * (∑ i, ∑ j,
        (z x i * g.inner x (D.gradient (fun y => A y i j) x)
          (D.gradient (fun y => z y j) x) +
        z x j * g.inner x (D.gradient (fun y => z y i) x)
          (D.gradient (fun y => A y i j) x) +
        A x i j * g.inner x (D.gradient (fun y => z y i) x)
          (D.gradient (fun y => z y j) x))) := by
  have hzero : A x *ᵥ z x = 0 :=
    (hpos.dotProduct_mulVec_zero_iff (z x)).mp (by simpa only [star_trivial] using hnull)
  have hright (i : I) : (∑ j, A x i j * z x j) = 0 := congrFun hzero i
  have hleft (j : I) : (∑ i, z x i * A x i j) = 0 := by
    have hs (i : I) : A x i j = A x j i := by
      simpa only [star_trivial] using hpos.1.apply j i
    simpa only [hs, mul_comm] using hright j
  have hcross₁ : (∑ i, ∑ j,
      z x i * A x i j * D.laplacian (fun y => z y j) x) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hleft, zero_mul, Finset.sum_const_zero]
  have hcross₂ : (∑ i, ∑ j,
      D.laplacian (fun y => z y i) x * (A x i j * z x j)) = 0 := by
    simp only [← Finset.mul_sum, hright, mul_zero, Finset.sum_const_zero]
  have hterm (i j : I) :
      D.laplacian (fun y => z y i * A y i j * z y j) x =
        z x i * A x i j * D.laplacian (fun y => z y j) x +
        D.laplacian (fun y => z y i) x * (A x i j * z x j) +
        z x i * D.laplacian (fun y => A y i j) x * z x j +
        2 * (z x i * g.inner x (D.gradient (fun y => A y i j) x)
            (D.gradient (fun y => z y j) x) +
          z x j * g.inner x (D.gradient (fun y => z y i) x)
            (D.gradient (fun y => A y i j) x) +
          A x i j * g.inner x (D.gradient (fun y => z y i) x)
            (D.gradient (fun y => z y j) x)) := by
    erw [D.laplacian_mul (f := fun y => z y i * A y i j)
        (h := fun y => z y j) ((hz i).mul (hA i j)) (hz j),
      D.laplacian_mul (hz i) (hA i j),
      D.gradient_mul ((hz i x).mdifferentiableAt (by simp))
        ((hA i j x).mdifferentiableAt (by simp))]
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have heval : (fun y => z y ⬝ᵥ (A y *ᵥ z y)) =
      (fun y => ∑ i, ∑ j, z y i * A y i j * z y j) := by
    funext y
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [heval]
  have hsmooth (i : I) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ j, z y i * A y i j * z y j) := by
    exact ContMDiff.sum fun j _ => ((hz i).mul (hA i j)).mul (hz j)
  erw [D.laplacian_sum_on_open (fun i y => ∑ j, z y i * A y i j * z y j) isOpen_univ
    (fun i => (hsmooth i).contMDiffOn) (Set.mem_univ x)]
  have hsum (i : I) := D.laplacian_sum_on_open
    (fun j y => z y i * A y i j * z y j) isOpen_univ
    (fun j => (((hz i).mul (hA i j)).mul (hz j)).contMDiffOn) (Set.mem_univ x)
  simp_rw [hsum, hterm]
  simp only [Finset.sum_add_distrib, hcross₁, hcross₂, zero_add]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]



lemma laplacian_quadratic_nonneg_at_null
    (D : LeviCivitaData g) {A : M → Matrix I I ℝ} {z : M → I → ℝ}
    (hA : ∀ i j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => A y i j))
    (hz : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => z y i))
    {x : M} (hpos : ∀ᶠ y in 𝓝 x, (A y).PosSemidef)
    (hnull : z x ⬝ᵥ (A x *ᵥ z x) = 0) :
    0 ≤ (∑ i, ∑ j, z x i * D.laplacian (fun y => A y i j) x * z x j) +
      2 * (∑ i, ∑ j,
        (z x i * g.inner x (D.gradient (fun y => A y i j) x)
          (D.gradient (fun y => z y j) x) +
        z x j * g.inner x (D.gradient (fun y => z y i) x)
          (D.gradient (fun y => A y i j) x) +
        A x i j * g.inner x (D.gradient (fun y => z y i) x)
          (D.gradient (fun y => z y j) x))) := by
  rw [← laplacian_quadratic_at_null D hA hz hpos.self_of_nhds hnull]
  apply D.horizon_laplacian_nonneg_of_isLocalMin
  · simp only [dotProduct, mulVec]
    exact ContMDiff.sum fun i _ => (hz i).mul
      (ContMDiff.sum fun j _ => (hA i j).mul (hz j))
  · filter_upwards [hpos] with y hy
    change z x ⬝ᵥ (A x *ᵥ z x) ≤ z y ⬝ᵥ (A y *ᵥ z y)
    rw [hnull]
    simpa only [star_trivial] using hy.dotProduct_mulVec_nonneg (z y)

private lemma exists_smooth_scalar_germ [T2Space M]
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U) :
    ∃ F : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] f := by
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hU.mem_nhds hx)
  refine ⟨fun y => b y * f y, ?_, ?_⟩
  · apply contMDiff_of_tsupport
    intro y hy
    have hyU : y ∈ U := hb (tsupport_mul_subset_left hy)
    exact b.contMDiffAt.mul ((hf y hyU).contMDiffAt (hU.mem_nhds hyU))
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp only [hy, Pi.one_apply, one_mul]

private lemma exists_smooth_scalar_first_jet [T2Space M]
    (x : M) (c : ℝ) (L : TangentSpace (𝓡 n) x →L[ℝ] ℝ) :
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧ f x = c ∧
      mvfderiv (𝓡 n) f x = L := by
  let chart := extChartAt (𝓡 n) x
  let e : TangentSpace (𝓡 n) x ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun v => v
      invFun := fun v => v
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Lc : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    L.comp e.symm.toContinuousLinearMap
  let h : EuclideanSpace ℝ (Fin n) → ℝ := fun v => c + Lc (v - chart x)
  have hL : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => Lc (v - chart x)) :=
    Lc.contDiff.comp (contDiff_id.sub contDiff_const)
  have hh : ContDiff ℝ ∞ h := contDiff_const.add hL
  have hlocal : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h ∘ chart) chart.source := by
    apply hh.contMDiff.comp_contMDiffOn
    simpa only [chart, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ∞))
  obtain ⟨f, hf, heq⟩ := exists_smooth_scalar_germ
    (isOpen_extChartAt_source x) hlocal (mem_extChartAt_source x)
  refine ⟨f, hf, ?_, ?_⟩
  · rw [heq.self_of_nhds]
    simp [h]
  · rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
    have hd := (Lc.hasFDerivAt.comp (chart x)
      ((hasFDerivAt_id (chart x)).sub_const (chart x))).const_add c
    have hd' : fderiv ℝ h (chart x) = Lc := by
      simpa only [h, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using! hd.fderiv
    rw [mvfderiv_comp x (hh.differentiable (by simp)).differentiableAt.mdifferentiableAt
      (mdifferentiableAt_extChartAt (mem_chart_source _ _))]
    simp only [mfderiv_extChartAt_self, ContinuousLinearMap.comp_id]
    simp only [mvfderiv, mfderiv_eq_fderiv]
    ext v
    change fderiv ℝ h (chart x) (e v) = L v
    rw [hd']
    change L (e.symm (e v)) = L v
    rw [e.symm_apply_apply]



lemma laplacian_quadratic_nonneg_at_null_on_open [T2Space M]
    (D : LeviCivitaData g) {A : M → Matrix I I ℝ} {z : M → I → ℝ}
    {U : Set M} (hU : IsOpen U)
    (hA : ∀ i j, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => A y i j) U)
    (hz : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => z y i) U)
    {x : M} (hx : x ∈ U) (hpos : ∀ᶠ y in 𝓝 x, (A y).PosSemidef)
    (hnull : z x ⬝ᵥ (A x *ᵥ z x) = 0) :
    0 ≤ (∑ i, ∑ j, z x i * D.laplacian (fun y => A y i j) x * z x j) +
      2 * (∑ i, ∑ j,
        (z x i * g.inner x (D.gradient (fun y => A y i j) x)
          (D.gradient (fun y => z y j) x) +
        z x j * g.inner x (D.gradient (fun y => z y i) x)
          (D.gradient (fun y => A y i j) x) +
        A x i j * g.inner x (D.gradient (fun y => z y i) x)
          (D.gradient (fun y => z y j) x))) := by
  classical
  choose B hB hBeq using fun i j => exists_smooth_scalar_germ hU (hA i j) hx
  choose w hw hweq using fun i => exists_smooth_scalar_germ hU (hz i) hx
  have hmatrix : (fun y i j => B i j y) =ᶠ[𝓝 x] A := by
    filter_upwards [Filter.eventually_all.mpr
      (fun i => Filter.eventually_all.mpr (hBeq i))] with y hy
    exact funext fun i => funext fun j => hy i j
  have hvector : (fun y i => w i y) =ᶠ[𝓝 x] z := by
    filter_upwards [Filter.eventually_all.mpr hweq] with y hy
    exact funext hy
  have hpositive : ∀ᶠ y in 𝓝 x, Matrix.PosSemidef (fun i j => B i j y) := by
    filter_upwards [hmatrix, hpos] with y hy hp
    simpa only [hy] using hp
  have hnull' : (fun i => w i x) ⬝ᵥ ((fun i j => B i j x) *ᵥ (fun i => w i x)) = 0 := by
    simpa only [hmatrix.self_of_nhds, hvector.self_of_nhds] using hnull
  have h := laplacian_quadratic_nonneg_at_null D hB hw hpositive hnull'
  have hgrad {f k : M → ℝ} (heq : f =ᶠ[𝓝 x] k) : D.gradient f x = D.gradient k x := by
    unfold LeviCivitaData.gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  simpa only [(hweq _).self_of_nhds, (hBeq _ _).self_of_nhds,
    D.laplacian_eq_of_eventuallyEq (hBeq _ _), hgrad (hBeq _ _), hgrad (hweq _)] using h



lemma quadratic_diffusion_nonneg_of_prescribed_gradients [T2Space M]
    (D : LeviCivitaData g) {A : M → Matrix I I ℝ}
    {U : Set M} (hU : IsOpen U)
    (hA : ∀ i j, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => A y i j) U)
    {x : M} (hx : x ∈ U) (hpos : ∀ᶠ y in 𝓝 x, (A y).PosSemidef)
    (z : I → ℝ) (hnull : z ⬝ᵥ (A x *ᵥ z) = 0)
    (V : I → TangentSpace (𝓡 n) x) :
    0 ≤ (∑ i, ∑ j, z i * D.laplacian (fun y => A y i j) x * z j) +
      2 * (∑ i, ∑ j,
        (z i * g.inner x (D.gradient (fun y => A y i j) x) (V j) +
        z j * g.inner x (V i) (D.gradient (fun y => A y i j) x) +
        A x i j * g.inner x (V i) (V j))) := by
  classical
  choose w hw hwval hwderiv using
    fun i => exists_smooth_scalar_first_jet x (z i) (g.inner x (V i))
  have hwgrad (i : I) : D.gradient (w i) x = V i := by
    apply (g.inner_isInvertible x).injective
    ext v
    rw [D.inner_gradient, hwderiv i]
  have hn : (fun i => w i x) ⬝ᵥ (A x *ᵥ (fun i => w i x)) = 0 := by
    simpa only [hwval] using hnull
  have h := laplacian_quadratic_nonneg_at_null_on_open D hU hA
    (fun i => (hw i).contMDiffOn) hx hpos hn
  simpa only [hwval, hwgrad] using h

end Poincare.RicciFlow.Harnack
