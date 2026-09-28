import PoincareConjecture.Proofs.M04.ScalarHessian
import PoincareConjecture.Proofs.M04.ScalarBracket
import PoincareConjecture.Proofs.M04.CurvaturePointwise
import PoincareConjecture.Proofs.M04.CurvatureFieldsRegularity
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic








set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def shiChartField (c : OpenPartialHomeomorph M E) (v : E) :
    (y : M) → TangentSpace (𝓡 n) y :=
  VectorField.mpullback (𝓡 n) 𝓘(ℝ, E) c (fun _ => v)

noncomputable def shiChartCoordinate (c : OpenPartialHomeomorph M E)
    (i : Fin n) (y : M) : ℝ := c y i

private theorem chart_mdifferentiable {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target) :
    c.MDifferentiable (𝓡 n) 𝓘(ℝ, E) :=
  ⟨hc.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_mfderiv_isInvertible {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {y : M} (hy : y ∈ c.source) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) c y).IsInvertible :=
  ⟨(chart_mdifferentiable hc hi).mfderiv hy, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_mfderiv_inverse {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {y : M} (hy : y ∈ c.source) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) c y).inverse =
      mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm (c y) := by
  exact ContinuousLinearMap.inverse_equiv ((chart_mdifferentiable hc hi).mfderiv hy)

set_option backward.isDefEq.respectTransparency false in
theorem shiChartField_duality {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {y : M} (hy : y ∈ c.source) (v : E) :
    mvfderiv (𝓡 n) c y (shiChartField c v y) = v :=
  (shiChart_mfderiv_isInvertible hc hi hy).self_apply_inverse v

set_option backward.isDefEq.respectTransparency false in
theorem shiChartField_at_inverse {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) (v : E) :
    shiChartField c v (c.symm z) = mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z v := by
  apply ((chart_mdifferentiable hc hi).mfderiv (c.map_target hz)).injective
  change mvfderiv (𝓡 n) c (c.symm z) (shiChartField c v (c.symm z)) =
    mvfderiv (𝓡 n) c (c.symm z) (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z v)
  rw [shiChartField_duality hc hi (c.map_target hz)]
  have he := congrArg (fun A : E →L[ℝ] E => A v)
    ((chart_mdifferentiable hc hi).comp_symm_deriv hz)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using! he.symm

set_option backward.isDefEq.respectTransparency false in
theorem shiChartField_smooth {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target) (v : E) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (shiChartField c v)) c.source := by
  intro y hy
  let V : (x : E) → TangentSpace 𝓘(ℝ, E) x := fun _ => v
  have hv : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (T% V) (c y) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  exact (hv.mpullback_vectorField_preimage (hc.contMDiffAt (c.open_source.mem_nhds hy))
    (shiChart_mfderiv_isInvertible hc hi hy) (by simp)).contMDiffWithinAt

theorem shiChartCoordinate_smooth {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source) (i : Fin n) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (shiChartCoordinate c i) c.source :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.contMDiff.comp_contMDiffOn hc)

set_option backward.isDefEq.respectTransparency false in
theorem shiChartCoordinate_derivative {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    {y : M} (hy : y ∈ c.source) (i : Fin n) (a : TangentSpace (𝓡 n) y) :
    mvfderiv (𝓡 n) (shiChartCoordinate c i) y a =
      (mvfderiv (𝓡 n) c y a) i := by
  let p : E →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i
  have hd := (hc.contMDiffAt (c.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  change mvfderiv (𝓡 n) (p ∘ c) y a = _
  rw [mvfderiv_comp_apply y p.differentiableAt.mdifferentiableAt hd a]
  simpa only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] using!
    congrArg (fun K : E →L[ℝ] ℝ => K (mvfderiv (𝓡 n) c y a))
      (p.fderiv (x := c y))

theorem shiChartCoordinate_field_derivative {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {y : M} (hy : y ∈ c.source) (i : Fin n) (v : E) :
    mvfderiv (𝓡 n) (shiChartCoordinate c i) y (shiChartField c v y) = v i := by
  rw [shiChartCoordinate_derivative hc hy, shiChartField_duality hc hi hy]

theorem contMDiffOn_shi_connection (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (fun y => D.connection Y y (X y))) U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_section_of_metric_pairings g (fun y => D.connection Y y (X y))
  intro v
  let t := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  have hx' : x ∈ U ∩ t.baseSet := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  exact (contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
    (hX.mono inter_subset_left) (hY.mono inter_subset_left)
    ((contMDiffOn_extend_baseSet v).mono inter_subset_right)).contMDiffAt
      ((hU.inter t.open_baseSet).mem_nhds hx')

set_option backward.isDefEq.respectTransparency false in
theorem shiChartField_bracket_eq_zero {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {y : M} (hy : y ∈ c.source) (u v : E) :
    VectorField.mlieBracket (𝓡 n) (shiChartField c u) (shiChartField c v) y = 0 := by
  apply ((chart_mdifferentiable hc hi).mfderiv hy).injective
  change mvfderiv (𝓡 n) c y
    (VectorField.mlieBracket (𝓡 n) (shiChartField c u) (shiChartField c v) y) =
      mvfderiv (𝓡 n) c y 0
  rw [map_zero]
  ext i
  rw [← shiChartCoordinate_derivative hc hy]
  have hconst (w : E) :
      (fun x => mvfderiv (𝓡 n) (shiChartCoordinate c i) x (shiChartField c w x))
        =ᶠ[𝓝 y] (fun _ => w i) := by
    filter_upwards [c.open_source.mem_nhds hy] with x hx
    exact shiChartCoordinate_field_derivative hc hi hx i w
  have hbr := mvfderiv_mlieBracket c.open_source (shiChartCoordinate_smooth hc i)
    (shiChartField_smooth hc hi u) (shiChartField_smooth hc hi v) hy
  have hu : mvfderiv (𝓡 n)
      (fun x => mvfderiv (𝓡 n) (shiChartCoordinate c i) x (shiChartField c u x)) y =
      mvfderiv (𝓡 n) (fun _ : M => u i) y := (hconst u).mfderiv_eq
  have hv : mvfderiv (𝓡 n)
      (fun x => mvfderiv (𝓡 n) (shiChartCoordinate c i) x (shiChartField c v x)) y =
      mvfderiv (𝓡 n) (fun _ : M => v i) y := (hconst v).mfderiv_eq
  rw [hu, hv, mvfderiv_const, mvfderiv_const] at hbr
  simpa only [ContinuousLinearMap.zero_apply, sub_zero, PiLp.zero_apply] using hbr

set_option backward.isDefEq.respectTransparency false in
theorem shiChartCoordinate_hessian_fields [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {y : M} (hy : y ∈ c.source) (i : Fin n) (u v : E) :
    D.hessian (shiChartCoordinate c i) y (shiChartField c u y) (shiChartField c v y) =
      -mvfderiv (𝓡 n) (shiChartCoordinate c i) y
        (D.connection (shiChartField c v) y (shiChartField c u y)) := by
  have he : (fun x => mvfderiv (𝓡 n) (shiChartCoordinate c i) x (shiChartField c v x))
      =ᶠ[𝓝 y] (fun _ => v i) := by
    filter_upwards [c.open_source.mem_nhds hy] with x hx
    exact shiChartCoordinate_field_derivative hc hi hx i v
  have hd : mvfderiv (𝓡 n)
      (fun x => mvfderiv (𝓡 n) (shiChartCoordinate c i) x (shiChartField c v x)) y =
      mvfderiv (𝓡 n) (fun _ : M => v i) y := he.mfderiv_eq
  rw [← hessianOnFields_eq_hessian_of_contMDiffOn D c.open_source
    (shiChartCoordinate_smooth hc i) (shiChartField_smooth hc hi u)
    (shiChartField_smooth hc hi v) hy]
  simp only [LeviCivitaData.hessianOnFields, hd, mvfderiv_const,
    ContinuousLinearMap.zero_apply, zero_sub]

set_option backward.isDefEq.respectTransparency false in
theorem shiChartCoordinate_connection [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {U : Set M} (hU : IsOpen U) (hUc : U ⊆ c.source)
    {Y : (x : M) → TangentSpace (𝓡 n) x}
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) U)
    {y : M} (hy : y ∈ U) (i : Fin n) (u : E) :
    (mvfderiv (𝓡 n) c y
      (D.connection Y y (shiChartField c u y))) i =
      mvfderiv (𝓡 n)
          (fun x => mvfderiv (𝓡 n) (shiChartCoordinate c i) x (Y x)) y
          (shiChartField c u y) -
        D.hessian (shiChartCoordinate c i) y (shiChartField c u y) (Y y) := by
  have he := hessianOnFields_eq_hessian_of_contMDiffOn D hU
    ((shiChartCoordinate_smooth hc i).mono hUc)
    ((shiChartField_smooth hc hi u).mono hUc) hY hy
  rw [LeviCivitaData.hessianOnFields, shiChartCoordinate_derivative hc (hUc hy)] at he
  linarith only [he]

noncomputable def shiChartChristoffel (D : LeviCivitaData g)
    (c : OpenPartialHomeomorph M E) (z : E) : E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    (-D.hessian (shiChartCoordinate c i) (c.symm z)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z (EuclideanSpace.basisFun (Fin n) ℝ j))
      (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z (EuclideanSpace.basisFun (Fin n) ℝ k))) •
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).smulRight
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).smulRight
            (EuclideanSpace.basisFun (Fin n) ℝ i))

private theorem hessian_bilinear_rep [T2Space M] (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {q : M → ℝ}
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) {x : M} (hx : x ∈ U) :
    ∃ B : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ,
      ∀ a b, B a b = D.hessian q x a b := by
  obtain ⟨A, hA⟩ := exists_hessian_bilinear_of_contMDiffOn D hU hq hx
  let B := (MultilinearMap.ofSubsingletonₗ ℝ ℝ (TangentSpace (𝓡 n) x) ℝ
    (0 : Fin 1)).symm.toLinearMap.comp A.curryLeft
  refine ⟨B, ?_⟩
  intro a b
  change A (Fin.cons a (fun _ : Fin 1 => b)) = D.hessian q x a b
  exact (hA (Fin.cons a (fun _ : Fin 1 => b))).symm

set_option backward.isDefEq.respectTransparency false in
theorem shiChartChristoffel_component [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    {z : E} (hz : z ∈ c.target) (i : Fin n) (u v : E) :
    (shiChartChristoffel D c z u v) i =
      -D.hessian (shiChartCoordinate c i) (c.symm z)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z v) := by
  classical
  let S : E →L[ℝ] TangentSpace (𝓡 n) (c.symm z) :=
    mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  obtain ⟨B, hB⟩ := hessian_bilinear_rep D c.open_source
    (shiChartCoordinate_smooth hc i) (c.map_target hz)
  have hS (w : E) : S w = ∑ j, w j • S (e j) := by
    have he : (∑ j, w j • e j) = w := by
      simpa only [e, EuclideanSpace.basisFun_repr] using e.sum_repr w
    calc
      S w = S (∑ j, w j • e j) := congrArg S he.symm
      _ = ∑ j, w j • S (e j) := by simp only [map_sum, map_smul]
  have hsum : B (S u) (S v) = ∑ j, ∑ k, u j * v k * B (S (e j)) (S (e k)) := by
    rw [hS u, hS v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    simp only [mul_left_comm]
  have hcoord : (shiChartChristoffel D c z u v) i =
      ∑ j, ∑ k, u j * v k *
        (-D.hessian (shiChartCoordinate c i) (c.symm z) (S (e j)) (S (e k))) := by
    simp only [shiChartChristoffel, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
      PiLp.smul_apply, smul_eq_mul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply, WithLp.ofLp_sum, Finset.sum_apply]
    simp [S, e, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] <;> rfl
  rw [hcoord]
  simp_rw [← hB, mul_neg]
  simpa only [S, Finset.sum_neg_distrib] using! congrArg Neg.neg hsum.symm

set_option backward.isDefEq.respectTransparency false in
theorem shiChartChristoffel_connection [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) (u v : E) :
    shiChartChristoffel D c z u v =
      mvfderiv (𝓡 n) c (c.symm z)
        (D.connection (shiChartField c v) (c.symm z)
          (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u)) := by
  ext i
  rw [shiChartChristoffel_component D hc hz,
    ← shiChartField_at_inverse hc hi hz u, ← shiChartField_at_inverse hc hi hz v,
    shiChartCoordinate_hessian_fields D hc hi (c.map_target hz), neg_neg,
    shiChartCoordinate_derivative hc (c.map_target hz)]

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_inverse_derivative_apply {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) (a : TangentSpace (𝓡 n) (c.symm z)) :
    mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z
      (mvfderiv (𝓡 n) c (c.symm z) a) = a := by
  apply ((chart_mdifferentiable hc hi).mfderiv (c.map_target hz)).injective
  change mvfderiv (𝓡 n) c (c.symm z)
    (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z (mvfderiv (𝓡 n) c (c.symm z) a)) =
      mvfderiv (𝓡 n) c (c.symm z) a
  rw [← shiChartField_at_inverse hc hi hz, shiChartField_duality hc hi (c.map_target hz)]

noncomputable def shiChartVector (c : OpenPartialHomeomorph M E)
    (Y : (x : M) → TangentSpace (𝓡 n) x) (z : E) : E :=
  mvfderiv (𝓡 n) c (c.symm z) (Y (c.symm z))

set_option backward.isDefEq.respectTransparency false in
theorem shiChartVector_smoothAt {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {z : E} (hz : z ∈ c.target)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) (c.symm z)) :
    ContDiffAt ℝ ∞ (shiChartVector c Y) z := by
  apply (contDiffAt_piLp 2).mpr
  intro i
  have hq := (shiChartCoordinate_smooth hc i).contMDiffAt
    (c.open_source.mem_nhds (c.map_target hz))
  have hd := contMDiffAt_directional_derivative hq hY
  have hcomp := hd.comp z (hi.contMDiffAt (c.open_target.mem_nhds hz))
  apply hcomp.contDiffAt.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hz] with w hw
  exact (shiChartCoordinate_derivative hc (c.map_target hw) i (Y (c.symm w))).symm

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_scalar_derivative {c : OpenPartialHomeomorph M E}
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) {q : M → ℝ}
    (hq : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q (c.symm z)) (u : E) :
    fderiv ℝ (q ∘ c.symm) z u =
      mvfderiv (𝓡 n) q (c.symm z) (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u) := by
  have he := mfderiv_comp z hq
    ((hi.contMDiffAt (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp))
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] using!
    congrArg (fun A => A u) he

set_option backward.isDefEq.respectTransparency false in
theorem shiChartVector_component_derivative {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {z : E} (hz : z ∈ c.target)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) (c.symm z))
    (i : Fin n) (u : E) :
    (fderiv ℝ (shiChartVector c Y) z u) i =
      mvfderiv (𝓡 n)
        (fun y => mvfderiv (𝓡 n) (shiChartCoordinate c i) y (Y y))
        (c.symm z) (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u) := by
  let p : E →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i
  let q : M → ℝ := fun y => mvfderiv (𝓡 n) (shiChartCoordinate c i) y (Y y)
  have hd := (shiChartVector_smoothAt hc hi hz hY).differentiableAt (by simp)
  have hp := (p.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  have he : (p ∘ shiChartVector c Y) =ᶠ[𝓝 z] (q ∘ c.symm) := by
    filter_upwards [c.open_target.mem_nhds hz] with w hw
    exact (shiChartCoordinate_derivative hc (c.map_target hw) i (Y (c.symm w))).symm
  have hq := contMDiffAt_directional_derivative
    ((shiChartCoordinate_smooth hc i).contMDiffAt
      (c.open_source.mem_nhds (c.map_target hz))) hY
  calc
    _ = fderiv ℝ (p ∘ shiChartVector c Y) z u :=
      (congrArg (fun A => A u) hp).symm
    _ = fderiv ℝ (q ∘ c.symm) z u :=
      congrArg (fun A : E →L[ℝ] ℝ => A u) (he.fderiv_eq (𝕜 := ℝ))
    _ = _ := shiChart_scalar_derivative hi hz (hq.mdifferentiableAt (by simp)) u

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_connection_formula [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {U : Set M} (hU : IsOpen U) (hUc : U ⊆ c.source)
    {Y : (x : M) → TangentSpace (𝓡 n) x}
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) U)
    {z : E} (hz : z ∈ c.target) (hzU : c.symm z ∈ U) (u : E) :
    mvfderiv (𝓡 n) c (c.symm z)
      (D.connection Y (c.symm z) (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u)) =
      fderiv ℝ (shiChartVector c Y) z u +
        shiChartChristoffel D c z u (shiChartVector c Y z) := by
  ext i
  rw [PiLp.add_apply, shiChartVector_component_derivative hc hi hz
    (hY.contMDiffAt (hU.mem_nhds hzU)), shiChartChristoffel_component D hc hz]
  rw [shiChartVector, shiChart_inverse_derivative_apply hc hi hz,
    ← shiChartField_at_inverse hc hi hz u,
    shiChartCoordinate_connection D hc hi hU hUc hY hzU]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem shiChartChristoffel_smooth [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target) :
    ContDiffOn ℝ ∞ (shiChartChristoffel D c) c.target := by
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_clm_apply]
  intro v z hz
  have hZ := contMDiffOn_shi_connection D c.open_source
    (shiChartField_smooth hc hi u) (shiChartField_smooth hc hi v)
  have hs := shiChartVector_smoothAt hc hi hz
    (hZ.contMDiffAt (c.open_source.mem_nhds (c.map_target hz)))
  apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [c.open_target.mem_nhds hz] with w hw
  rw [shiChartChristoffel_connection D hc hi hw, shiChartVector,
    shiChartField_at_inverse hc hi hw u]

set_option backward.isDefEq.respectTransparency false in
theorem shiChartChristoffel_symm [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) (u v : E) :
    shiChartChristoffel D c z u v = shiChartChristoffel D c z v u := by
  have hX (w : E) := ((shiChartField_smooth hc hi w).contMDiffAt
    (c.open_source.mem_nhds (c.map_target hz))).mdifferentiableAt (by simp)
  have he := connection_commutator D (hX u) (hX v)
  rw [shiChartField_bracket_eq_zero hc hi (c.map_target hz)] at he
  rw [shiChartChristoffel_connection D hc hi hz, shiChartChristoffel_connection D hc hi hz,
    ← shiChartField_at_inverse hc hi hz u, ← shiChartField_at_inverse hc hi hz v,
    sub_eq_zero.mp he]

set_option backward.isDefEq.respectTransparency false in
noncomputable def shiChartMetric (g : RiemannianMetric n M)
    (c : OpenPartialHomeomorph M E) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let S : E →L[ℝ] TangentSpace (𝓡 n) (c.symm z) :=
    mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z
  (g.inner (c.symm z)).bilinearComp S S

set_option backward.isDefEq.respectTransparency false in
theorem shiChartMetric_smooth (g : RiemannianMetric n M)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target) :
    ContDiffOn ℝ ∞ (shiChartMetric g c) c.target := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_clm_apply]
  intro v z hz
  have hs := (shiChartField_smooth hc hi u).inner_bundle (shiChartField_smooth hc hi v)
  have hp := (hs.contMDiffAt (c.open_source.mem_nhds (c.map_target hz))).comp z
    (hi.contMDiffAt (c.open_target.mem_nhds hz))
  apply (hp.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [c.open_target.mem_nhds hz] with w hw
  change g.inner (c.symm w) _ _ = g.inner (c.symm w) _ _
  rw [shiChartField_at_inverse hc hi hw u, shiChartField_at_inverse hc hi hw v]
  rfl

theorem shiChartMetric_symm (g : RiemannianMetric n M)
    (c : OpenPartialHomeomorph M E) (z u v : E) :
    shiChartMetric g c z u v = shiChartMetric g c z v u :=
  g.symm _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem shiChartMetric_pos (g : RiemannianMetric n M)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) {u : E} (hu : u ≠ 0) :
    0 < shiChartMetric g c z u u := by
  apply g.pos
  intro he
  have he' : mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u = 0 := he
  have hv : mvfderiv (𝓡 n) c (c.symm z)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u) = u := by
    rw [← shiChartField_at_inverse hc hi hz, shiChartField_duality hc hi (c.map_target hz)]
  rw [he', map_zero] at hv
  exact hu hv.symm

set_option synthInstance.maxHeartbeats 100000 in

set_option backward.isDefEq.respectTransparency false in
private theorem shi_fderiv_bilinear_eval {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : E → E →L[ℝ] E →L[ℝ] F} {z : E}
    (hB : DifferentiableAt ℝ B z) (u v w : E) :
    fderiv ℝ (fun a => B a u v) z w = (fderiv ℝ B z w) u v := by
  have h := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const u z)).clm_apply
    (hasFDerivAt_const v z)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, zero_apply, map_zero, add_zero, zero_add] using!
    congrArg (fun A : E →L[ℝ] F => A w) h.fderiv

set_option backward.isDefEq.respectTransparency false in
theorem shiChartMetric_derivative [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) (u v w : E) :
    (fderiv ℝ (shiChartMetric g c) z v) u w =
      shiChartMetric g c z (shiChartChristoffel D c z v u) w +
        shiChartMetric g c z u (shiChartChristoffel D c z v w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let q : M → ℝ := fun y => g.inner y (shiChartField c u y) (shiChartField c w y)
  have hX (a : E) := (shiChartField_smooth hc hi a).contMDiffAt
    (c.open_source.mem_nhds (c.map_target hz))
  have hq : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ q (c.symm z) :=
    (hX u).inner_bundle (hX w)
  have he : (fun a => shiChartMetric g c a u w) =ᶠ[𝓝 z] (q ∘ c.symm) := by
    filter_upwards [c.open_target.mem_nhds hz] with a ha
    change g.inner (c.symm a) _ _ = g.inner (c.symm a) _ _
    rw [shiChartField_at_inverse hc hi ha u, shiChartField_at_inverse hc hi ha w]
    rfl
  have hb := metric_derivative_pairing D (shiChartField c v)
    ((hX u).mdifferentiableAt (by simp)) ((hX w).mdifferentiableAt (by simp))
  calc
    _ = fderiv ℝ (fun a => shiChartMetric g c a u w) z v :=
      (shi_fderiv_bilinear_eval
        (((shiChartMetric_smooth g hc hi).contDiffAt
          (c.open_target.mem_nhds hz)).differentiableAt (by simp)) u w v).symm
    _ = fderiv ℝ (q ∘ c.symm) z v :=
      congrArg (fun A : E →L[ℝ] ℝ => A v) (he.fderiv_eq (𝕜 := ℝ))
    _ = mvfderiv (𝓡 n) q (c.symm z) (shiChartField c v (c.symm z)) := by
      rw [shiChart_scalar_derivative hi hz (hq.mdifferentiableAt (by simp)),
        shiChartField_at_inverse hc hi hz]
    _ = _ := by
      rw [hb]
      simp only [shiChartMetric, ContinuousLinearMap.bilinearComp_apply,
        shiChartChristoffel_connection D hc hi hz,
        shiChartField_at_inverse hc hi hz]
      erw [shiChart_inverse_derivative_apply hc hi hz,
        shiChart_inverse_derivative_apply hc hi hz]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_curvature_formula [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {z : E} (hz : z ∈ c.target) (u v w : E) :
    mvfderiv (𝓡 n) c (c.symm z)
      (D.curvature (c.symm z)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z u)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z v)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm z w)) =
      (fderiv ℝ (shiChartChristoffel D c) z u) v w -
        (fderiv ℝ (shiChartChristoffel D c) z v) u w +
        shiChartChristoffel D c z u (shiChartChristoffel D c z v w) -
        shiChartChristoffel D c z v (shiChartChristoffel D c z u w) := by
  let Z (a b : E) : (y : M) → TangentSpace (𝓡 n) y :=
    fun y => D.connection (shiChartField c b) y (shiChartField c a y)
  have hZ (a b : E) := contMDiffOn_shi_connection D c.open_source
    (shiChartField_smooth hc hi a) (shiChartField_smooth hc hi b)
  have he (a b : E) : shiChartVector c (Z a b) =ᶠ[𝓝 z]
      (fun d => shiChartChristoffel D c d a b) := by
    filter_upwards [c.open_target.mem_nhds hz] with d hd
    dsimp only [shiChartVector, Z]
    erw [shiChartChristoffel_connection D hc hi hd,
      shiChartField_at_inverse hc hi hd a]
  have hΓ := ((shiChartChristoffel_smooth D hc hi).contDiffAt
    (c.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hconn (a b d : E) :
      mvfderiv (𝓡 n) c (c.symm z)
        (D.connection (Z b d) (c.symm z) (shiChartField c a (c.symm z))) =
        (fderiv ℝ (shiChartChristoffel D c) z a) b d +
          shiChartChristoffel D c z a (shiChartChristoffel D c z b d) := by
    rw [shiChartField_at_inverse hc hi hz a,
      shiChart_connection_formula D hc hi c.open_source (fun _ h => h)
        (hZ b d) hz (c.map_target hz), (he b d).fderiv_eq,
      shi_fderiv_bilinear_eval hΓ, (he b d).eq_of_nhds]
  rw [← shiChartField_at_inverse hc hi hz u, ← shiChartField_at_inverse hc hi hz v,
    ← shiChartField_at_inverse hc hi hz w,
    ← curvatureOnFields_eq_curvature D c.open_source
      (shiChartField_smooth hc hi u) (shiChartField_smooth hc hi v)
      (shiChartField_smooth hc hi w) (c.map_target hz),
    LeviCivitaData.curvatureOnFields,
    shiChartField_bracket_eq_zero hc hi (c.map_target hz), map_zero, sub_zero, map_sub]
  change mvfderiv (𝓡 n) c (c.symm z)
    (D.connection (Z v w) (c.symm z) (shiChartField c u (c.symm z))) -
    mvfderiv (𝓡 n) c (c.symm z)
      (D.connection (Z u w) (c.symm z) (shiChartField c v (c.symm z))) = _
  rw [hconn, hconn]
  abel

end PoincareConjecture.M04

