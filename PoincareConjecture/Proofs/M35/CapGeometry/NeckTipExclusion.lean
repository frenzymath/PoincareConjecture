import PoincareConjecture.Proofs.M35.CapGeometry.TipNeckRealization
import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureLimit











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)



theorem exists_cylinder_tip_exclusion :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (g : RiemannianMetric 3 StandardCapSpace) (_D : LeviCivitaData g),
        (∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
          ∀ x u v : StandardCapSpace,
            g.inner (standardRotation A x)
              (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
              (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v) →
        ∀ (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x),
          RoundCylinderClose epsilon 0 (roundCylinderPullback g N.coordinate) →
            (0 : StandardCapSpace) ∉ N.carrier := by
  classical
  by_contra hnone
  push Not at hnone
  have hbad (n : ℕ) := hnone (min (1 / 4) (1 / ((n : ℝ) + 1))) (by positivity)
  choose epsilon he hemax g D hrotation x N hclose htip using hbad
  have hk (n : ℕ) : 2 ≤ ⌊(epsilon n)⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ (he n)]
    norm_num only [Nat.cast_ofNat]
    have hquarter := (hemax n).trans (min_le_left _ _)
    linarith
  have hezero : Tendsto epsilon atTop (𝓝 0) :=
    squeeze_zero (fun n => (he n).le)
      (fun n => (hemax n).trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hpre (n : ℕ) : ∃ (q : UnitTwoSphere) (s : ℝ),
      s ∈ Ioo (-(epsilon n)⁻¹) (epsilon n)⁻¹ ∧ (N n).coordinate (q, s) = 0 := by
    have hn := htip n
    rw [← (N n).coordinate_image] at hn
    obtain ⟨⟨q, s⟩, hz, hzero⟩ := hn
    exact ⟨q, s, hz.2, hzero⟩
  choose q s hs hcoordinate using hpre
  choose G DG hG hisotropic using fun n =>
    exists_tip_neck_metric_realization (g n) (D n) (hrotation n) (N n)
      (q n) (s n) (hs n) (hcoordinate n)
  let model := cylinderEuclideanMetric 0 (by norm_num)
  let modelD := cylinderEuclideanConnection 0 (by norm_num)
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hjet (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
      Tendsto (fun n => iteratedFDeriv ℝ r (fun p : V => (G n).inner p (b i) (b j)) 0)
        atTop (𝓝 (iteratedFDeriv ℝ r (fun p : V => model.inner p (b i) (b j)) 0)) := by
    let J (h : RiemannianMetric 3 V) :=
      iteratedFDeriv ℝ r (fun p : V => h.inner p (b i) (b j)) 0
    have herr : Tendsto (fun n => J (G n) - J model) atTop (𝓝 0) := by
      apply tendsto_cylinder_jet_of_components
      intro a
      have hbound (n : ℕ) :
          ‖(J (G n) - J model) (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))‖ ≤
            52 * epsilon n := by
        have hr' : (r : ℕ∞ω) ≤ ∞ := by norm_cast; exact le_top
        have hsub := iteratedFDeriv_sub_apply
          ((metric_component_contDiffAt (G n) 0 (b i) (b j)).of_le hr')
          ((metric_component_contDiffAt model 0 (b i) (b j)).of_le hr')
        have hh := (hclose n).euclidean_metric_error_component_abs_lt_shift
          (he n) (by norm_num) (by norm_num) (q n) (s n) (hs n) (hk n)
          (G n) i j (hG n i j) hr a
        have heq := congrArg
          (fun A => A (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) hsub
        exact (congrArg abs heq).symm.trans_le hh.le
      exact squeeze_zero_norm hbound (by simpa only [mul_zero] using hezero.const_mul 52)
    simpa only [sub_add_cancel, zero_add] using herr.add
      (tendsto_const_nhds (x := J model))
  have hricci (i : Fin 3) : Tendsto (fun n => (DG n).ricci 0 (b i) (b i)) atTop
      (𝓝 (modelD.ricci 0 (b i) (b i))) :=
    LeviCivitaData.tendsto_ricci_of_scalar_metric_jets DG modelD 0 (b i) (b i) b hjet
  have hmetric (i : Fin 3) : Tendsto (fun n => (G n).inner 0 (b i) (b i)) atTop
      (𝓝 (model.inner 0 (b i) (b i))) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V ℝ).continuous.tendsto _).comp
      (hjet 0 (by omega) i i)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hangular : modelD.ricci 0 (b 0) (b 0) = 1 := by
    have h := cylinder_ricci_center 0 (by norm_num) modelD (q 0) 0 0 0
    norm_num [roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left] at h
    rw [show cylinderCoordinateEquiv.symm ((0, 0) : RoundCylinderCoordinates) = 0
      from map_zero cylinderCoordinateEquiv.symm] at h
    simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using h
  have haxial : modelD.ricci 0 (b 2) (b 2) = 0 := by
    have h := cylinder_ricci_center 0 (by norm_num) modelD (q 0) 0 2 2
    change modelD.ricci (cylinderCoordinateEquiv.symm (0, 0)) (b 2) (b 2) =
      inner ℝ (0 : EuclideanSpace ℝ (Fin 2)) 0 at h
    rw [show cylinderCoordinateEquiv.symm ((0, 0) : RoundCylinderCoordinates) = 0
      from map_zero cylinderCoordinateEquiv.symm, inner_zero_left] at h
    exact h
  have haxialmetric : model.inner 0 (b 2) (b 2) = 1 := by
    have h := cylinderEuclideanMetric_inner_basis 0 (by norm_num) 0
      (EuclideanSpace.basisFun (Fin 3) ℝ 2) 2
    norm_num [EuclideanSpace.basisFun_apply, EuclideanSpace.single] at h
    have htwo : ![(2 : ℝ), 2, 1] (2 : Fin 3) = 1 := rfl
    rw [htwo] at h
    simpa only [model, b, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single] using h
  have heq := tendsto_nhds_unique
    (((hricci 0).mul (hmetric 2)).congr (fun n => hisotropic n (b 0) (b 2)))
    ((hricci 2).mul (hmetric 0))
  rw [hangular, haxial, haxialmetric] at heq
  norm_num at heq

end PoincareConjecture.M35
