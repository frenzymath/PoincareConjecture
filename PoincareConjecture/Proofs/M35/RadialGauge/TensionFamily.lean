import PoincareConjecture.Proofs.M35.RadialGauge.TensionContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.JointSuccessor











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem mapTension_family_joint_c1
    {g : ℝ → RiemannianMetric n V} (D : ∀ t, LeviCivitaData (g t))
    {b : RiemannianMetric n V} (B : LeviCivitaData b) {J : Set ℝ} {F : ℝ → V → V}
    (hΓ : ContDiffOn ℝ 1 (fun p : ℝ × V => rawConnectionCoefficient (D p.1) p.2)
      (J ×ˢ univ))
    (hInv : ∀ i j : Fin n, ContDiffOn ℝ 1
      (fun p : ℝ × V => (rawCoordinateGram (g p.1) p.2)⁻¹ i j) (J ×ˢ univ))
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) (J ×ˢ univ))
    (hDF : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (F p.1) p.2) (J ×ˢ univ))
    (hDDF : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (F p.1)) p.2)
      (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => mapTension (D p.1) B (F p.1) p.2) (J ×ˢ univ) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have he (i : Fin n) : e i = EuclideanSpace.single i (1 : ℝ) :=
    EuclideanSpace.basisFun_apply (Fin n) ℝ i
  have htrace (p : ℝ × V) : mapTension (D p.1) B (F p.1) p.2 = ∑ i, ∑ j,
      (rawCoordinateGram (g p.1) p.2)⁻¹ i j •
        mapCovariantHessian (D p.1) B (F p.1) p.2 (e i) (e j) := by
    rw [mapTension_eq_inverse_gram (D p.1) B (F p.1) p.2 e.toBasis]
    have hgram : Matrix.of (fun i j => (g p.1).inner p.2 (e.toBasis i) (e.toBasis j)) =
        rawCoordinateGram (g p.1) p.2 := by
      ext i j
      simp only [Matrix.of_apply, OrthonormalBasis.coe_toBasis, he, rawCoordinateGram]
    rw [hgram]
    rfl
  apply ContDiffOn.congr (f := fun p : ℝ × V => ∑ i, ∑ j,
    (rawCoordinateGram (g p.1) p.2)⁻¹ i j •
      mapCovariantHessian (D p.1) B (F p.1) p.2 (e i) (e j)) ?_ (fun p _ => htrace p)
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  apply (hInv i j).smul
  have h1 := (hDDF.clm_apply (contDiffOn_const (c := e i))).clm_apply
    (contDiffOn_const (c := e j))
  have hB : ContDiffOn ℝ 1
      (fun p : ℝ × V => rawConnectionCoefficient B (F p.1 p.2)) (J ×ˢ univ) :=
    ((rawConnectionCoefficient_contDiff B).of_le (by simp)).comp_contDiffOn hF
  have h2 := (hB.clm_apply (hDF.clm_apply (contDiffOn_const (c := e i)))).clm_apply
    (hDF.clm_apply (contDiffOn_const (c := e j)))
  have h3 := hDF.clm_apply ((hΓ.clm_apply (contDiffOn_const (c := e i))).clm_apply
    (contDiffOn_const (c := e j)))
  exact (h1.add h2).sub h3



theorem native_harmonic_map_joint_c2
    {g : ℝ → RiemannianMetric n V} (D : ∀ t, LeviCivitaData (g t))
    {b : RiemannianMetric n V} (B : LeviCivitaData b) {J : Set ℝ} (hJ : IsOpen J)
    {F : ℝ → V → V} (hs : ∀ t ∈ J, ContDiff ℝ ∞ (F t))
    (hΓ : ContDiffOn ℝ 1 (fun p : ℝ × V => rawConnectionCoefficient (D p.1) p.2)
      (J ×ˢ univ))
    (hInv : ∀ i j : Fin n, ContDiffOn ℝ 1
      (fun p : ℝ × V => (rawCoordinateGram (g p.1) p.2)⁻¹ i j) (J ×ˢ univ))
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) (J ×ˢ univ))
    (hDF : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (F p.1) p.2) (J ×ˢ univ))
    (hDDF : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (F p.1)) p.2)
      (J ×ˢ univ))
    (hPDE : ∀ t ∈ J, ∀ x, HasDerivAt (fun a => F a x) (mapTension (D t) B (F t) x) t) :
    ContDiffOn ℝ 2 (Function.uncurry F) (J ×ˢ univ) :=
  joint_contDiffOn_succ_of_partials hJ 1
    (fun t ht => (hs t ht).differentiable (by simp)) hPDE
    (mapTension_family_joint_c1 D B hΓ hInv hF hDF hDDF) hDF

end PoincareConjecture.M35.RadialGauge
