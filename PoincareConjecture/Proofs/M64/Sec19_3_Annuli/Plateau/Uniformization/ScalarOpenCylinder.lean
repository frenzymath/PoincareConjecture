import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarInverseConformal
import PoincareConjecture.Proofs.M01.ConnectionExistence
import PoincareConjecture.Definitions.M64Annulus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

def scalarCylinderCoordinate : Plane →L[ℝ] Cover :=
  (EuclideanSpace.proj 1).prod (curvePeriod⁻¹ • EuclideanSpace.proj 0)

theorem scalarCylinderCoordinate_apply (p : Plane) :
    scalarCylinderCoordinate p = (p 1, curvePeriod⁻¹ * p 0) := rfl

private theorem scalarCurvePeriod_pos : 0 < curvePeriod := by
  unfold curvePeriod
  positivity

theorem scalarCylinderCoordinate_injective : Function.Injective scalarCylinderCoordinate := by
  intro v w hvw
  have h0 := congrArg Prod.snd hvw
  have h1 := congrArg Prod.fst hvw
  change curvePeriod⁻¹ * v 0 = curvePeriod⁻¹ * w 0 at h0
  change v 1 = w 1 at h1
  ext i
  fin_cases i
  · exact mul_left_cancel₀ (inv_ne_zero scalarCurvePeriod_pos.ne') h0
  · exact h1

theorem scalarCylinderCoordinate_periodic (x s : ℝ) :
    scalarCylinderCoordinate (annulusPoint (x + curvePeriod) s) =
      scalarCylinderCoordinate (annulusPoint x s) + (0, 1) := by
  simp only [scalarCylinderCoordinate_apply, annulusPoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.mk_add_mk, add_zero]
  congr 1
  rw [mul_add, inv_mul_cancel₀ scalarCurvePeriod_pos.ne']

theorem scalarCylinderCoordinate_right_inverse (y : Cover) :
    scalarCylinderCoordinate (annulusPoint (curvePeriod * y.2) y.1) = y := by
  simp only [scalarCylinderCoordinate_apply, annulusPoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, ← mul_assoc, inv_mul_cancel₀ scalarCurvePeriod_pos.ne', one_mul]

theorem exists_smooth_modulus_conformal_open_cylinder (g : RiemannianMetric 2 Plane) :
    ∃ (r : ℝ), 0 < r ∧ ∃ F : Plane → Plane,
      ContDiffOn ℝ ∞ F Strip ∧
      (∀ p ∈ Strip, F p ∈ scalarAnnulus) ∧
      SurjOn F Strip scalarAnnulus ∧
      (∀ x s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
        F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s)) ∧
      (∀ p ∈ Strip, Function.Injective (fderiv ℝ F p)) ∧
      ∀ p ∈ Strip,
        r * m60AreaGram g F p 0 0 = r⁻¹ * m60AreaGram g F p 1 1 ∧
          m60AreaGram g F p 0 1 = 0 := by
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  obtain ⟨H, V, P, e, -, hHs, -, -, -, hP, -, -, hdV,
    hsource, htarget, he, hes, hei, hdeck⟩ := exists_smooth_annular_cover_chart D
  let L := scalarCylinderCoordinate
  let F : Plane → Plane := scalarInverseCoverMap e ∘ L
  let r := curvePeriod / P
  have hLt {p : Plane} (hp : p ∈ Strip) : L p ∈ e.target := by
    rw [htarget]
    exact hp
  have hFd {p : Plane} (hp : p ∈ Strip) : fderiv ℝ F p =
      (fderiv ℝ (scalarInverseCoverMap e) (L p)).comp L := by
    simpa only [ContinuousLinearMap.fderiv] using fderiv_comp p
      (((scalarInverseCoverMap_smooth e hei).contDiffAt
        (e.open_target.mem_nhds (hLt hp))).differentiableAt (by simp)) L.differentiableAt
  have hFs : ContDiffOn ℝ ∞ F Strip := by
    intro p hp
    exact (((scalarInverseCoverMap_smooth e hei).contDiffAt
      (e.open_target.mem_nhds (hLt hp))).comp p L.contDiff.contDiffAt).contDiffWithinAt
  refine ⟨r, div_pos scalarCurvePeriod_pos hP, F, hFs, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    apply scalarCoverMap_mem
    rw [← hsource]
    exact e.map_target (hLt hp)
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjOn hx
    have hzs : z ∈ e.source := hsource ▸ hz
    have hzt : e z ∈ scalarPotentialStrip := htarget ▸ e.map_source hzs
    refine ⟨annulusPoint (curvePeriod * (e z).2) (e z).1, hzt, ?_⟩
    change scalarCoverMap (e.symm (scalarCylinderCoordinate
      (annulusPoint (curvePeriod * (e z).2) (e z).1))) = scalarCoverMap z
    rw [scalarCylinderCoordinate_right_inverse, e.left_inv hzs]
  · intro x s hs
    change scalarInverseCoverMap e (scalarCylinderCoordinate (annulusPoint (x + curvePeriod) s)) = _
    rw [scalarCylinderCoordinate_periodic]
    exact scalarInverseCoverMap_periodic e hsource htarget hdeck (hLt hs)
  · intro p hp
    rw [hFd hp]
    exact (scalarInverseCoverMap_fderiv_injective D hHs hdV P e hsource he hes hei
      (hLt hp)).comp scalarCylinderCoordinate_injective
  · intro p hp
    let E := g.inner (F p) (D.gradient H (F p)) (D.gradient H (F p))
    have hmetric (v w : Plane) :
        E * g.inner (F p) (fderiv ℝ F p v) (fderiv ℝ F p w) =
          (L v).1 * (L w).1 + P ^ 2 * (L v).2 * (L w).2 := by
      rw [hFd hp]
      exact scalarInverseCoverMap_metric_identity D hHs hdV hP.ne' e hsource he hes hei
        (hLt hp) (L v) (L w)
    let b := EuclideanSpace.basisFun (Fin 2) ℝ
    have hgram (i j : Fin 2) : m60AreaGram g F p i j =
        g.inner (F p) (fderiv ℝ F p (b i)) (fderiv ℝ F p (b j)) := by
      unfold m60AreaGram
      rw [mfderiv_eq_fderiv]
      rfl
    have h00 : E * m60AreaGram g F p 0 0 = P ^ 2 * curvePeriod⁻¹ * curvePeriod⁻¹ := by
      rw [hgram]
      simpa [L, scalarCylinderCoordinate_apply, b, EuclideanSpace.basisFun_apply]
        using hmetric (b 0) (b 0)
    have h11 : E * m60AreaGram g F p 1 1 = 1 := by
      rw [hgram]
      simpa [L, scalarCylinderCoordinate_apply, b, EuclideanSpace.basisFun_apply]
        using hmetric (b 1) (b 1)
    have h01 : E * m60AreaGram g F p 0 1 = 0 := by
      rw [hgram]
      simpa [L, scalarCylinderCoordinate_apply, b, EuclideanSpace.basisFun_apply]
        using hmetric (b 0) (b 1)
    have hE : E ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at h11
      exact zero_ne_one h11
    constructor
    · apply mul_left_cancel₀ hE
      have hbalance : r * (P ^ 2 * curvePeriod⁻¹ * curvePeriod⁻¹) = r⁻¹ := by
        dsimp [r]
        field_simp [hP.ne', scalarCurvePeriod_pos.ne']
      calc
        E * (r * m60AreaGram g F p 0 0) = r * (E * m60AreaGram g F p 0 0) := by ring
        _ = r * (P ^ 2 * curvePeriod⁻¹ * curvePeriod⁻¹) := by rw [h00]
        _ = r⁻¹ := hbalance
        _ = E * (r⁻¹ * m60AreaGram g F p 1 1) := by
          rw [mul_left_comm E, h11, mul_one]
    · exact (mul_eq_zero.mp h01).resolve_left hE

end PoincareConjecture.M64Uniformization
