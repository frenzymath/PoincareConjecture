import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.DefectCoordinates
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.CovariantTestSlab








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem raw_inverseCoefficients_family_contDiffOn {J : Set ℝ}
    (F : RicciFlow n V J) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => (F.metric p.1).inverseCoefficients p.2 i j)
      (J ×ˢ univ) := by
  intro p hp
  have hi := ((F.metric p.1).inner_isInvertible p.2).contDiffAt_map_inverse.comp_contDiffWithinAt p
    (rawMetricBilin_family_contDiffOn F p hp)
  exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp_contDiffWithinAt p
    (hi.clm_apply (contDiffWithinAt_const (c := EuclideanSpace.proj (𝕜 := ℝ) i)))

def defectTestCoefficient (g : RiemannianMetric n V) (φ : V → ℝ)
    (k l i j : Fin n) (x : V) : ℝ :=
  φ x * g.inverseCoefficients x k l * g.inverseCoefficients x i j

theorem defectTestCoefficient_contDiff (g : RiemannianMetric n V)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (k l i j : Fin n) :
    ContDiff ℝ ∞ (defectTestCoefficient g φ k l i j) :=
  (hφ.mul (g.contDiff_inverseCoefficients k l)).mul (g.contDiff_inverseCoefficients i j)

theorem defectTestCoefficient_family_contDiffOn {J : Set ℝ}
    (F : RicciFlow n V J) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (k l i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => defectTestCoefficient (F.metric p.1) φ k l i j p.2)
      (J ×ˢ univ) :=
  ((hφ.comp contDiff_snd).contDiffOn.mul (raw_inverseCoefficients_family_contDiffOn F k l)).mul
    (raw_inverseCoefficients_family_contDiffOn F i j)

theorem defectTestCoefficient_zero_off (g : RiemannianMetric n V)
    (φ : V → ℝ) (k l i j : Fin n) {x : V} (hx : x ∉ tsupport φ) :
    defectTestCoefficient g φ k l i j x = 0 := by
  simp only [defectTestCoefficient, image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem defectTestCoefficient_hasCompactSupport (g : RiemannianMetric n V)
    {φ : V → ℝ} (hφ : HasCompactSupport φ) (k l i j : Fin n) :
    HasCompactSupport (defectTestCoefficient g φ k l i j) := hφ.mul_right.mul_right

end PoincareConjecture.M35.Uniqueness.Heat
