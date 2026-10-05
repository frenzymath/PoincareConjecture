import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Locality of the round-cylinder metric comparison

Tensor fields that agree on the open axial strip have the same coordinate
coefficients and covariant jets there. Consequently they satisfy the same
frozen `RoundCylinderClose` condition, independently of their values outside
the strip. This lets a lifted neck retain its original metric comparison.

Reference: Morgan--Tian, Definition 2.18, p. 31, and corrected Lemma A.20,
p. 508.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT

variable {ε : ℝ} {B C : RoundCylinderTwoTensor}

/-- Equality of tensors on the axial strip gives coefficient equality for
every sphere chart, including points outside its target. -/
theorem roundCylinderTensorCoefficient_eq_of_eqOn_strip
    (hBC : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      ∀ v w, B z v w = C z v w)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (hp : p.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (a b : Fin 3) :
    roundCylinderTensorCoefficient B c p a b =
      roundCylinderTensorCoefficient C c p a b :=
  hBC (c.symm p.1, p.2) hp _ _

/-- Every covariant derivative agrees at every interior axial point when
the tensor fields agree on the strip. -/
theorem roundCylinderIteratedDerivative_eq_of_eqOn_strip
    (hBC : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      ∀ v w, B z v w = C z v w)
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) (p : RoundCylinderCoordinates) (hp : p.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    roundCylinderIteratedDerivative u c B k p =
      roundCylinderIteratedDerivative u c C k p := by
  induction k generalizing p with
  | zero =>
    funext a
    simp only [roundCylinderIteratedDerivative,
      roundCylinderTensorCoefficient_eq_of_eqOn_strip hBC c p hp]
  | succ k ih =>
    funext a
    have heq :
        (fun q => roundCylinderIteratedDerivative u c B k q (fun i => a i.succ))
          =ᶠ[𝓝 p]
        (fun q => roundCylinderIteratedDerivative u c C k q (fun i => a i.succ)) := by
      filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds hp] with q hq
      exact congr_fun (ih q hq) _
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    erw [heq.fderiv_eq (𝕜 := ℝ)]
    rw [ih p hp]
    rfl

/-- The full finite-order jet error is unchanged by altering the tensor
outside the open axial strip. -/
theorem roundCylinderJetErrorSquared_eq_of_eqOn_strip
    (hBC : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      ∀ v w, B z v w = C z v w)
    (u : ℝ) (order : ℕ) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    roundCylinderJetErrorSquared u B order z =
      roundCylinderJetErrorSquared u C order z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_congr rfl
  intro k hk
  rw [roundCylinderIteratedDerivative_eq_of_eqOn_strip hBC u _ k _ hz]

/-- Smoothness of the tensor coefficients only depends on the tensor on
the open axial strip. -/
theorem roundCylinderTensorSmoothOn_congr
    (hBC : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      ∀ v w, B z v w = C z v w) :
    RoundCylinderTensorSmoothOn ε B ↔ RoundCylinderTensorSmoothOn ε C := by
  constructor
  · intro h q a b
    apply (h q a b).congr
    intro p hp
    exact (roundCylinderTensorCoefficient_eq_of_eqOn_strip hBC _ p hp.2 a b).symm
  · intro h q a b
    apply (h q a b).congr
    intro p hp
    exact roundCylinderTensorCoefficient_eq_of_eqOn_strip hBC _ p hp.2 a b

/-- Equality on the open axial strip preserves the exact frozen neck
comparison, including its original uniform bound and every retained jet. -/
theorem roundCylinderClose_congr
    (hBC : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      ∀ v w, B z v w = C z v w)
    (u : ℝ) : RoundCylinderClose ε u B ↔ RoundCylinderClose ε u C := by
  constructor
  · rintro ⟨hsmooth, bound, hbound, hjet⟩
    refine ⟨(roundCylinderTensorSmoothOn_congr hBC).mp hsmooth, bound, hbound, ?_⟩
    intro z hz
    rw [← roundCylinderJetErrorSquared_eq_of_eqOn_strip hBC u _ z hz]
    exact hjet z hz
  · rintro ⟨hsmooth, bound, hbound, hjet⟩
    refine ⟨(roundCylinderTensorSmoothOn_congr hBC).mpr hsmooth, bound, hbound, ?_⟩
    intro z hz
    rw [roundCylinderJetErrorSquared_eq_of_eqOn_strip hBC u _ z hz]
    exact hjet z hz

end PoincareMT
