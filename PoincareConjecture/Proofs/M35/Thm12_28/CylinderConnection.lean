import PoincareConjecture.Proofs.M35.Thm12_28.SphereCoordinates
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetNorm

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

theorem fderiv_roundCylinderGram_apply (u : ℝ) (q : UnitTwoSphere)
    (p v : RoundCylinderCoordinates) (a b : Fin 3) :
    fderiv ℝ (fun p : RoundCylinderCoordinates =>
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) p v =
      (-128 * (1 - u) / (‖p.1‖ ^ 2 + 4) ^ 3) * inner ℝ p.1 v.1 *
        inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 := by
  have h := (((hasFDerivAt_stereographicMetricFactor (32 * (1 - u)) p.1).comp
    p hasFDerivAt_fst).mul_const
      (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1)).add_const
        ((roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2)
  simp_rw [roundCylinderGram_apply]
  convert! congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ => L v) h.fderiv using 1
  simp
  ring

theorem hasFDerivAt_roundCylinderGram_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) (a b : Fin 3) :
    HasFDerivAt (𝕜 := ℝ) (fun p : RoundCylinderCoordinates =>
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)
      0 (0, s) := by
  have hfactor : HasFDerivAt (𝕜 := ℝ) (fun p : RoundCylinderCoordinates =>
      32 * (1 - u) / (‖p.1‖ ^ 2 + 4) ^ 2) 0 (0, s) := by
    have hf : HasFDerivAt (𝕜 := ℝ) (Prod.fst : RoundCylinderCoordinates →
        EuclideanSpace ℝ (Fin 2))
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) (0, s) :=
      hasFDerivAt_fst
    convert! (hasFDerivAt_stereographicMetricFactor (32 * (1 - u))
      (0 : EuclideanSpace ℝ (Fin 2))).comp ((0, s) : RoundCylinderCoordinates) hf using 1
    simp
  simp_rw [roundCylinderGram_eq]
  fin_cases a <;> fin_cases b <;> simp only [Matrix.diagonal] <;>
    first | exact hfactor | exact hasFDerivAt_const _ _

theorem roundCylinderChristoffel_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) (a b d : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (0, s) a b d = 0 := by
  unfold roundCylinderChristoffel
  simp only [(hasFDerivAt_roundCylinderGram_center u q s _ _).fderiv]
  simp

theorem roundCylinderTensorDerivative_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) {r : ℕ} (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      T (0, s) a =
      fderiv ℝ (fun p => T p (fun i => a i.succ)) (0, s)
        (roundCylinderCoordinateBasis (a 0)) := by
  simp [roundCylinderTensorDerivative, roundCylinderChristoffel_center]

theorem roundCylinderIteratedDerivative_one_center (u : ℝ) (q : UnitTwoSphere)
    (s : ℝ) (B : RoundCylinderTwoTensor) (a : Fin 3 → Fin 3)
    (hB : DifferentiableAt ℝ (fun p : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        p (a 1) (a 2)) (0, s)) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      B 1 (0, s) a =
      fderiv ℝ (fun p : RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          p (a 1) (a 2)) (0, s) (roundCylinderCoordinateBasis (a 0)) := by
  rw [roundCylinderIteratedDerivative, roundCylinderTensorDerivative_center]
  change fderiv ℝ (fun p : RoundCylinderCoordinates =>
    roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      p (a 1) (a 2) -
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2))
    (0, s) _ = _
  have h := hB.hasFDerivAt.sub (hasFDerivAt_roundCylinderGram_center u q s (a 1) (a 2))
  have he := congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
    L (roundCylinderCoordinateBasis (a 0))) h.fderiv
  simp only [sub_zero] at he
  convert! he using 1

end PoincareConjecture.M35
