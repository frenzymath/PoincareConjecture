import PoincareConjecture.Proofs.M35.Uniqueness.RotationIntegration








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Matrix Topology

namespace PoincareConjecture.M35.Uniqueness

def coordinateRotation02 (s : ℝ) : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![Real.cos s, 0, -Real.sin s;
      0, 1, 0;
      Real.sin s, 0, Real.cos s], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
        nlinarith [Real.sin_sq_add_cos_sq s]
    · simp [Matrix.det_fin_three]
      nlinarith [Real.sin_sq_add_cos_sq s]⟩

def coordinateRotation02Generator : StandardCapSpace →L[ℝ] StandardCapSpace :=
  (Matrix.toEuclideanLin !![(0 : ℝ), 0, -1; 0, 0, 0; 1, 0, 0]).toContinuousLinearMap

theorem coordinateRotation02_zero : coordinateRotation02 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinateRotation02]

theorem coordinateRotation02_hasDerivAt_time (s : ℝ) (x : StandardCapSpace) :
    HasDerivAt (fun t => standardRotation (coordinateRotation02 t) x)
      (coordinateRotation02Generator (standardRotation (coordinateRotation02 s) x)) s := by
  let f : ℝ → Fin 3 → ℝ := fun t =>
    ![Real.cos t * x 0 - Real.sin t * x 2, x 1,
      Real.sin t * x 0 + Real.cos t * x 2]
  have hf : HasDerivAt f
      ![-Real.sin s * x 0 - Real.cos s * x 2, 0,
        Real.cos s * x 0 - Real.sin s * x 2] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((Real.hasDerivAt_cos s).mul_const (x 0)).sub
        ((Real.hasDerivAt_sin s).mul_const (x 2))
    · exact hasDerivAt_const s (x 1)
    · simpa [f, sub_eq_add_neg, neg_mul] using!
        ((Real.hasDerivAt_sin s).mul_const (x 0)).add
          ((Real.hasDerivAt_cos s).mul_const (x 2))
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hf
  convert! h using 1
  · funext t
    ext i
    fin_cases i <;> simp [standardRotation, coordinateRotation02, f, L,
      dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  · ext i
    fin_cases i <;> simp [coordinateRotation02Generator, standardRotation,
      coordinateRotation02, L, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_succ] <;> ring

theorem coordinateRotation02Generator_inner_zero (x : StandardCapSpace) :
    inner ℝ x (coordinateRotation02Generator x) = 0 := by
  simp [coordinateRotation02Generator, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ]
  ring

theorem initial_coordinateRotation02Generator_killing (g₀ : StandardInitialMetric)
    (x u v : StandardCapSpace) :
    DeTurckNative.metricLieDerivative g₀.connection
      (fun y => coordinateRotation02Generator y) x u v = 0 := by
  apply initial_rotation_path_killing g₀ coordinateRotation02 coordinateRotation02Generator
    coordinateRotation02_zero
  intro y
  simpa only [coordinateRotation02_zero, standardRotation_one] using
    coordinateRotation02_hasDerivAt_time 0 y

theorem coordinateRotation02_isometry_of_killing {g : RiemannianMetric 3 StandardCapSpace}
    (D : LeviCivitaData g)
    (hkill : ∀ x u v, DeTurckNative.metricLieDerivative D
      (fun y => coordinateRotation02Generator y) x u v = 0)
    (s : ℝ) (x u v : StandardCapSpace) :
    g.inner (standardRotation (coordinateRotation02 s) x)
      (standardRotation (coordinateRotation02 s) u) (standardRotation (coordinateRotation02 s) v) =
        g.inner x u v :=
  linear_killing_path_preserves_metric D coordinateRotation02Generator
    (fun t => standardRotation (coordinateRotation02 t))
    (fun x => by rw [coordinateRotation02_zero, standardRotation_one])
    coordinateRotation02_hasDerivAt_time hkill s x u v

end PoincareConjecture.M35.Uniqueness
