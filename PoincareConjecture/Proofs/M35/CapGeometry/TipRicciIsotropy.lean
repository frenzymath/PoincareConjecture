import PoincareConjecture.Proofs.M35.CapGeometry.RadialPointIdentification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single (2 : Fin 3) 1

variable {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include hrotation

private theorem tip_ricci_rotation
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (u v : StandardCapSpace) :
    D.ricci 0 (standardRotation A u) (standardRotation A v) = D.ricci 0 u v := by
  let F := standardRotationDiffeomorph A
  have hF : MetricHomothety g g F 1 := by
    intro y a b
    change g.inner (standardRotation A y)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y a)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y b) = _
    simpa only [one_mul] using hrotation A y a b
  have h := M13.homothety_ricci_eq g g F 1 zero_lt_one hF D D 0 u v
  let R (x a b : StandardCapSpace) := D.ricci x a b
  change R (standardRotation A 0)
    (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) 0 u)
    (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) 0 v) = R 0 u v at h
  rw [standardRotation_mfderiv] at h
  change R (Matrix.toEuclideanLin A.1 0)
    (standardRotation A u) (standardRotation A v) = R 0 u v at h
  rw [map_zero] at h
  exact h

private theorem tip_metric_rotation
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (u v : StandardCapSpace) :
    g.inner 0 (standardRotation A u) (standardRotation A v) = g.inner 0 u v := by
  have h := hrotation A 0 u v
  let B (x a b : StandardCapSpace) := g.inner x a b
  change B (standardRotation A 0)
    (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) 0 u)
    (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) 0 v) = B 0 u v at h
  rw [standardRotation_mfderiv] at h
  change B (Matrix.toEuclideanLin A.1 0)
    (standardRotation A u) (standardRotation A v) = B 0 u v at h
  rw [map_zero] at h
  exact h

theorem rotational_tip_ricci_diagonal (u v : StandardCapSpace) :
    D.ricci 0 u u * g.inner 0 v v = D.ricci 0 v v * g.inner 0 u u := by
  have hdiag (w : StandardCapSpace) :
      D.ricci 0 w w = ‖w‖ ^ 2 * D.ricci 0 e2 e2 ∧
        g.inner 0 w w = ‖w‖ ^ 2 * g.inner 0 e2 e2 := by
    obtain ⟨A, hA⟩ := exists_axis_rotation w
    have hR := tip_ricci_rotation D hrotation A (‖w‖ • e2) (‖w‖ • e2)
    have hG := tip_metric_rotation hrotation A (‖w‖ • e2) (‖w‖ • e2)
    rw [hA] at hR hG
    constructor
    · change M13.ricciLinear D 0 w w = _
      change M13.ricciLinear D 0 w w =
        M13.ricciLinear D 0 (‖w‖ • e2) (‖w‖ • e2) at hR
      rw [hR]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, M13.ricciLinear_apply]
      ring
    · rw [hG]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
  rw [(hdiag u).1, (hdiag v).1, (hdiag u).2, (hdiag v).2]
  ring

end PoincareConjecture.M35.Uniqueness
