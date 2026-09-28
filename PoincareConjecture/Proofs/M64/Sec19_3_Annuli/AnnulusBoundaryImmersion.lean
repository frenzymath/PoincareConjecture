import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSliceDifferential











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem m64Annulus_energyDensity_pos_of_horizontal_immersed
    (g : RiemannianMetric n M) {f : LoopPlane → M} {x s : ℝ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (annulusPoint x s))
    (himm : curveVelocity (n := n) (fun y => f (annulusPoint y s)) x ≠ 0) :
    0 < m60EnergyDensity g f (annulusPoint x s) := by
  let u0 := mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let u1 := mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
    (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have hvel : curveVelocity (n := n) (fun y => f (annulusPoint y s)) x = u0 := by
    simpa only [u0, EuclideanSpace.basisFun_apply] using m64Annulus_horizontal_velocity hf
  have hu0 : u0 ≠ 0 := fun h => himm (hvel.trans h)
  have hpos := g.pos (f (annulusPoint x s)) u0 hu0
  have hnonneg : 0 ≤ g.inner (f (annulusPoint x s)) u1 u1 := by
    by_cases h : u1 = 0
    · simp [h]
    · exact (g.pos _ _ h).le
  simp only [m60EnergyDensity, Matrix.trace, Fin.sum_univ_two, m60AreaGram]
  change 0 < (1 / 2 : ℝ) *
    (g.inner (f (annulusPoint x s)) u0 u0 + g.inner (f (annulusPoint x s)) u1 u1)
  linarith

end PoincareConjecture
