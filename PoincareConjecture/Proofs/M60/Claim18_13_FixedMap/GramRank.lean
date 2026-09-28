import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60AreaGram_det_ne_zero_iff (g : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane) :
    Matrix.det (m60AreaGram g F z) ≠ 0 ↔
      LinearIndependent ℝ (fun i : Fin 2 =>
        mfderiv (𝓡 2) (𝓡 n) F z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
    (v := fun i : Fin 2 =>
      mfderiv (𝓡 2) (𝓡 n) F z (EuclideanSpace.basisFun (Fin 2) ℝ i))

theorem m60AreaGram_det_eq_zero_iff (g h : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane) :
    Matrix.det (m60AreaGram g F z) = 0 ↔ Matrix.det (m60AreaGram h F z) = 0 := by
  exact not_iff_not.mp
    ((m60AreaGram_det_ne_zero_iff g F z).trans (m60AreaGram_det_ne_zero_iff h F z).symm)

theorem m60AreaDensity_eq_zero_of_det_eq_zero (g h : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane) (hz : Matrix.det (m60AreaGram g F z) = 0) :
    m60AreaDensity h F z = 0 := by
  simp only [m60AreaDensity, (m60AreaGram_det_eq_zero_iff g h F z).mp hz,
    max_self, Real.sqrt_zero]

theorem m60SphereRicciTraceDensity_eq_zero {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : UnitTwoSphere → M) (z : LoopPlane)
    (hz : Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z) = 0) :
    m60SphereRicciTraceDensity D f z = 0 := by
  simp only [m60SphereRicciTraceDensity, hz, if_true]

theorem m60SphereDensity_variation_of_degenerate {J : Set ℝ}
    (F : RicciFlow n M J) (f : UnitTwoSphere → M) (z : LoopPlane) (t : ℝ)
    (hz : Matrix.det (m60AreaGram (F.metric t) (f ∘ m60SphereParameter) z) = 0) :
    HasDerivWithinAt (fun s => m60SphereAreaDensity (F.metric s) f z)
      (-m60SphereRicciTraceDensity (F.connection t) f z) J t := by
  rw [m60SphereRicciTraceDensity_eq_zero (F.connection t) f z hz, neg_zero]
  have hzero : (fun s => m60SphereAreaDensity (F.metric s) f z) = fun _ => (0 : ℝ) := by
    funext s
    exact m60AreaDensity_eq_zero_of_det_eq_zero (F.metric t) (F.metric s)
      (f ∘ m60SphereParameter) z hz
  rw [hzero]
  exact hasDerivWithinAt_const _ _ _

end PoincareConjecture
