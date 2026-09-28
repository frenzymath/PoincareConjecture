import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.GramRank
import PoincareConjecture.Proofs.M60.Mathlib.GramDeterminantDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereDensity_variation {J : Set ℝ} (F : RicciFlow n M J)
    (f : UnitTwoSphere → M) (z : LoopPlane) {t : ℝ} (ht : t ∈ J) :
    HasDerivWithinAt (fun s => m60SphereAreaDensity (F.metric s) f z)
      (-m60SphereRicciTraceDensity (F.connection t) f z) J t := by
  by_cases hdeg : Matrix.det (m60AreaGram (F.metric t) (f ∘ m60SphereParameter) z) = 0
  · exact m60SphereDensity_variation_of_degenerate F f z t hdeg
  let G := fun s => m60AreaGram (F.metric s) (f ∘ m60SphereParameter) z
  let e := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 n) (f ∘ m60SphereParameter) z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let R : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => (F.connection t).ricci ((f ∘ m60SphereParameter) z) (e i) (e j)
  have hG : ∀ i j, HasDerivWithinAt (fun s => G s i j) (-2 * R i j) J t :=
    fun i j => F.equation t ht ((f ∘ m60SphereParameter) z) (e i) (e j)
  have hnonneg (s : ℝ) : 0 ≤ Matrix.det (G s) :=
    m60AreaGram_det_nonneg (F.metric s) (f ∘ m60SphereParameter) z
  have hpos : 0 < Matrix.det (G t) := lt_of_le_of_ne (hnonneg t) (Ne.symm hdeg)
  have hd := M60.hasDerivWithinAt_sqrt_det_fin_two hG hpos
  have harea : (fun s => Real.sqrt (Matrix.det (G s))) =
      fun s => m60SphereAreaDensity (F.metric s) f z := by
    funext s
    exact congrArg Real.sqrt (max_eq_right (hnonneg s)).symm
  rw [harea] at hd
  convert hd using 1
  unfold m60SphereRicciTraceDensity
  rw [if_neg hdeg]
  unfold m60AreaDensity
  rw [max_eq_right (hnonneg t)]
  simp only [Fin.sum_univ_two]
  dsimp only [G, R, e]
  ring

end PoincareConjecture
