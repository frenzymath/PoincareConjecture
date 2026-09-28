import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneFirstVariation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskDivergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def m65PlaneFluxVector (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) (t : ℝ) (z : LoopPlane) : LoopPlane :=
  !₂[m65PlaneVariationFlux g u t 0 z, m65PlaneVariationFlux g u t 1 z]

theorem m65PlaneVariationFlux_contDiffAt (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) {t : ℝ} {z : LoopPlane}
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) (t, z))
    (i : Fin 2) : ContDiffAt ℝ 1 (m65PlaneVariationFlux g u t i) z := by
  have hf : ContMDiffAt (𝓡 2) (𝓡 n) ∞ (u t) z :=
    hu.comp z (contMDiffAt_const.prodMk contMDiffAt_id)
  have hV := m65PlaneTimeVelocity_contMDiffAt u (hu.of_le (by decide))
  have he := (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf
    (EuclideanSpace.basisFun (Fin 2) ℝ i)).of_le (show (1 : WithTop ℕ∞) ≤ ∞ from by simp)
  have hg := ((g.contMDiff (u t z)).of_le (show (1 : WithTop ℕ∞) ≤ ∞ from by simp)).comp z
    (hf.of_le (by simp))
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hV he
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', EuclideanSpace.basisFun_apply,
    Bundle.Trivial.trivialization_apply] at hh
  convert! contMDiffAt_iff_contDiffAt.mp hh using 1
  funext w
  dsimp only [m65PlaneVariationFlux]
  rw [EuclideanSpace.basisFun_apply]

theorem m65PlaneFluxVector_contDiffAt (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) {t : ℝ} {z : LoopPlane}
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) (t, z)) :
    ContDiffAt ℝ 1 (m65PlaneFluxVector g u t) z := by
  apply contDiffAt_euclidean.mpr
  intro i
  fin_cases i
  · exact m65PlaneVariationFlux_contDiffAt g u hu 0
  · exact m65PlaneVariationFlux_contDiffAt g u hu 1

theorem m65PlaneFluxVector_inner (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) (t : ℝ) (z w : LoopPlane) :
    inner ℝ (m65PlaneFluxVector g u t z) w =
      g.inner (u t z) (curveVelocity (fun s => u s z) t)
        (mfderiv (𝓡 2) (𝓡 n) (u t) z w) := by
  have hw : w = w 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      w 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.single]
  nth_rw 1 [hw]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    EuclideanSpace.inner_basisFun_real, EuclideanSpace.inner_basisFun_real]
  nth_rw 3 [hw]
  simp only [map_add, map_smul, m65PlaneFluxVector, m65PlaneVariationFlux,
    smul_eq_mul, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

end PoincareConjecture
