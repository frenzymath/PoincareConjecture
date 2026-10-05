import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.PlaneFirstVariation
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Disk.Divergence

/-!
# Regularity and boundary meaning of the actual velocity flux

The Euclidean flux vector packages the two genuine Riemannian pairings.
Its regularity follows from joint smoothness of the variation, and its
radial pairing is exactly the parameter-disk conormal pairing.
Source: Morgan--Tian Lemma 19.2, p. 438; M65 derivation 24, seventh stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual parameter-disk velocity flux vector. Source: MT Lemma 19.2,
p. 438; M65 derivation 24, seventh stage. -/
noncomputable def m65PlaneFluxVector (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) (t : ℝ) (z : LoopPlane) : LoopPlane :=
  !₂[m65PlaneVariationFlux g u t 0 z, m65PlaneVariationFlux g u t 1 z]

/-- Each actual flux component is C1 for a joint smooth variation.
Source: MT Lemma 19.2, p. 438; M65 derivation 24, seventh stage. -/
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

/-- The genuine flux vector is C1 near a smooth variation point.
Source: MT Lemma 19.2, p. 438; M65 derivation 24, seventh stage. -/
theorem m65PlaneFluxVector_contDiffAt (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) {t : ℝ} {z : LoopPlane}
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) (t, z)) :
    ContDiffAt ℝ 1 (m65PlaneFluxVector g u t) z := by
  apply contDiffAt_euclidean.mpr
  intro i
  fin_cases i
  · exact m65PlaneVariationFlux_contDiffAt g u hu 0
  · exact m65PlaneVariationFlux_contDiffAt g u hu 1

/-- Pairing the flux with any parameter vector is the actual Riemannian
pairing with its image under the disk derivative. Source: MT Lemma 19.2,
p. 438; M65 derivation 24, seventh stage. -/
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

end PoincareMT
