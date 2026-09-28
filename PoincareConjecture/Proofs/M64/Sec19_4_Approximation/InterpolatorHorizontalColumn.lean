import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorEndpointBound
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SampledPolygonSpeed
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem m64_interpolator_horizontal_column_eq
    {gamma beta : ℝ → M} {H : ℝ × (M × M) → M} (x : LoopPlane)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma (x 0))
    (hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) beta (x 0))
    (hH : MDifferentiableAt
      (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
        (x 1, gamma (x 0), beta (x 0))) :
    mfderiv (𝓡 2) (𝓡 n)
        (fun p : LoopPlane => H (p 1, gamma (p 0), beta (p 0))) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
        (x 1, gamma (x 0), beta (x 0))
        (0, curveVelocity gamma (x 0), curveVelocity beta (x 0)) := by
  have hp0 : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : LoopPlane => p 0) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞) |>.contMDiff.contMDiffAt |>.mdifferentiableAt (by simp)
  have hp1 : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : LoopPlane => p 1) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff
      (n := ∞) |>.contMDiff.contMDiffAt |>.mdifferentiableAt (by simp)
  let b := EuclideanSpace.basisFun (Fin 2) ℝ 0
  have hb0 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : LoopPlane => p 0) x b = 1 := by
    rw [mfderiv_eq_fderiv]
    have hd : fderiv ℝ (fun p : LoopPlane => p 0) x =
        (EuclideanSpace.proj 0 : LoopPlane →L[ℝ] ℝ) :=
      (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 0).fderiv
    rw [hd]
    change (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0 = 1
    simp [EuclideanSpace.basisFun_apply]
  have hb1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : LoopPlane => p 1) x b = 0 := by
    rw [mfderiv_eq_fderiv]
    have hd : fderiv ℝ (fun p : LoopPlane => p 1) x =
        (EuclideanSpace.proj 1 : LoopPlane →L[ℝ] ℝ) :=
      (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 1).fderiv
    rw [hd]
    change (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1 = 0
    simp [EuclideanSpace.basisFun_apply]
  have hgamma_b : mfderiv (𝓡 2) (𝓡 n)
      (fun p : LoopPlane => gamma (p 0)) x b = curveVelocity gamma (x 0) := by
    have hc := mfderiv_comp_apply x hgamma hp0 b
    rw [hb0] at hc
    simpa only [Function.comp_def, curveVelocity] using hc
  have hbeta_b : mfderiv (𝓡 2) (𝓡 n)
      (fun p : LoopPlane => beta (p 0)) x b = curveVelocity beta (x 0) := by
    have hc := mfderiv_comp_apply x hbeta hp0 b
    rw [hb0] at hc
    simpa only [Function.comp_def, curveVelocity] using hc
  let input : LoopPlane → ℝ × (M × M) := fun p =>
    (p 1, gamma (p 0), beta (p 0))
  have hinput : MDifferentiableAt (𝓡 2)
      (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) input x :=
    hp1.prodMk ((hgamma.comp x hp0).prodMk (hbeta.comp x hp0))
  have hbinput : mfderiv (𝓡 2)
      (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) input x b =
        (0, curveVelocity gamma (x 0), curveVelocity beta (x 0)) := by
    have hprod := mfderiv_prodMk hp1
      ((hgamma.comp x hp0).prodMk (hbeta.comp x hp0))
    have hev := congrArg (fun L => L b) hprod
    erw [mfderiv_prodMk (hgamma.comp x hp0) (hbeta.comp x hp0)] at hev
    change _ = ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : LoopPlane => p 1) x) b,
      ((mfderiv (𝓡 2) (𝓡 n) (fun p : LoopPlane => gamma (p 0)) x) b,
        (mfderiv (𝓡 2) (𝓡 n) (fun p : LoopPlane => beta (p 0)) x) b)) at hev
    simpa only [input, Function.comp_def, hb1, hgamma_b, hbeta_b] using hev
  have hc := mfderiv_comp_apply x hH hinput b
  rw [hbinput] at hc
  simpa only [Function.comp_def, input, b] using hc

theorem m64_translated_side_speed
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {ell left x : ℝ} {p q : M}
    (side : M63MinimizingGeodesicSide g D ell p q)
    (hx : x - left ∈ Icc (0 : ℝ) ell) :
    g.tangentNorm (side.map (x - left))
      (curveVelocity (fun y => side.map (y - left)) x) = side.speed := by
  have hside : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) side.map (x - left) :=
    (side.smooth.contMDiffAt
      (side.domain_open.mem_nhds (side.interval_subset hx))).mdifferentiableAt
        (by simp)
  rw [M63.curveVelocity_comp (phi := fun y : ℝ => y - left)
    (x := x) (v := 1) hside ((hasDerivAt_id x).sub_const left), one_smul]
  exact side.constant_speed (x - left) hx

end PoincareConjecture
