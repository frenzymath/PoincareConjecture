import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.SpectralTranslation
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Real.PeriodicJets

/-!
# Translation of the actual real spectral state

Realification conjugates the complex phase action without losing
either coordinate. MT2007 Claim 19.1, p. 437;
`2026-09-21-real-vector-spectral-translation.md`, statements 1-5.
-/

set_option autoImplicit false

open PoincareMT.SpectralHeatNative

namespace PoincareMT.M63

variable {L : ℝ}

/-- The literal realification of the complex phase action. MT2007
Claim 19.1, p. 437; real/vector spectral-translation derivation,
statement 1. No positive-period premise is needed for the action. -/
noncomputable def realPeriodicSpectralTranslation (a : ℝ) :
    State (ℤ × Fin 2) →L[ℝ] State (ℤ × Fin 2) :=
  complexLpRealEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((periodicSpectralTranslation (L := L) a).restrictScalars ℝ).comp
      complexLpRealEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Inverse realification recovers the exact complex phase action,
and the full real state norm is preserved. MT2007 Claim 19.1,
p. 437; real/vector spectral-translation derivation, statement 2. -/
theorem realPeriodicSpectralTranslation_spec (a : ℝ) (u : State (ℤ × Fin 2)) :
    complexLpRealEquiv.symm (realPeriodicSpectralTranslation (L := L) a u) =
      periodicSpectralTranslation (L := L) a (complexLpRealEquiv.symm u) ∧
      ‖realPeriodicSpectralTranslation (L := L) a u‖ = ‖u‖ := by
  constructor
  · exact complexLpRealEquiv.symm_apply_apply _
  · change ‖complexLpRealEquiv
      (periodicSpectralTranslation (L := L) a (complexLpRealEquiv.symm u))‖ = ‖u‖
    rw [complexLpRealEquiv.norm_map, (periodicSpectralTranslation_spec a _).2,
      complexLpRealEquiv.symm.norm_map]

/-- Real spectral translation is jointly strongly continuous in its
parameter and state. MT2007 Claim 19.1, p. 437;
real/vector spectral-translation derivation, statement 3. -/
theorem continuous_realPeriodicSpectralTranslation :
    Continuous (fun p : ℝ × State (ℤ × Fin 2) =>
      realPeriodicSpectralTranslation (L := L) p.1 p.2) := by
  let e := complexLpRealEquiv (ι := ℤ)
  have harg : Continuous (fun p : ℝ × State (ℤ × Fin 2) => (p.1, e.symm p.2)) :=
    continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  have hc := (continuous_periodicSpectralTranslation (L := L)).comp harg
  exact e.continuous.comp hc

/-- Real weights common to each real/imaginary pair commute with
translation when both weighted states exist. No boundedness of the
weight is inferred. MT2007 Claim 19.1, p. 437; real/vector
spectral-translation derivation, statement 4. -/
theorem realPeriodicSpectralTranslation_real_weight (m : ℤ → ℝ)
    (u v : State (ℤ × Fin 2)) (h : ∀ p, v p = m p.1 * u p) (a : ℝ) :
    ∀ p, realPeriodicSpectralTranslation (L := L) a v p =
      m p.1 * realPeriodicSpectralTranslation (L := L) a u p := by
  have hc : ∀ n, complexLpRealEquiv.symm v n =
      (m n : ℂ) * complexLpRealEquiv.symm u n := by
    apply (complexLpRealEquiv_real_weight_iff m (complexLpRealEquiv.symm u)
      (complexLpRealEquiv.symm v)).mpr
    simpa only [complexLpRealEquiv.apply_symm_apply] using h
  change ∀ p, complexLpRealEquiv
      (periodicSpectralTranslation (L := L) a (complexLpRealEquiv.symm v)) p =
    m p.1 * complexLpRealEquiv
      (periodicSpectralTranslation (L := L) a (complexLpRealEquiv.symm u)) p
  apply (complexLpRealEquiv_real_weight_iff m _ _).mp
  intro n
  change fourier n (-(a : AddCircle L)) * complexLpRealEquiv.symm v n =
    (m n : ℂ) * (fourier n (-(a : AddCircle L)) * complexLpRealEquiv.symm u n)
  rw [hc n]
  ring

/-- Every permitted actual real periodic jet is translated by the
real spectral action. MT2007 Claim 19.1, p. 437;
real/vector spectral-translation derivation, statement 5. -/
theorem realPeriodicJet_spectralTranslation [Fact (0 < L)]
    (k j : ℕ) (hj : j ≤ k) (u : State (ℤ × Fin 2)) (a : ℝ) :
    realPeriodicJet (L := L) k j hj (realPeriodicSpectralTranslation (L := L) a u) =
      periodicTranslation a (realPeriodicJet (L := L) k j hj u) := by
  ext x
  change (periodicSobolevJet (L := L) k j hj
    (complexLpRealEquiv.symm (realPeriodicSpectralTranslation (L := L) a u)) x).re =
      (periodicSobolevJet (L := L) k j hj
        (complexLpRealEquiv.symm u) (x - (a : AddCircle L))).re
  rw [(realPeriodicSpectralTranslation_spec a u).1,
    periodicSobolevJet_periodicSpectralTranslation]
  rfl

end PoincareMT.M63
