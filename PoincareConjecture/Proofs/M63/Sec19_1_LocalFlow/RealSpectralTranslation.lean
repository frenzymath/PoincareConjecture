import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSpectralTranslation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.RealPeriodicJets









set_option autoImplicit false

open PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ}




noncomputable def realPeriodicSpectralTranslation (a : ℝ) :
    State (ℤ × Fin 2) →L[ℝ] State (ℤ × Fin 2) :=
  complexLpRealEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((periodicSpectralTranslation (L := L) a).restrictScalars ℝ).comp
      complexLpRealEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)




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




theorem continuous_realPeriodicSpectralTranslation :
    Continuous (fun p : ℝ × State (ℤ × Fin 2) =>
      realPeriodicSpectralTranslation (L := L) p.1 p.2) := by
  let e := complexLpRealEquiv (ι := ℤ)
  have harg : Continuous (fun p : ℝ × State (ℤ × Fin 2) => (p.1, e.symm p.2)) :=
    continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  have hc := (continuous_periodicSpectralTranslation (L := L)).comp harg
  exact e.continuous.comp hc





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

end PoincareConjecture.M63
