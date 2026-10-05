import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Real.SpectralTranslation
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Vector.PeriodicJets

/-!
# Translation of the actual finite-vector spectral state

The bounded finite split/join map assembles the scalar phase actions.
Its energy identity gives exact norm preservation. MT2007 Claim 19.1,
p. 437; `2026-09-21-real-vector-spectral-translation.md`, statements 6-11.
-/

set_option autoImplicit false

open PoincareMT.SpectralHeatNative

namespace PoincareMT.M63

variable {L : ℝ} {ι : Type*} [Fintype ι]

/-- The actual finite-vector action is split, componentwise real
translation, then join. MT2007 Claim 19.1, p. 437;
real/vector spectral-translation derivation, statement 6. -/
noncomputable def vectorPeriodicSpectralTranslation (a : ℝ) :
    State ((ℤ × Fin 2) × ι) →L[ℝ] State ((ℤ × Fin 2) × ι) :=
  (lpFinitePiEquiv ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap (fun _ : ι => realPeriodicSpectralTranslation (L := L) a)).comp
      (lpFinitePiEquiv ℝ).toContinuousLinearMap)

/-- The literal split identity and exact product-state norm hold
even for an empty finite component type. MT2007 Claim 19.1, p. 437;
real/vector spectral-translation derivation, statement 7. -/
theorem vectorPeriodicSpectralTranslation_spec (a : ℝ) (u : State ((ℤ × Fin 2) × ι)) :
    (∀ i, lpFinitePiEquiv ℝ (vectorPeriodicSpectralTranslation (L := L) a u) i =
      realPeriodicSpectralTranslation (L := L) a (lpFinitePiEquiv ℝ u i)) ∧
      ‖vectorPeriodicSpectralTranslation (L := L) a u‖ = ‖u‖ := by
  have hs (i : ι) : lpFinitePiEquiv ℝ (vectorPeriodicSpectralTranslation (L := L) a u) i =
      realPeriodicSpectralTranslation (L := L) a (lpFinitePiEquiv ℝ u i) := by
    change lpFinitePiEquiv ℝ ((lpFinitePiEquiv ℝ).symm
      (fun j => realPeriodicSpectralTranslation (L := L) a (lpFinitePiEquiv ℝ u j))) i = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hsq : ‖vectorPeriodicSpectralTranslation (L := L) a u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [lpFinitePiEquiv_norm_sq ℝ (vectorPeriodicSpectralTranslation (L := L) a u),
      lpFinitePiEquiv_norm_sq ℝ u]
    apply Finset.sum_congr rfl
    intro i _
    rw [hs i, (realPeriodicSpectralTranslation_spec a _).2]
  refine ⟨hs, ?_⟩
  nlinarith [norm_nonneg u, norm_nonneg (vectorPeriodicSpectralTranslation (L := L) a u)]

/-- The finite-vector phase action is jointly strongly continuous.
MT2007 Claim 19.1, p. 437; real/vector spectral-translation derivation,
statement 8. No operator-norm continuity is asserted. -/
theorem continuous_vectorPeriodicSpectralTranslation :
    Continuous (fun p : ℝ × State ((ℤ × Fin 2) × ι) =>
      vectorPeriodicSpectralTranslation (L := L) p.1 p.2) := by
  let S := lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ
  have harg (i : ι) : Continuous (fun p : ℝ × State ((ℤ × Fin 2) × ι) =>
      (p.1, S p.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp (S.continuous.comp continuous_snd))
  have h (i : ι) := (continuous_realPeriodicSpectralTranslation (L := L)).comp (harg i)
  exact S.symm.continuous.comp (continuous_pi h)

/-- A real spectral weight common to each real/imaginary pair
commutes with the finite-vector action when both states exist.
MT2007 Claim 19.1, p. 437; real/vector spectral-translation derivation,
statement 9. The weight may depend on the finite component. -/
theorem vectorPeriodicSpectralTranslation_real_weight (m : ℤ × ι → ℝ)
    (u v : State ((ℤ × Fin 2) × ι))
    (h : ∀ p, v p = m (p.1.1, p.2) * u p) (a : ℝ) :
    ∀ p, vectorPeriodicSpectralTranslation (L := L) a v p =
      m (p.1.1, p.2) * vectorPeriodicSpectralTranslation (L := L) a u p := by
  have hs (i : ι) (p : ℤ × Fin 2) :
      lpFinitePiEquiv ℝ v i p = m (p.1, i) * lpFinitePiEquiv ℝ u i p := h (p, i)
  intro p
  change lpFinitePiEquiv ℝ (vectorPeriodicSpectralTranslation (L := L) a v) p.2 p.1 =
    m (p.1.1, p.2) *
      lpFinitePiEquiv ℝ (vectorPeriodicSpectralTranslation (L := L) a u) p.2 p.1
  rw [(vectorPeriodicSpectralTranslation_spec a v).1 p.2,
    (vectorPeriodicSpectralTranslation_spec a u).1 p.2]
  exact realPeriodicSpectralTranslation_real_weight (fun n => m (n, p.2))
    (lpFinitePiEquiv ℝ u p.2) (lpFinitePiEquiv ℝ v p.2) (hs p.2) a p.1

/-- Every permitted actual vector jet is translated by the same
state action. MT2007 Claim 19.1, p. 437;
real/vector spectral-translation derivation, statement 10. -/
theorem vectorPeriodicJet_spectralTranslation [Fact (0 < L)]
    (k j : ℕ) (hj : j ≤ k) (u : State ((ℤ × Fin 2) × ι)) (a : ℝ) :
    vectorPeriodicJet (L := L) k j hj (vectorPeriodicSpectralTranslation (L := L) a u) =
      periodicTranslation a (vectorPeriodicJet (L := L) k j hj u) := by
  ext x i
  change realPeriodicJet (L := L) k j hj
    (lpFinitePiEquiv ℝ (vectorPeriodicSpectralTranslation (L := L) a u) i) x =
      realPeriodicJet (L := L) k j hj (lpFinitePiEquiv ℝ u i) (x - (a : AddCircle L))
  rw [(vectorPeriodicSpectralTranslation_spec a u).1 i, realPeriodicJet_spectralTranslation]
  rfl

/-- Zero translation is exactly the identity on the full vector
state. MT2007 Claim 19.1, p. 437;
real/vector spectral-translation derivation, statement 11. -/
theorem vectorPeriodicSpectralTranslation_zero :
    vectorPeriodicSpectralTranslation (L := L) (ι := ι) 0 = ContinuousLinearMap.id ℝ _ := by
  ext u p
  rcases p with ⟨p, i⟩
  have hs : lpFinitePiEquiv ℝ (vectorPeriodicSpectralTranslation (L := L) 0 u) i =
      lpFinitePiEquiv ℝ u i := by
    rw [(vectorPeriodicSpectralTranslation_spec 0 u).1 i]
    apply complexLpRealEquiv.symm.injective
    rw [(realPeriodicSpectralTranslation_spec 0 _).1,
      (periodicSpectralTranslation_group (L := L)).1]
    rfl
  exact congrArg (fun v : State (ℤ × Fin 2) => v p) hs

end PoincareMT.M63
