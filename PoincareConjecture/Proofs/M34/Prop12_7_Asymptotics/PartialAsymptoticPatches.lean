import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.AsymptoticCertificate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy





theorem partialStandardCapFlow_asymptoticPatches_exists
    (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    (A : StandardCylinderAtlas) {epsilon t0 : ℝ}
    (hepsilon : 0 < epsilon) (ht0 : t0 ∈ Ico 0 F.lifetime) :
    ∃ K : Set StandardCapSpace, IsCompact K ∧
      ∀ x : StandardCapSpace, x ∉ K →
        ∃ N : StandardCylinderPatch epsilon⁻¹ x,
          StandardSpacetimeCylinderClose A F.flow.metric epsilon 0 1 (Icc 0 t0) N := by
  let e := g0.cylindrical_end
  let qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FH 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FA 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FS 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let p : endReferenceRegion e := Classical.choice inferInstance
  have ht : t0 ∈ Ico 0 F.lifetime ∩ Ico 0 1 :=
    ⟨ht0, ⟨ht0.1, ht0.2.trans_le (partialStandardCapFlow_lifetime_le_one P E0 F)⟩⟩
  obtain ⟨N, hN⟩ := partialFlow_endCylinder_intrinsicJetError_tendsto
    P E0 F e qH qA qS p ht ⌊epsilon⁻¹⌋₊ (half_pos hepsilon)
  have htail : ∀ k ≥ N, ∀ t ∈ Icc 0 t0, ∀ q : UnitTwoSphere,
      ∀ r ∈ Icc (17 / 5 : ℝ) (23 / 5),
        roundCylinderJetErrorSquared t
          (roundCylinderPullback (F.flow.metric t)
            (endAxialTranslation e (k + 1 : ℕ) ∘ e.coordinate))
          ⌊epsilon⁻¹⌋₊ (q, r) ≤ epsilon ^ 2 / 4 := by
    intro k hk t ht q r hr
    exact (hN k hk t ht q r hr).le.trans_eq (by ring)
  let R : ℝ := 1 + epsilon⁻¹ + (N : ℝ) + 9 / 2
  have hlength : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hN0 := Nat.cast_nonneg (α := ℝ) N
  refine ⟨{x | endExhaustion e x ≤ R}, endExhaustion_sublevel_isCompact e R, ?_⟩
  intro x hx
  have hlarge : R < endExhaustion e x := lt_of_not_ge hx
  obtain ⟨z, _hz, hcoord, hrho⟩ := endExhaustion_large_coordinate e
    (by dsimp [R] at hlarge; linarith : 3 < endExhaustion e x)
  have hmargin : (N : ℝ) + 9 / 2 < z.2 - epsilon⁻¹ := by
    dsimp [R] at hlarge
    linarith
  have hheight : epsilon⁻¹ < z.2 := by linarith
  rw [← hcoord]
  refine ⟨endCenteredCylinderPatch e hlength hheight z.1, ?_⟩
  have hclose := endCenteredCylinder_familyClose_of_tail e F.flow.metric (Icc 0 t0)
    hepsilon htail hmargin
  simp only [StandardSpacetimeCylinderClose, div_one, zero_add, one_mul]
  convert! hclose using 1

end PoincareConjecture.M34
