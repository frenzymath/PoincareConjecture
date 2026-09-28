import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderPatchBounds
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.LifetimeUpperBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy



theorem standardFlowAsymptoticCertificate_of_tail
    {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
    (e : StandardCylindricalEnd g0.metric) (A : StandardCylinderAtlas)
    {ε t₀ : ℝ} (hε : 0 < ε) (ht₀ : t₀ ∈ Ico 0 F.base.lifetime) {N : ℕ}
    (htail : ∀ k ≥ N, ∀ t ∈ Icc 0 t₀, ∀ q : UnitTwoSphere,
      ∀ r ∈ Icc (17 / 5 : ℝ) (23 / 5),
        roundCylinderJetErrorSquared t
          (roundCylinderPullback (F.metric t)
            (endAxialTranslation e (k + 1 : ℕ) ∘ e.coordinate))
          ⌊ε⁻¹⌋₊ (q, r) ≤ ε ^ 2 / 4) :
    Nonempty (StandardFlowAsymptoticCertificate A F ε t₀) := by
  let R : ℝ := 1 + ε⁻¹ + (N : ℝ) + 9 / 2
  have hL : 0 < ε⁻¹ := inv_pos.mpr hε
  have hN0 := Nat.cast_nonneg (α := ℝ) N
  refine ⟨{
    epsilon_pos := hε
    t₀_mem := ht₀
    compact_set := {x | endExhaustion e x ≤ R}
    compact := endExhaustion_sublevel_isCompact e R
    patches := ?_ }⟩
  intro x hx
  have hlarge : R < endExhaustion e x := lt_of_not_ge hx
  obtain ⟨z, _hz, hcoord, hrho⟩ := endExhaustion_large_coordinate e
    (by dsimp [R] at hlarge; linarith : 3 < endExhaustion e x)
  have hmargin : (N : ℝ) + 9 / 2 < z.2 - ε⁻¹ := by
    dsimp [R] at hlarge
    linarith
  have hheight : ε⁻¹ < z.2 := by linarith
  rw [← hcoord]
  refine ⟨endCenteredCylinderPatch e hL hheight z.1, ?_⟩
  have hclose := endCenteredCylinder_familyClose_of_tail e F.metric (Icc 0 t₀)
    hε htail hmargin
  simp only [StandardSpacetimeCylinderClose, div_one, zero_add, one_mul]
  convert! hclose using 1



theorem partialStandardCapFlow_lifetime_le_one (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0) :
    F.lifetime ≤ 1 := by
  let qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FH 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FA 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FS 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact partialFlow_lifetime_le_one_of_end_jets P E0 F g0.cylindrical_end qH qA qS
    (Classical.choice inferInstance)




theorem standardFlowAsymptoticCertificate_exists (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : MaximalStandardCapFlow g0) (A : StandardCylinderAtlas)
    {ε t₀ : ℝ} (hε : 0 < ε) (ht₀ : t₀ ∈ Ico 0 F.base.lifetime) :
    Nonempty (StandardFlowAsymptoticCertificate A F ε t₀) := by
  let e := g0.cylindrical_end
  let qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FH 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FA 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (FS 3))) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let p : endReferenceRegion e := Classical.choice inferInstance
  have hlife := partialStandardCapFlow_lifetime_le_one P E0 F.base
  have ht : t₀ ∈ Ico 0 F.base.lifetime ∩ Ico 0 1 :=
    ⟨ht₀, ⟨ht₀.1, ht₀.2.trans_le hlife⟩⟩
  obtain ⟨N, hN⟩ := partialFlow_endCylinder_intrinsicJetError_tendsto
    P E0 F.base e qH qA qS p ht ⌊ε⁻¹⌋₊ (half_pos hε)
  apply standardFlowAsymptoticCertificate_of_tail F e A hε ht₀ (N := N)
  intro k hk t ht q r hr
  exact (hN k hk t ht q r hr).le.trans_eq (by ring)

end PoincareConjecture.M34
