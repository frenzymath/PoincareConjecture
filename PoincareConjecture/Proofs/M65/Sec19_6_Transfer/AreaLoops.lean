import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FillingWitnesses
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.AnnularInfimum
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.AreaAlternative









set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}



theorem m65FamilyFillingDifference_le_initial (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (Set.univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (z w : LoopTwoSphere)
    (A : M64Annulus ((V.flow.geometry.product circumference h).flow.metric a)
      (m63CanonicalRamp (V.flow.geometry.product circumference h)
        (periodicFreeLoop (C.approximation.family z)))
      (m63CanonicalRamp (V.flow.geometry.product circumference h)
        (periodicFreeLoop (C.approximation.family w)))) (t : Set.Icc a b) :
    |fillingArea (F.metric t) ((C.solutions circumference h).projected t w) -
      fillingArea (F.metric t) ((C.solutions circumference h).projected t z)| ≤
        Real.exp (5 * V.flow.geometry.K0 * ((t : ℝ) - a)) * A.area := by
  let S := C.solutions circumference h
  have E := m65FamilyAnnulusFlow S V.flow.evolution z w A
  obtain ⟨D⟩ := m65ProjectedDisk_nonempty hM64 compact S t z
  exact (m65ProjectedAreaDifference_le_infimum S
    (V.flow.projection circumference h) (V.disks circumference h) z w E t D).trans
      (m65FamilyAnnulusArea_le_initial S z w E A t)



theorem m65AreaLoopTransfer (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (Set.univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta) (hab : a ≤ b)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ circumference (h : 0 < circumference), ∀ z w : LoopTwoSphere,
      ∀ A : M64Annulus ((V.flow.geometry.product circumference h).flow.metric a)
        (m63CanonicalRamp (V.flow.geometry.product circumference h)
          (periodicFreeLoop (C.approximation.family z)))
        (m63CanonicalRamp (V.flow.geometry.product circumference h)
          (periodicFreeLoop (C.approximation.family w))), A.area < mu →
      fillingArea (F.metric b) ((C.solutions circumference h).projected ⟨b, hab, le_rfl⟩ w) ≤
        areaComparisonProfile F (fillingArea (F.metric a) (C.approximation.family w)) b + eta / 2 →
      fillingArea (F.metric b) ((C.solutions circumference h).projected ⟨b, hab, le_rfl⟩ z) ≤
        areaComparisonProfile F (fillingArea (F.metric a) (C.approximation.family z)) b + eta := by
  let E := Real.exp (5 * V.flow.geometry.K0 * (b - a))
  let Q := Real.exp (-(∫ t in a..b, flowScalarCurvatureInfimum F t / 2))
  have hE : 0 < E := Real.exp_pos _
  have hQ : 0 < Q := Real.exp_pos _
  let mu := eta / (4 * (E + Q))
  have hmu : 0 < mu := div_pos heta (mul_pos (by norm_num) (add_pos hE hQ))
  have herror : E * mu + Q * mu < eta / 2 := by
    have hcancel : mu * (4 * (E + Q)) = eta :=
      div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) (add_pos hE hQ)))
    nlinarith
  refine ⟨mu, hmu, ?_⟩
  intro circumference h z w A hA hnode
  let S := C.solutions circumference h
  have hstart := m65FamilyFillingDifference_le_initial hM64 compact V C
    circumference h z w A ⟨a, le_rfl, hab⟩
  rw [(C.solutions circumference h).projected_initial ⟨le_rfl, hab⟩] at hstart
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hstart
  have hend := m65FamilyFillingDifference_le_initial hM64 compact V C
    circumference h z w A ⟨b, hab, le_rfl⟩
  have hinitial : |fillingArea (F.metric a) (C.approximation.family w) -
      fillingArea (F.metric a) (C.approximation.family z)| ≤ mu := hstart.trans hA.le
  have hterminal : fillingArea (F.metric b) (S.projected ⟨b, hab, le_rfl⟩ z) ≤
      fillingArea (F.metric b) (S.projected ⟨b, hab, le_rfl⟩ w) + E * mu := by
    have he := hend.trans (mul_le_mul_of_nonneg_left hA.le hE.le)
    have ha := neg_le_abs
      (fillingArea (F.metric b) (S.projected ⟨b, hab, le_rfl⟩ w) -
        fillingArea (F.metric b) (S.projected ⟨b, hab, le_rfl⟩ z))
    linarith
  have h := m65AreaAlternative_transfer F hinitial hterminal hnode
  change _ ≤ areaComparisonProfile F _ b + eta / 2 + E * mu + Q * mu at h
  linarith

end PoincareConjecture
