import PoincareConjecture.Proofs.M65.Mathlib.EnergyWindow
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.EnergyGoodTimes
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.SubarcEnergy
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.EvolvedSmallAnnulus
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ProjectedLength










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}



theorem m65ShortLoopTransfer (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (E : M64AppliedFamilyEstimates V.flow.geometry C)
    {s eta : ℝ} (heta : 0 < eta) (has : a ≤ s) (hsb : s < b)
    (hgrowth : Real.exp (V.flow.geometry.K2 * (b - s)) < 4 / 3) :
    ∃ mu : ℝ, 0 < mu ∧
      ∀ circumference (h : 0 < circumference), circumference < 1 →
        ∀ z w : LoopTwoSphere,
          ∀ A : M64Annulus ((V.flow.geometry.product circumference h).flow.metric a)
            (m63CanonicalRamp (V.flow.geometry.product circumference h)
              (periodicFreeLoop (C.approximation.family z)))
            (m63CanonicalRamp (V.flow.geometry.product circumference h)
              (periodicFreeLoop (C.approximation.family w))), A.area < mu →
          (∀ t ∈ Set.Icc s b, m62Length (V.flow.geometry.product circumference h).flow
            ((C.solutions circumference h).curve w) t < eta / 2) →
          freeLoopLength (F.metric b)
            ((C.solutions circumference h).projected ⟨b, ⟨has.trans hsb.le, le_rfl⟩⟩ z) < eta := by
  let G := V.flow.geometry
  let energyBound := (m63FamilyLengthSup (F.metric a) Gamma + 1) * Real.exp (G.K2 * (b - a))
  let B := (|energyBound| + 1) / (b - s)
  have hB : 0 < B := div_pos (by positivity) (sub_pos.mpr hsb)
  have hBmul : B * (b - s) = |energyBound| + 1 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hsb.ne')
  have hwindow : energyBound / B < b - s := by
    apply (div_lt_iff₀ hB).mpr
    nlinarith [le_abs_self energyBound]
  let r := min (eta / 2) (((1 / 400 : ℝ) ^ 2) / B)
  have hr : 0 < r := lt_min (half_pos heta) (div_pos (by norm_num) hB)
  have hrEta : r ≤ eta / 2 := min_le_left _ _
  have hrB : r * B ≤ (1 / 400 : ℝ) ^ 2 :=
    (le_div_iff₀ hB).mp (min_le_right _ _)
  obtain ⟨epsilon, hepsilon, hcomparison⟩ := V.flow.ramp_comparison (by norm_num) r hr
  let mu := epsilon / (2 * Real.exp (5 * G.K0 * (b - a)))
  have hmu : 0 < mu := div_pos hepsilon (mul_pos (by norm_num) (Real.exp_pos _))
  have hthreshold : Real.exp (5 * G.K0 * (b - a)) * mu < epsilon := by
    dsimp [mu]
    field_simp
    linarith
  refine ⟨mu, hmu, ?_⟩
  intro circumference h hlt z w A hA hshort
  let S := C.solutions circumference h
  let P := G.product circumference h
  have hb : b ∈ Set.Icc a b := ⟨has.trans hsb.le, le_rfl⟩
  obtain ⟨t, ht, henergy⟩ := M65.exists_energy_le_in_window has hsb le_rfl
    (m65FamilyEnergy_nonneg C circumference h z)
    (m64FamilyEnergyIntegrable C E circumference h z)
    (m64FamilyEnergyBound C E circumference h hlt z) hB hwindow
  have htopen : t ∈ Set.Ioo a b := ⟨has.trans_lt ht.1, ht.2⟩
  have htclosed := Set.Ioo_subset_Icc_self htopen
  by_contra hnotshort
  have hterminal : eta ≤ m62Length P.flow (S.curve z) b :=
    (le_of_not_gt hnotshort).trans (m65ProjectedFamilyLength_le S ⟨b, hb⟩ z)
  have hlength : 0 ≤ m62Length P.flow (S.curve z) t :=
    intervalIntegral.integral_nonneg_of_forall (by unfold curvePeriod; positivity)
      (M62.speed_nonneg P.flow (S.curve z) t)
  have hexp : Real.exp (G.K2 * (b - t)) ≤ Real.exp (G.K2 * (b - s)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1.le b) G.nonnegative.2.2
  have hforward := (E.curve_estimates circumference h z).length_exponential
    t b htclosed hb ht.2.le
  have hlarge : 3 / 4 * eta ≤ m62Length P.flow (S.curve z) t := by
    have hupper := hforward.trans
      (mul_le_mul_of_nonneg_left (hexp.trans hgrowth.le) hlength)
    nlinarith
  have hsubarcs := m65SmallSubarcs_of_energy_le P.flow (S.curve z) (S.shrinking z)
    htopen hr.le (by norm_num : (0 : ℝ) ≤ 1 / 400) henergy hrB
  obtain ⟨At, hAt⟩ := m65EvolvedSmallAnnulus S V.flow.evolution z w hmu hthreshold A hA
    ⟨t, htclosed⟩
  have hcompare := hcomparison circumference h t htclosed
    (fun x => S.curve z x t) (fun x => S.curve w x t)
    ((S.shrinking z).periodic t htclosed) ((S.shrinking w).periodic t htclosed)
    ((S.shrinking z).spatial_regular t htclosed) ((S.shrinking w).spatial_regular t htclosed)
    (S.ramp z t htclosed) (S.ramp w t htclosed)
    (by change r ≤ m62Length P.flow (S.curve z) t; linarith)
    (fun alpha beta hab hbeta hlen =>
      (hsubarcs alpha beta hab hbeta hlen).trans_lt (by norm_num)) At hAt
  have hnode := hshort t ⟨ht.1.le, ht.2.le⟩
  change 3 / 4 * m62Length P.flow (S.curve z) t ≤ m62Length P.flow (S.curve w) t at hcompare
  nlinarith

end PoincareConjecture
