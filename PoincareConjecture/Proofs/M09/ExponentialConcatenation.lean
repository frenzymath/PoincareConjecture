import PoincareConjecture.Proofs.M09.SmoothJoinAction
import PoincareConjecture.Proofs.M09.ExponentialAction
import PoincareConjecture.Proofs.M09.FamilySlices








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_concat_approx {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p q : M} (A : LExponentialFamily F T τmax p) (B : LExponentialFamily F T τmax q)
    (Z : TangentSpace (𝓡 n) p) (W : TangentSpace (𝓡 n) q)
    (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (hjoin : A.gamma Z c = B.gamma W c) (η : ℝ) (hη : 0 < η) :
    ∃ P : BackwardTimePath F T 0 b, P.curve 0 = p ∧ P.curve b = B.gamma W b ∧
      backwardLLength F T 0 b P.curve ≤ A.action Z c + B.action W b - B.action W c + η := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hb : 0 < b := hc.trans hcb
  have hcmax := hcb.trans hmax
  let D := ((fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain) ∩
    ((fun s : ℝ ↦ (W, s)) ⁻¹' B.squareDomain)
  have hD : IsOpen D := (A.square_open.preimage (continuous_const.prodMk continuous_id)).inter
    (B.square_open.preimage (continuous_const.prodMk continuous_id))
  have hI : Set.Icc 0 (Real.sqrt b) ⊆ D := by
    intro s hs
    have hsmax := hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact ⟨A.square_contains ⟨Set.mem_univ _, hs.1, hsmax⟩,
      B.square_contains ⟨Set.mem_univ _, hs.1, hsmax⟩⟩
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) D :=
    A.square_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hs ↦ hs.1)
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (B.squareFamily W) D :=
    B.square_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hs ↦ hs.2)
  have hcS : Real.sqrt c ∈ Set.Ioo 0 (Real.sqrt b) :=
    ⟨Real.sqrt_pos.mpr hc, Real.sqrt_lt_sqrt hc.le hcb⟩
  have hjoinS : A.squareFamily Z (Real.sqrt c) = B.squareFamily W (Real.sqrt c) := by
    have hca := A.square_agrees Z (Real.sqrt c)
      ⟨hcS.1.le, Real.sqrt_lt_sqrt hc.le hcmax⟩
    have hcb' := B.square_agrees W (Real.sqrt c)
      ⟨hcS.1.le, Real.sqrt_lt_sqrt hc.le hcmax⟩
    simp only [Real.sq_sqrt hc.le] at hca hcb'
    exact hca.trans (hjoin.trans hcb'.symm)
  obtain ⟨P, hP0, hPb, hPaction⟩ := exists_backwardPath_smoothJoin_action_le F hM04 T τmax
    hτmax hwindow b hb hmax (A.squareFamily Z) (B.squareFamily W) D hD hI hα hβ
      (Real.sqrt c) hcS hjoinS η hη
  have hAaction : (∫ s in 0..Real.sqrt c, squareCurveActionDensity F T (A.squareFamily Z) s) =
      A.action Z c := (lExponentialFamily_action_square_eq A Z c hc hcmax).symm
  have hBaction : (∫ s in 0..Real.sqrt b, squareCurveActionDensity F T (B.squareFamily W) s) =
      B.action W b := (lExponentialFamily_action_square_eq B W b hb hmax).symm
  have hCaction : (∫ s in 0..Real.sqrt c, squareCurveActionDensity F T (B.squareFamily W) s) =
      B.action W c := (lExponentialFamily_action_square_eq B W c hc hcmax).symm
  have hi := squareCurveActionDensity_intervalIntegrable F hM04 T τmax hτmax hwindow
    b hb hmax (B.squareFamily W) D hD hI hβ
  have hi0c : IntervalIntegrable (squareCurveActionDensity F T (B.squareFamily W))
      MeasureTheory.volume 0 (Real.sqrt c) := hi.mono_set (by
    rw [Set.uIcc_of_le (Real.sqrt_nonneg c), Set.uIcc_of_le (Real.sqrt_nonneg b)]
    exact Set.Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hcb.le))
  have hicb : IntervalIntegrable (squareCurveActionDensity F T (B.squareFamily W))
      MeasureTheory.volume (Real.sqrt c) (Real.sqrt b) := hi.mono_set (by
    rw [Set.uIcc_of_le (Real.sqrt_le_sqrt hcb.le), Set.uIcc_of_le (Real.sqrt_nonneg b)]
    exact Set.Icc_subset_Icc (Real.sqrt_nonneg c) le_rfl)
  have htail : (∫ s in Real.sqrt c..Real.sqrt b, squareCurveActionDensity F T (B.squareFamily W) s) =
      B.action W b - B.action W c := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi0c hicb
    rw [hBaction, hCaction] at hadd
    linarith
  refine ⟨P, hP0.trans (A.square_at_zero Z), ?_, ?_⟩
  · have he := B.square_agrees W (Real.sqrt b)
      ⟨Real.sqrt_nonneg b, Real.sqrt_lt_sqrt hb.le hmax⟩
    exact hPb.trans (by simpa only [Real.sq_sqrt hb.le] using he)
  · rw [hAaction, htail] at hPaction
    linarith

end PoincareConjecture.Proofs.M09
