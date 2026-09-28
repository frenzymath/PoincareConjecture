import PoincareConjecture.Proofs.M15.Mathlib.CurveExtension
import PoincareConjecture.Proofs.M08.RegularizedAction
import PoincareConjecture.Proofs.M09.SmoothJoinAction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M15




theorem exists_backwardPath_concat_approx
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T taumax : ℝ)
    (htau : 0 < taumax) (hwindow : Icc (T - taumax) T ⊆ J)
    {c b : ℝ} (hc : 0 < c) (hcb : c < b) (hb : b < taumax)
    (P : BackwardTimePath F T 0 c) (Q : BackwardTimePath F T c b)
    (RP : SqrtRegularPath P) (RQ : SqrtRegularPath Q)
    (hjoin : P.curve c = Q.curve c) (eta : ℝ) (heta : 0 < eta) :
    ∃ R : BackwardTimePath F T 0 b,
      R.curve 0 = P.curve 0 ∧ R.curve b = Q.curve b ∧
      backwardLLength F T 0 b R.curve ≤
        backwardLLength F T 0 c P.curve +
          backwardLLength F T c b Q.curve + eta := by
  obtain ⟨α, hα, heqα⟩ := RP.smooth.exists_global_extension_Icc
    (Real.sqrt_le_sqrt P.ordered.le) RP.open_domain RP.interval_subset
  obtain ⟨β, hβ, heqβ⟩ := RQ.smooth.exists_global_extension_Icc
    (Real.sqrt_le_sqrt Q.ordered.le) RQ.open_domain RQ.interval_subset
  let RA : SqrtRegularPath P := {
    curve := α
    domain := univ
    open_domain := isOpen_univ
    interval_subset := subset_univ _
    smooth := hα.contMDiffOn
    agrees := fun s hs => (heqα hs).trans (RP.agrees s hs)
  }
  let RB : SqrtRegularPath Q := {
    curve := β
    domain := univ
    open_domain := isOpen_univ
    interval_subset := subset_univ _
    smooth := hβ.contMDiffOn
    agrees := fun s hs => (heqβ hs).trans (RQ.agrees s hs)
  }
  have hα0 : α 0 = P.curve 0 := by
    simpa only [RA, Real.sqrt_zero, zero_pow (by decide : 2 ≠ 0)] using
      RA.agrees 0 (show 0 ∈ sqrtParameterInterval 0 c from
        ⟨by simp, Real.sqrt_nonneg c⟩)
  have hαc : α (Real.sqrt c) = P.curve c := by
    simpa only [RA, Real.sq_sqrt hc.le] using
      RA.agrees (Real.sqrt c) (right_mem_Icc.mpr (Real.sqrt_le_sqrt hc.le))
  have hβc : β (Real.sqrt c) = Q.curve c := by
    simpa only [RB, Real.sq_sqrt hc.le] using
      RB.agrees (Real.sqrt c) (left_mem_Icc.mpr (Real.sqrt_le_sqrt hcb.le))
  have hβb : β (Real.sqrt b) = Q.curve b := by
    simpa only [RB, Real.sq_sqrt (hc.trans hcb).le] using
      RB.agrees (Real.sqrt b) (right_mem_Icc.mpr (Real.sqrt_le_sqrt hcb.le))
  obtain ⟨R, hR0, hRb, hRaction⟩ := M09.exists_backwardPath_smoothJoin_action_le
    F hM04 T taumax htau hwindow b (hc.trans hcb) hb α β univ isOpen_univ
      (subset_univ _) hα.contMDiffOn hβ.contMDiffOn (Real.sqrt c)
      ⟨Real.sqrt_pos.mpr hc, Real.sqrt_lt_sqrt hc.le hcb⟩
      (hαc.trans (hjoin.trans hβc.symm)) eta heta
  have hA := M08.regularizedLAction_eq_backwardLLength RA
  have hB := M08.regularizedLAction_eq_backwardLLength RB
  change (∫ s in Real.sqrt 0..Real.sqrt c, M09.squareCurveActionDensity F T α s) =
    backwardLLength F T 0 c P.curve at hA
  rw [Real.sqrt_zero] at hA
  change (∫ s in Real.sqrt c..Real.sqrt b, M09.squareCurveActionDensity F T β s) =
    backwardLLength F T c b Q.curve at hB
  rw [hA, hB] at hRaction
  exact ⟨R, hR0.trans hα0, hRb.trans hβb, hRaction⟩

end PoincareConjecture.Proofs.M15
