import PoincareConjecture.Proofs.M09.InteriorPhaseJet
import PoincareConjecture.Proofs.M09.BrokenCostDifferential
import PoincareConjecture.Proofs.M09.PositiveMomentumDerivative
import PoincareConjecture.Proofs.M09.PhaseVariationUniqueness








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_sliceDifferential_prefix_bijective
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b (hc.trans hcb) hmax)) :
    Function.Bijective (A.sliceDifferential Z c) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ Q (TangentSpace (𝓡 n) : M → Type _) p
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) (A.gamma Z c)) :=
    VectorBundle.finiteDimensional ℝ Q (TangentSpace (𝓡 n) : M → Type _) (A.gamma Z c)
  have hkernel (W : TangentSpace (𝓡 n) p) (hW : A.sliceDifferential Z c W = 0) : W = 0 := by
    obtain ⟨D⟩ := exists_lineInteriorFamily A Z W c b hc hcb hmax
    let q := A.squareFamily Z (Real.sqrt c)
    let a := lineInteriorCoordinate A Z W c
    let ξ : ℝ → Q := fun r ↦ (initialLineChartPhase A Z W q (Real.sqrt c, r)).2
    let G : Q → Q →L[ℝ] Q →L[ℝ] ℝ := fun y ↦ squareChartMetric F T q (Real.sqrt c, y)
    have hs : Real.sqrt c ∈ sqrtParameterInterval 0 b := by
      simpa only [sqrtParameterInterval, Real.sqrt_zero] using
        (show Real.sqrt c ∈ Set.Icc 0 (Real.sqrt b) from
          ⟨Real.sqrt_nonneg c, Real.sqrt_le_sqrt hcb.le⟩)
    have hP := initialLineChartPhase_fixedTime_contDiffAt A Z W b (hc.trans hcb) hmax
      (Real.sqrt c) hs q (mem_chart_source Q q)
    have ha : ContDiffAt ℝ ∞ a 0 := D.coordinate_smooth
    have hξ : ContDiffAt ℝ ∞ ξ 0 := hP.snd
    have ha0 : deriv a 0 = 0 := lineInteriorCoordinate_deriv_eq_zero A Z W c hc (hcb.trans hmax) hW
    have hcoord : a 0 = (chartAt Q q) q := by
      simp only [a, lineInteriorCoordinate, zero_smul, add_zero, q]
    have htarget : a 0 ∈ (chartAt Q q).target := by
      rw [hcoord]
      exact (chartAt Q q).map_source (mem_chart_source Q q)
    have htime : Real.sqrt c ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
      ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le (Real.sqrt_nonneg c),
        Real.sqrt_lt_sqrt hc.le (hcb.trans hmax)⟩
    have hG : ContDiffAt ℝ ∞ G (a 0) :=
      ((squareChartMetric_smooth F T τmax hτmax hwindow q).contDiffAt
        ((isOpen_Ioo.prod (chartAt Q q).open_target).mem_nhds ⟨htime, htarget⟩)).comp
          (a 0) (contDiffAt_const.prodMk contDiffAt_id)
    have hS := D.tailAction_contDiffAt hM04 hτmax hwindow hc hcb hmax (a 0) D.center_mem
    have hR : ContDiffAt ℝ ∞ D.meetingCovector 0 :=
      ((hG.comp 0 ha).clm_apply hξ).add ((hS.fderiv_right (m := ∞) (by simp)).comp 0 ha)
    have hident := D.cost_first_derivatives hM04 hL hτmax hwindow hc hcb hmax
    have hR0 := localMin_meetingMomentum_deriv_eq_zero D.cost a D.meetingCovector
      (D.cost_contDiffAt hM04 hτmax hwindow hc hcb hmax)
      (D.cost_isLocalMin hM04 hτmax hwindow hc hcb hmax hmin)
      ha ha0 (hR.differentiableAt (by simp)) (hident.mono (fun _ h ↦ h.1))
      (hident.mono (fun _ h ↦ h.2))
    have hξ0 : deriv ξ 0 = 0 := positiveMomentum_deriv_eq_zero a ξ G D.tailAction ha hξ hG hS
      (fun v hv ↦ squareChartMetric_pos F T q (Real.sqrt c, a 0) htarget v hv) ha0 hR0
    have hzero : deriv (fun r ↦ initialLineChartPhase A Z W q (Real.sqrt c, r)) 0 = 0 := by
      have hd := (ha.differentiableAt (by simp)).hasDerivAt.prodMk
        (hξ.differentiableAt (by simp)).hasDerivAt
      rw [ha0, hξ0] at hd
      exact hd.deriv
    exact initialLinePhase_variation_zero_implies hM04 hτmax hwindow A Z W b
      (hc.trans hcb) hmax (Real.sqrt c) hs q (mem_chart_source Q q) hzero
  have hinj : Function.Injective (A.sliceDifferential Z c) := by
    intro U V hUV
    apply sub_eq_zero.mp
    apply hkernel
    rw [map_sub, hUV, sub_self]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) =
      Module.finrank ℝ (TangentSpace (𝓡 n) (A.gamma Z c)) := by
    rw [VectorBundle.finrank_eq ℝ Q (TangentSpace (𝓡 n) : M → Type _) p,
      VectorBundle.finrank_eq ℝ Q (TangentSpace (𝓡 n) : M → Type _) (A.gamma Z c)]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end PoincareConjecture.Proofs.M09
