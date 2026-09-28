import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ReferenceCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CylinderSplice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.BackwardClock










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
  (hΩ : H.reference.regularLimitSet.Nonempty)
  {t : ℝ} (ht : t ∈ Ioo H.reference.tMinus T)
  (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04)
  (hR : (F.connection t).scalarCurvature N.center <
    (H.terminalConnection P04).scalarCurvature x₀)



def regularNeckSplicedCylinder :
    GeneralizedFlowCylinder (H.nonemptyExtension P04 hΩ).extended (H.terminalSliceCarrier P04)
      T ((H.terminalConnection P04).scalarCurvature x₀) (Ioc (-1) 0)
      (H.regularNeckSourceMap P04 ⟨ht.1.le, ht.2⟩ ⁻¹' N.carrier) := by
  let d := H.regularNeckExtendedCylinder P04 hΩ ⟨ht.1.le, ht.2⟩ N x₀
  have hQ : 0 < (H.terminalConnection P04).scalarCurvature x₀ := N.scalar_center_pos.trans hR
  have hold : ∀ s ∈ Ioc (-1 : ℝ) 0,
      T + s / (H.terminalConnection P04).scalarCurvature x₀ ≤ t →
        (T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) * (N.scale⁻¹ ^ 2) ∈
          Ioc (-1 : ℝ) 0 := by
    intro s hs hst
    rw [N.inverse_scale_sq_eq_scalar]
    exact (SingularRegularLimit.backward_clock_reparametrize ht.2 N.scalar_center_pos hR hs).2.1 hst
  refine GeneralizedFlowCylinder.spliceBox (F := (H.nonemptyExtension P04 hΩ).extended)
    (b := Sum.inr PUnit.unit) d hQ ht.1 (show Ioc H.reference.tMinus T ⊆
      ((H.nonemptyExtension P04 hΩ).extended.box (Sum.inr PUnit.unit)).interval from subset_rfl) hold ?_
  intro s hs hl hc x hx
  exact H.regularNeckExtendedCylinder_eq_regularBox P04 hΩ ⟨ht.1.le, ht.2⟩ N x₀
    ⟨hl, hc.trans_lt ht.2⟩ (hold s hs hc) x hx



theorem regularNeckSplicedCylinder_terminal (h : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0)
    (x : H.regularRegion P04) :
    (H.regularNeckSplicedCylinder P04 hΩ ht N x₀ hR).pointMap 0 h x =
      (⟨T, (H.terminalSliceHomeomorph P04).symm x⟩ : H.extendedPoint P04) := by
  simp only [regularNeckSplicedCylinder, GeneralizedFlowCylinder.spliceBox,
    GeneralizedFlowCylinder.pointMap, GeneralizedFlowCylinder.spliceForward]
  have hclock : T + 0 / (H.terminalConnection P04).scalarCurvature x₀ = T := by simp
  have hcut : ¬ T + 0 / (H.terminalConnection P04).scalarCurvature x₀ ≤ t := by
    simpa only [hclock] using ht.2.not_ge
  simp only [dif_neg hcut]
  change (⟨T + 0 / _, (H.regularBox P04 hΩ).forward _ _ x⟩ : H.extendedPoint P04) = _
  have hpoint (r s : ℝ) (hr : r ∈ Ioc H.reference.tMinus T)
      (hs : s ∈ Ioc H.reference.tMinus T) (hrs : r = s) :
      (⟨r, (H.regularBox P04 hΩ).forward r hr x⟩ : H.extendedPoint P04) =
      ⟨s, (H.regularBox P04 hΩ).forward s hs x⟩ := by
    subst s
    rfl
  rw [hpoint _ T _ ⟨H.reference.tMinus_lt, le_rfl⟩ hclock,
    H.regularBox_forward_terminal P04]


def regularTerminalDiffeomorph : Diffeomorph (𝓡 3) (𝓡 3)
    ((H.nonemptyExtension P04 hΩ).extended.slice T).carrier (H.regularRegion P04) ∞ where
  toEquiv := (H.terminalSliceHomeomorph P04).toEquiv
  contMDiff_toFun := H.terminalSliceHomeomorph_smooth P04
  contMDiff_invFun := H.terminalSliceHomeomorph_symm_smooth P04


def regularNeckTerminalCylinder :
    GeneralizedFlowCylinder (H.nonemptyExtension P04 hΩ).extended
      ((H.nonemptyExtension P04 hΩ).extended.slice T)
      T ((H.terminalConnection P04).scalarCurvature x₀) (Ioc (-1) 0)
      ((H.regularNeckSourceMap P04 ⟨ht.1.le, ht.2⟩ ∘ H.terminalSliceHomeomorph P04) ⁻¹' N.carrier) :=
  (H.regularNeckSplicedCylinder P04 hΩ ht N x₀ hR).rebaseSource
    (H.regularTerminalDiffeomorph P04 hΩ)



theorem regularNeckTerminalCylinder_identity (h : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0)
    (x : ((H.nonemptyExtension P04 hΩ).extended.slice T).carrier) :
    (H.regularNeckTerminalCylinder P04 hΩ ht N x₀ hR).pointMap 0 h x =
      (⟨T, x⟩ : (H.nonemptyExtension P04 hΩ).extended.point) := by
  rw [regularNeckTerminalCylinder, GeneralizedFlowCylinder.rebaseSource_pointMap]
  change (H.regularNeckSplicedCylinder P04 hΩ ht N x₀ hR).pointMap 0 h
    (H.terminalSliceHomeomorph P04 x) = _
  rw [H.regularNeckSplicedCylinder_terminal P04 hΩ ht N x₀ hR,
    Homeomorph.symm_apply_apply]

end PoincareConjecture.SingularTimeAssumptions
