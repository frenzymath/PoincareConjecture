import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CylinderSource
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CylinderClock
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CylinderCompatibility
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Extension



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

def regularNeckSourceMap {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T) :
    H.regularRegion P04 → (F.slice t).carrier := H.reference.forward t ht ∘ Subtype.val



def regularNeckOldCylinder {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04) :
    GeneralizedFlowCylinder F (H.terminalSliceCarrier P04) t (N.scale⁻¹ ^ 2)
      (Ioc (-1) 0) (H.regularNeckSourceMap P04 ht ⁻¹' N.carrier) := by
  let f := H.regularNeckSourceMap P04 ht
  let g := SingularRegularLimit.openRetraction (H.regularRegion P04) x₀ ∘ H.reference.inverse t ht
  have hf : Topology.IsEmbedding f := (H.reference.forward_openEmbedding t ht).isEmbedding.comp
    (H.regularRegion P04).isOpen.isOpenEmbedding_subtypeVal.isEmbedding
  have hfs : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (H.reference.forward_smooth t ht).comp contMDiff_subtype_val
  have hgs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (range f) := by
    apply SingularRegularLimit.contMDiffOn_openRetraction_comp _ x₀
      (H.reference.inverse_smooth t ht).contMDiffOn
    rintro y ⟨x, rfl⟩
    change H.reference.inverse t ht (H.reference.forward t ht x) ∈ H.regularRegion P04
    rw [H.reference.left_inverse]
    exact x.property
  have hleft : Function.LeftInverse g f := by
    intro x
    change SingularRegularLimit.openRetraction (H.regularRegion P04) x₀
      (H.reference.inverse t ht (H.reference.forward t ht x)) = x
    rw [H.reference.left_inverse, SingularRegularLimit.openRetraction_coe]
  exact N.time_cylinder.rebaseSourceEmbedding (C' := H.terminalSliceCarrier P04) f g hf hfs hgs hleft

theorem regularNeckOldCylinder_pointMap {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04)
    (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) (x : H.regularRegion P04) :
    (H.regularNeckOldCylinder P04 ht N x₀).pointMap s hs x =
      N.time_cylinder.pointMap s hs (H.reference.forward t ht x) := rfl



def regularNeckExtendedCylinder (hΩ : H.reference.regularLimitSet.Nonempty)
    {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04) :
    GeneralizedFlowCylinder (H.nonemptyExtension P04 hΩ).extended (H.terminalSliceCarrier P04)
      t (N.scale⁻¹ ^ 2) (Ioc (-1) 0) (H.regularNeckSourceMap P04 ht ⁻¹' N.carrier) :=
  (H.nonemptyExtension P04 hΩ).pushCylinder (H.regularNeckOldCylinder P04 ht N x₀) ⟨x₀⟩

theorem regularNeckExtendedCylinder_pointMap (hΩ : H.reference.regularLimitSet.Nonempty)
    {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04)
    (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) (x : H.regularRegion P04) :
    (H.regularNeckExtendedCylinder P04 hΩ ht N x₀).pointMap s hs x =
      H.oldSpacetimeForward P04 (N.time_cylinder.pointMap s hs (H.reference.forward t ht x)) := by
  exact (H.nonemptyExtension P04 hΩ).pushCylinder_pointMap
    (H.regularNeckOldCylinder P04 ht N x₀) ⟨x₀⟩ s hs x



theorem regularNeckExtendedCylinder_eq_regularBox
    (hΩ : H.reference.regularLimitSet.Nonempty) {t : ℝ}
    (ht : t ∈ Ico H.reference.tMinus T) (N : GeneralizedStrongNeck F t H.epsilon)
    (x₀ : H.regularRegion P04) {τ : ℝ}
    (hτ : τ ∈ Ioo H.reference.tMinus T)
    (hcyl : (τ - t) * (N.scale⁻¹ ^ 2) ∈ Ioc (-1 : ℝ) 0)
    (x : H.regularRegion P04) (hx : H.reference.forward t ht x ∈ N.carrier) :
    (H.regularNeckExtendedCylinder P04 hΩ ht N x₀).forwardAtTime τ hcyl x =
      (H.regularBox P04 hΩ).forward τ ⟨hτ.1, hτ.2.le⟩ x := by
  let q := N.scale⁻¹ ^ 2
  have hRpoint (v w : ℝ) (hv : v ∈ Ico H.reference.tMinus T)
      (hw : w ∈ Ico H.reference.tMinus T) (hvw : v = w) :
      (⟨v, H.reference.forward v hv x⟩ : F.point) = ⟨w, H.reference.forward w hw x⟩ := by
    subst w
    rfl
  have hz : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by norm_num
  have hrz : t + 0 / q ∈ Ico H.reference.tMinus T := by simpa using ht
  have hstart : H.reference.forward (t + 0 / q) hrz x =
      N.time_cylinder.forward 0 hz (H.reference.forward t ht x) := by
    have h := N.cylinder_identity hz _ hx
    have heq : (⟨t + 0 / q, H.reference.forward (t + 0 / q) hrz x⟩ : F.point) =
        ⟨t, H.reference.forward t ht x⟩ := hRpoint _ t hrz ht (by simp)
    exact eq_of_heq (Sigma.mk.inj_iff.mp (heq.trans h.symm)).2
  have hclock : t + ((τ - t) * q) / q = τ := N.time_cylinder.physical_clock_eq τ
  have hrt : t + ((τ - t) * q) / q ∈ Ico H.reference.tMinus T := hclock.symm ▸ ⟨hτ.1.le, hτ.2⟩
  have hworld := H.reference.forward_eq_cylinder_of_eq N.time_cylinder ordConnected_Ioc
    (H.reference.forward t ht x) hx (x : M) hz hrz hstart hcyl hrt
  have hOld : N.time_cylinder.pointMap ((τ - t) * q) hcyl (H.reference.forward t ht x) =
      (⟨τ, H.reference.forward τ ⟨hτ.1.le, hτ.2⟩ x⟩ : F.point) := by
    exact (congrArg (Sigma.mk (t + ((τ - t) * q) / q)) hworld.symm).trans
      (hRpoint _ τ hrt ⟨hτ.1.le, hτ.2⟩ hclock)
  have hPoint : (⟨τ, (H.regularNeckExtendedCylinder P04 hΩ ht N x₀).forwardAtTime τ hcyl x⟩ :
        H.extendedPoint P04) = ⟨τ, (H.regularBox P04 hΩ).forward τ ⟨hτ.1, hτ.2.le⟩ x⟩ := by
    rw [(H.regularNeckExtendedCylinder P04 hΩ ht N x₀).forwardAtTime_point,
      H.regularNeckExtendedCylinder_pointMap P04 hΩ ht N x₀, hOld,
      H.oldSpacetimeForward_eq P04 hτ.2.ne, H.regularBox_forward_old P04 hΩ τ _ hτ.2]
  exact eq_of_heq (Sigma.mk.inj_iff.mp hPoint).2

end PoincareConjecture.SingularTimeAssumptions
