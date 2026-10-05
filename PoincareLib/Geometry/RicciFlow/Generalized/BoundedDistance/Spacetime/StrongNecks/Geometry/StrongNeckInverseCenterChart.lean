import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckHalfFlow
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenInclusionDiffeomorph

/-!
# The actual inverse source normal chart

A whole terminal normal ball lies in the original strong neck's middle
half. Closed two-thirds core capture therefore guards its literal inverse
through the retained raw-stage map. Source: MT Sections 10.5-10.6,
pp. 263-265; M28 derivations 136 and 144.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.M28

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))

/-- The whole normal chart has original source height at most epsilon
inverse over two, before any use of a raw-stage inverse.
Source: MT pp. 263-265; M28 derivation 144. -/
theorem strongNeck_center_chart_height
    (hepsilon : epsilon ≤ (1 / 200 : ℝ)) {R : ℝ} (hR : R < 1 / 8)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen S) ∞)
    (hsource : Phi.source = Metric.ball 0 R)
    (htarget : Phi.target =
      ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        (strongNeckSourceCenter S) R)
    {z : E3} (hz : z ∈ Metric.ball 0 R) :
    |(S.coordinate_inverse (Phi z).val).2| ≤ epsilon⁻¹ / 2 := by
  have hhalf : epsilon < 1 / 2 := hepsilon.trans_lt (by norm_num)
  let N := GeneralizedStrongNeck.rescaled_half_source_neck S H hhalf
  have hinv : (200 : ℝ) ≤ epsilon⁻¹ := by
    have hh := one_div_le_one_div_of_le S.epsilon_pos hepsilon
    norm_num at hh
    exact hh
  have hradius : R ≤ epsilon⁻¹ / 8 := by linarith
  have hball : Phi z ∈
      ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        (strongNeckSourceCenter S) R := by
    rw [← htarget]
    exact Phi.toPartialEquiv.map_source (hsource.symm ▸ hz)
  have hball' : Phi z ∈
      ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        N.center (N.scale * N.epsilon⁻¹ / 8) := by
    change ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).edist
      (strongNeckSourceCenter S) (Phi z) < ENNReal.ofReal (1 * epsilon⁻¹ / 8)
    simpa only [one_mul] using
      hball.trans_le (ENNReal.ofReal_le_ofReal hradius)
  have hm := N.small_ball_subset_middle N.center_on_central_sphere hball'
  have hh : -(epsilon⁻¹ / 2) < (S.coordinate_inverse (Phi z).val).2 ∧
      (S.coordinate_inverse (Phi z).val).2 < epsilon⁻¹ / 2 := hm.2
  exact (abs_lt.mpr hh).le

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

/-- The inverse chart is the literal composition with open source inclusion
and the same retained raw-stage inverse.
Source: MT pp. 263-265; M28 derivation 144. -/
def inverseStrongNeckCenterChart
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen S) ∞)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M (F.slice t).carrier ∞) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞ :=
  (Phi.trans (openSubtypePartialDiffeomorph (strongNeckOpen S)
    ⟨strongNeckSourceCenter S⟩)).trans e.symm

omit [IsManifold (𝓡 3) ∞ M] in
/-- Forward evaluation retains the actual total partial-inverse map.
Source: MT pp. 263-265; M28 derivation 144. -/
@[simp] theorem inverseStrongNeckCenterChart_apply
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen S) ∞)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M (F.slice t).carrier ∞) (z : E3) :
    inverseStrongNeckCenterChart S Phi e z = e.symm (Phi z).val := rfl

omit [IsManifold (𝓡 3) ∞ M] in
/-- Capturing the original closed two-thirds core guards the whole normal
chart and retains its inverse points in the supplied fixed stage.
Source: MT pp. 263-265; M28 derivation 144. -/
theorem inverseStrongNeckCenterChart_domain
    (hepsilon : epsilon ≤ (1 / 200 : ℝ)) {R : ℝ} (hR : R < 1 / 8)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen S) ∞)
    (hsource : Phi.source = Metric.ball 0 R)
    (htarget : Phi.target =
      ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        (strongNeckSourceCenter S) R)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M (F.slice t).carrier ∞)
    (Vstage : Set M)
    (hcore : ∀ y ∈ S.carrier,
      |(S.coordinate_inverse y).2| ≤ 2 * epsilon⁻¹ / 3 →
        y ∈ e.target ∧ e.symm y ∈ Vstage) :
    let Psi := inverseStrongNeckCenterChart S Phi e
    Psi.source = Metric.ball 0 R ∧
      (∀ z ∈ Metric.ball 0 R, Psi z ∈ Vstage ∧ e (Psi z) = (Phi z).val) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ Psi (Metric.ball 0 R) ∧
      ContinuousOn Psi (Metric.ball 0 R) ∧
      IsOpen (Psi '' Metric.ball 0 R) ∧ Psi '' Metric.ball 0 R ⊆ Vstage := by
  let Psi := inverseStrongNeckCenterChart S Phi e
  have hguard (z : E3) (hz : z ∈ Metric.ball 0 R) :
      (Phi z).val ∈ e.target ∧ e.symm (Phi z).val ∈ Vstage := by
    have hh := strongNeck_center_chart_height S H hepsilon hR Phi hsource htarget hz
    apply hcore (Phi z).val (Phi z).property
    exact hh.trans (by have hi := inv_pos.mpr S.epsilon_pos; linarith)
  have hPsi : Psi.source = Metric.ball 0 R := by
    change (Phi.source ∩ Phi ⁻¹' (univ : Set (strongNeckOpen S)) ∩
      (fun z => (Phi z).val) ⁻¹' e.target) = Metric.ball 0 R
    simp only [preimage_univ, inter_univ]
    rw [hsource]
    ext z
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, (hguard z hz).1⟩⟩
  have hpoint (z : E3) (hz : z ∈ Metric.ball 0 R) :
      Psi z ∈ Vstage ∧ e (Psi z) = (Phi z).val :=
    ⟨(hguard z hz).2, e.toPartialEquiv.right_inv (hguard z hz).1⟩
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Psi (Metric.ball 0 R) := by
    simpa only [hPsi] using Psi.contMDiffOn
  refine ⟨hPsi, hpoint, hsmooth, hsmooth.continuousOn, ?_, ?_⟩
  · rw [← hPsi, Psi.toPartialEquiv.image_source_eq_target]
    exact Psi.open_target
  · rintro _ ⟨z, hz, rfl⟩
    exact (hpoint z hz).1

omit [IsManifold (𝓡 3) ∞ M] in
/-- The inverse chart's center is the actual retained diagonal center.
Source: MT pp. 263-265; M28 derivation 144. -/
theorem inverseStrongNeckCenterChart_zero
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen S) ∞)
    (hzero : Phi 0 = strongNeckSourceCenter S)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M (F.slice t).carrier ∞)
    {q : M} (hcenter : e.symm S.center = q) :
    inverseStrongNeckCenterChart S Phi e 0 = q := by
  rw [inverseStrongNeckCenterChart_apply, hzero]
  exact hcenter

end PoincareMT.M28
