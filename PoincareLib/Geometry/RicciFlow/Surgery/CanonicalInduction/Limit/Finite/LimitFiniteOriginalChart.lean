import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalPhysicalCoefficientJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.CenteredDiffeomorph

/-!
# The original centered chart on an exhaustion source

The actual native inverse and open subtype inclusion give one buffered
partial diffeomorphism before the source index or metric is chosen.
MT Proposition 17.1; limit-finite-original-anchor.md, AD1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private noncomputable def finiteOriginalSubtypeChart
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier) (q : U) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) U C.carrier ∞ := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨q⟩
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
    apply contMDiffWithinAt_id.congr_of_mem _ hx
    intro y hy
    exact e.right_inv hy
  exact {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := hi }

private noncomputable def finiteOriginalRestrict
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier)
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞) (R : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞ := by
  let e := Φ.toOpenPartialHomeomorph.restrOpen (Metric.ball 0 R) Metric.isOpen_ball
  exact {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := Φ.contMDiffOn.mono inter_subset_left
    contMDiffOn_invFun := Φ.symm.contMDiffOn.mono inter_subset_left }

/-- The literal native inverse, translated once, has a compact buffer
inside the original open source and an actual smooth subtype lift. -/
theorem limitFinite_exists_original_chart
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier) (q : U) :
    ∃ R : ℝ, 0 < R ∧ ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
      Φ.source = Metric.ball 0 R ∧ Φ 0 = q ∧
      (∀ z ∈ Metric.ball 0 R,
        (Φ z).val = (extChartAt (𝓡 3) q.val).symm
          ((extChartAt (𝓡 3) q.val) q.val + z)) ∧
      ∀ z ∈ Metric.closedBall 0 R,
        (extChartAt (𝓡 3) q.val) q.val + z ∈ (extChartAt (𝓡 3) q.val).target ∧
          (extChartAt (𝓡 3) q.val).symm
            ((extChartAt (𝓡 3) q.val) q.val + z) ∈ U := by
  let c := limitCanonicalNativeChart q.val
  let z0 : E := c q.val
  let i := finiteOriginalSubtypeChart U q
  let raw := M34.centeredDiffeomorph (c.symm.trans i.symm) z0
  have hiTarget : i.target = (U : Set C.carrier) :=
    U.openPartialHomeomorphSubtypeCoe_target ⟨q⟩
  have htrans : (c.symm.trans i.symm).source =
      c.target ∩ c.symm ⁻¹' (U : Set C.carrier) := by
    change (c.symm.toOpenPartialHomeomorph.trans i.symm.toOpenPartialHomeomorph).source = _
    rw [OpenPartialHomeomorph.trans_source]
    change c.target ∩ c.symm ⁻¹' i.target = _
    rw [hiTarget]
  have hzero : (0 : E) ∈ raw.source := by
    rw [M34.centeredDiffeomorph_mem_source]
    rw [htrans, add_zero]
    refine ⟨c.map_source (mem_extChartAt_source q.val), ?_⟩
    change c.symm (c q.val) ∈ U
    exact (c.left_inv (mem_extChartAt_source q.val)).symm ▸ q.property
  obtain ⟨R, hR, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (raw.open_source.mem_nhds hzero)
  let Φ := finiteOriginalRestrict U raw R
  have hsource : Φ.source = Metric.ball 0 R :=
    inter_eq_right.mpr (Metric.ball_subset_closedBall.trans hclosed)
  have hbuffer (z : E) (hz : z ∈ Metric.closedBall 0 R) :
      z0 + z ∈ c.target ∧ c.symm (z0 + z) ∈ U := by
    have h := (M34.centeredDiffeomorph_mem_source (c.symm.trans i.symm) z0 z).mp (hclosed hz)
    rwa [htrans] at h
  have hmap (z : E) (hz : z ∈ Metric.ball 0 R) :
      (Φ z).val = c.symm (z0 + z) := by
    have hy : c.symm (z0 + z) ∈ i.target := by
      rw [hiTarget]
      exact (hbuffer z (Metric.ball_subset_closedBall hz)).2
    exact i.right_inv hy
  refine ⟨R, hR, Φ, hsource, ?_, hmap, hbuffer⟩
  apply Subtype.ext
  rw [hmap 0 (Metric.mem_ball_self hR)]
  change (extChartAt (𝓡 3) q.val).symm ((extChartAt (𝓡 3) q.val) q.val + 0) = q.val
  rw [add_zero]
  exact (extChartAt (𝓡 3) q.val).left_inv (mem_extChartAt_source q.val)

/-- The actual open-ball identity differentiates through the fixed
subtype inclusion and the original translated native inverse. -/
theorem limitFinite_original_chart_differential
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier) (q : U)
    {R : ℝ} (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : Φ.source = Metric.ball 0 R)
    (hmap : ∀ z ∈ Metric.ball 0 R,
      (Φ z).val = (extChartAt (𝓡 3) q.val).symm
        ((extChartAt (𝓡 3) q.val) q.val + z))
    {z : E} (hz : z ∈ Metric.ball 0 R)
    (htarget : (extChartAt (𝓡 3) q.val) q.val + z ∈ (extChartAt (𝓡 3) q.val).target) :
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)).comp
        (mfderiv (𝓡 3) (𝓡 3) Φ z) =
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q.val).symm
        ((extChartAt (𝓡 3) q.val) q.val + z) := by
  let c := extChartAt (𝓡 3) q.val
  let a := M34.modelTranslationDiffeomorph (𝕜 := ℝ) (c q.val)
  have heq : (fun y => (Φ y).val) =ᶠ[𝓝 z] (c.symm ∘ a) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact hmap y hy
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q.val).contMDiffAt
    ((isOpen_extChartAt_target q.val).mem_nhds htarget)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) _)
    (Φ.mdifferentiableAt (by simp) (hsource.symm ▸ hz))
  have ha := mfderiv_comp z hc (a.contMDiff.mdifferentiable (by simp) z)
  have htranslation := M34.modelTranslationDiffeomorph_mfderiv (𝕜 := ℝ) (c q.val) z
  change mfderiv (𝓡 3) (𝓡 3) (fun y : E => c q.val + y) z =
    ContinuousLinearMap.id ℝ E at htranslation
  rw [htranslation] at ha
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun B => B v) (hd.symm.trans (heq.mfderiv_eq.trans ha))

end PoincareMT.M47
