import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderReverseBall
import PoincareConjecture.Proofs.M34.Standard.LocalCalibratedImageVolume
import PoincareConjecture.Proofs.M34.Standard.ScaledTangentComparison
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

theorem source_ball_volume_le_of_localization
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hU : IsOpen U) (h0 : 0 ∈ I) (hscale : 0 < scale)
    (g : RiemannianMetric 3 C.carrier) (o : C.carrier)
    {p : F.point} (hp : e.pointMap 0 h0 o = p) {a : ℝ}
    {V : Set C.carrier} (hV : IsOpen V) (hVU : V ⊆ U)
    (hAV : g.ball o (2 * a) ⊆ V)
    (hlocal : ∀ x ∈ (F.metric p.1).ball p.2 (a / Real.sqrt scale),
      ∃ y ∈ g.ball o (2 * a) ∩ U,
        e.pointMap 0 h0 y = (⟨p.1, x⟩ : F.point))
    (hbound : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
      e.pullbackInner 0 h0 x v v ≤ 2 * g.inner x v v) :
    calibratedMetricVolume (F.metric p.1) ((F.metric p.1).ball p.2 (a / Real.sqrt scale)) ≤
      ENNReal.ofReal (2 / Real.sqrt scale) ^ 3 * calibratedMetricVolume g (g.ball o (2 * a)) := by
  subst p
  let : T3Space C.carrier := C.t3Space
  let : SecondCountableTopology C.carrier := C.secondCountable
  let : PseudoEMetricSpace C.carrier := g.comparisonPseudoEMetric
  let f := e.spatialOpenPartialHomeomorph hU 0 h0
  let fV := f.restrOpen V hV
  let h := F.metric (origin + 0 / scale)
  have hA : MeasurableSet (g.ball o (2 * a)) :=
    (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  have hsource : g.ball o (2 * a) ⊆ fV.source := fun x hx =>
    ⟨hVU (hAV hx), hAV hx⟩
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 fV fV.source :=
    ((e.forward_smooth 0 h0).of_le (by simp)).mono inter_subset_left
  have hvolume := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le g h fV hf
    (div_pos two_pos (Real.sqrt_pos.mpr hscale)) (fun x hx v => by
      apply g.tangentNorm_le_two_div_sqrt_mul_of_scaled_inner_le h v _ hscale
      exact hbound x hx.2 v) hA hsource
  apply le_trans _ hvolume
  apply measure_mono
  intro x hx
  obtain ⟨y, hy, he⟩ := hlocal x hx
  have he' : e.forward 0 h0 y = x := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact ⟨y, hy.1, he'⟩

end PoincareConjecture.GeneralizedFlowCylinder
