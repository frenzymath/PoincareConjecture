import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Coordinate
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Manifold Bundle

noncomputable section

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum.Variational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local instance dualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance dualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance bilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance bilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance endGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance endSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance connectionGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance connectionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

theorem chartConnection_smooth (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦
      chartConnection G q.1 q.2.1 q.2.2) {q | q.1 ∈ U} := by
  let S : Set ((ℝ × E) × (E × E)) := {q | q.1 ∈ U}
  have hDG : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ fderiv ℝ G q.1) S :=
    (hG.fderiv_of_isOpen hU (m := ∞) (by simp)).comp contDiffOn_fst (fun _ hq ↦ hq)
  have hv : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ q.2.1) S :=
    contDiffOn_fst.comp contDiffOn_snd (fun _ _ ↦ mem_univ _)
  have hw : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ q.2.2) S :=
    contDiffOn_snd.comp contDiffOn_snd (fun _ _ ↦ mem_univ _)
  have hfirst := (hDG.clm_apply ((contDiffOn_const (c := (0 : ℝ))).prodMk hv)).clm_apply hw
  have hsecond := (hDG.clm_apply ((contDiffOn_const (c := (0 : ℝ))).prodMk hw)).clm_apply hv
  let eval₁ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ
  let eval₂ : E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)
  have heval₁ : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ eval₁ q.2.2) S :=
    eval₁.contDiff.comp_contDiffOn hw
  have heval₂ : ContDiffOn ℝ ∞ (fun q : (ℝ × E) × (E × E) ↦ eval₂ q.2.1) S :=
    eval₂.contDiff.comp_contDiffOn hv
  have heval : ContDiffOn ℝ ∞
      (fun q : (ℝ × E) × (E × E) ↦ (ContinuousLinearMap.apply ℝ ℝ q.2.2).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) q.2.1)) S :=
    heval₁.clm_comp heval₂
  have hlast := heval.clm_comp (hDG.clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E)))
  have hC : ContDiffOn ℝ ∞
      (fun q : (ℝ × E) × (E × E) ↦ chartConnectionCovector G q.1 q.2.1 q.2.2) S :=
    (contDiffOn_const (c := (1 / 2 : ℝ))).smul ((hfirst.add hsecond).sub hlast)
  have hA : ContDiffOn ℝ ∞ (chartMetricOperator G) U := by
    unfold chartMetricOperator InnerProductSpace.continuousLinearMapOfBilin
    exact contDiffOn_const.clm_comp hG
  have hInv : ContDiffOn ℝ ∞ (fun z ↦ Ring.inverse (chartMetricOperator G z)) U :=
    contDiffOn_inverse_operator _ hA
      (fun z hz ↦ positive_form_operator_isUnit (G z) (hpos z hz))
  exact (hInv.comp contDiffOn_fst (fun _ h ↦ h)).clm_apply
    ((InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hC)

theorem chartConnectionBilinear_contDiffOn (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ (chartConnectionBilinear G) U := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  change ContDiffOn ℝ ∞ (fun z ↦ chartConnection G z v w) U
  exact (chartConnection_smooth G U hU hG hpos).comp
    (contDiffOn_id.prodMk (contDiffOn_const (c := (v, w)))) (fun _ hz ↦ hz)

theorem chartTransportOperator_contDiffOn
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × E) × E ↦ chartTransportOperator G q.1 q.2)
      (U ×ˢ univ) := by
  have hC : ContDiffOn ℝ ∞
      (fun q : (ℝ × E) × E ↦ chartConnectionBilinear G q.1) (U ×ˢ univ) :=
    (chartConnectionBilinear_contDiffOn G U hU hG hpos).comp
      contDiffOn_fst (fun _ hq ↦ hq.1)
  have hA : ContDiffOn ℝ ∞ (chartMetricOperator G) U := by
    unfold chartMetricOperator InnerProductSpace.continuousLinearMapOfBilin
    exact contDiffOn_const.clm_comp hG
  have hInv : ContDiffOn ℝ ∞ (fun z ↦ Ring.inverse (chartMetricOperator G z)) U :=
    contDiffOn_inverse_operator _ hA
      (fun z hz ↦ positive_form_operator_isUnit (G z) (hpos z hz))
  have hTime : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ G z (1, 0)) U :=
    (hG.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := ((1 : ℝ), (0 : E))))
  have hRaised : ContDiffOn ℝ ∞ (fun z ↦
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.comp
        (fderiv ℝ G z (1, 0))) U :=
    contDiffOn_const.clm_comp hTime
  have hRest := (hInv.clm_comp hRaised).comp
    (contDiffOn_fst (s := U ×ˢ (univ : Set E))) (fun _ hq ↦ hq.1)
  exact (hC.clm_apply contDiffOn_snd).neg.sub
    ((contDiffOn_const (c := (1 / 2 : ℝ))).smul hRest)

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
