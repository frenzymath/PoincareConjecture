import PoincareConjecture.Proofs.M35.RawFlow.AxisTimeCoefficients
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialCoordinate
import PoincareConjecture.Proofs.M35.RadialGauge.AxisDivisionJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

variable {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)

private theorem raw_speed_jet_contDiffOn (j : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => iteratedDeriv j (axisRadialSpeed (G.flow.metric p.1)) p.2)
      (Ico 0 G.lifetime ×ˢ univ) := by
  have hd {f : ℝ → ℝ → ℝ}
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Ico 0 G.lifetime ×ˢ univ)) :
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv (f p.1) p.2)
        (Ico 0 G.lifetime ×ˢ univ) := by
    have hD := hf.fderivWithin ((uniqueDiffOn_Ico 0 G.lifetime).prod uniqueDiffOn_univ)
      (m := ∞) (by simp)
    apply (hD.clm_apply (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))).congr
    intro p hp
    have hm : ∀ᶠ r in 𝓝 p.2, (p.1, r) ∈ Ico 0 G.lifetime ×ˢ (univ : Set ℝ) :=
      Eventually.of_forall (fun _ => ⟨hp.1, mem_univ _⟩)
    have h := ((hf.differentiableOn (by simp)) p hp).hasFDerivWithinAt.comp_hasFDerivAt p.2
      (hasFDerivAt_prodMk_right p.1 p.2) hm
    have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h.fderiv
    simpa only [Function.comp_def, Function.uncurry, fderiv_apply_one_eq_deriv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using he
  induction j with
  | zero => exact raw_axisRadialSpeed_contDiffOn G
  | succ j ih =>
      simpa only [iteratedDeriv_succ] using
        hd (f := fun t => iteratedDeriv j (axisRadialSpeed (G.flow.metric t))) ih

theorem raw_arclength_quotient_jet_continuous_slab
    {T : ℝ} (hTlt : T < G.lifetime) (j : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × ℝ =>
      iteratedDeriv j (axisDivision (radialArclength (G.flow.metric p.1.1))) p.2) := by
  have hd (t : ℝ) : deriv (radialArclength (G.flow.metric t)) =
      axisRadialSpeed (G.flow.metric t) :=
    funext (fun r => (radialArclength_hasDerivAt (G.flow.metric t) r).deriv)
  have hc : Continuous (fun p : Icc (0 : ℝ) T × ℝ =>
      iteratedDeriv j (axisRadialSpeed (G.flow.metric p.1.1)) p.2) :=
    (raw_speed_jet_contDiffOn G j).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨⟨p.1.2.1, p.1.2.2.trans_lt hTlt⟩, mem_univ _⟩)
  apply axisDivision_jet_continuous
    (fun t : Icc (0 : ℝ) T => radialArclength_contDiff (G.flow.metric t.1)) j
  exact hc.congr (fun p => by rw [iteratedDeriv_succ', hd])

theorem raw_intrinsic_coordinate_closed_slab_continuity
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T : ℝ} (hTlt : T < G.lifetime) :
    Continuous (fun p : Icc (0 : ℝ) T × StandardCapSpace =>
      intrinsicSpatialCoordinate (G.flow.metric p.1.1) p.2) ∧
    Continuous (fun p : Icc (0 : ℝ) T × StandardCapSpace =>
      fderiv ℝ (intrinsicSpatialCoordinate (G.flow.metric p.1.1)) p.2) := by
  let q (t : Icc (0 : ℝ) T) := axisDivision (radialArclength (G.flow.metric t.1))
  have hqs (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (q t) :=
    axisDivision_contDiff (radialArclength_contDiff (G.flow.metric t.1))
  have hqe (t : Icc (0 : ℝ) T) : Function.Even (q t) :=
    axisDivision_even_of_odd (radialArclength_contDiff (G.flow.metric t.1))
      (radialArclength_odd (G.flow.metric t.1)
        (hrotation t.1 ⟨t.2.1, t.2.2.trans_lt hTlt⟩))
  have hq0 : Continuous (fun p : Icc (0 : ℝ) T × ℝ => q p.1 p.2) := by
    simpa only [iteratedDeriv_zero] using raw_arclength_quotient_jet_continuous_slab G hTlt 0
  have hq2 : Continuous
      (fun p : Icc (0 : ℝ) T × ℝ => iteratedDeriv 1 (deriv (q p.1)) p.2) := by
    simpa only [iteratedDeriv_succ', iteratedDeriv_zero] using
      raw_arclength_quotient_jet_continuous_slab G hTlt 2
  have hQ : Continuous
      (fun p : Icc (0 : ℝ) T × ℝ => axisDivision (deriv (q p.1)) p.2) := by
    simpa only [iteratedDeriv_zero] using axisDivision_jet_continuous
      (fun t => (contDiff_infty_iff_deriv.mp (hqs t)).2) 0 hq2
  have harg : Continuous (fun p : Icc (0 : ℝ) T × StandardCapSpace => (p.1, ‖p.2‖)) :=
    continuous_fst.prodMk continuous_snd.norm
  have ha := hq0.comp harg
  refine ⟨ha.smul continuous_snd, ?_⟩
  have hL := ha.smul (continuous_const (y := ContinuousLinearMap.id ℝ StandardCapSpace))
  have hR := ((ContinuousLinearMap.smulRightL ℝ StandardCapSpace StandardCapSpace).continuous.comp
    ((hQ.comp harg).smul ((innerSL ℝ).continuous.comp continuous_snd))).clm_apply continuous_snd
  apply (hL.add hR).congr
  intro p
  exact ((hasFDerivAt_even_norm (hqs p.1) (hqe p.1) p.2).smul
    (hasFDerivAt_id p.2)).fderiv.symm

end PoincareConjecture.M35.Uniqueness
