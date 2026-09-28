import PoincareConjecture.Proofs.M35.RawFlow.ArclengthSlabContinuity
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSlopeEquation

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)

theorem raw_axisWarpingRadius_deriv_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv (axisWarpingRadius (G.flow.metric p.1)) p.2)
      (Ico 0 G.lifetime ×ˢ univ) := by
  let U : Set (ℝ × ℝ) := Ico 0 G.lifetime ×ˢ univ
  let A (p : ℝ × ℝ) := axisWarpingRadius (G.flow.metric p.1) p.2
  have hA : ContDiffOn ℝ ∞ A U := raw_axisWarpingRadius_contDiffOn G
  have hD := hA.fderivWithin ((uniqueDiffOn_Ico 0 G.lifetime).prod uniqueDiffOn_univ)
    (m := ∞) (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))).congr
  intro p hp
  have hm : ∀ᶠ r in 𝓝 p.2, (p.1, r) ∈ U :=
    Eventually.of_forall (fun r => ⟨hp.1, mem_univ r⟩)
  have hd := ((hA.differentiableOn (by simp)) p hp).hasFDerivWithinAt.comp_hasFDerivAt p.2
    (hasFDerivAt_prodMk_right p.1 p.2) hm
  have hh := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hd.fderiv
  simpa only [Function.comp_def, A, fderiv_apply_one_eq_deriv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using hh

variable (P : RicciFlowCurvatureTheory.{0})
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

theorem rawWarpingSlope_eq_original_deriv {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) (s : ℝ) :
    rawWarpingSlope P G hrotation t s =
      deriv (axisWarpingRadius (G.flow.metric t)) (rawInverseRadius P G hrotation t s) /
        axisRadialSpeed (G.flow.metric t) (rawInverseRadius P G hrotation t s) := by
  unfold rawWarpingSlope
  rw [rawWarpingRadius_eq P G hrotation ht, rawInverseRadius_eq P G hrotation ht]
  have hd := ((axisWarpingRadius_contDiff (G.flow.metric t)).differentiable (by simp)
    ((radialArclengthOrderIso (G.flow.metric t)
      (hrotation t ht) (G.complete P ht)).symm s)).hasDerivAt
  have hh := hd.comp s
    (radialArclengthOrderIso_symm_hasDerivAt (G.flow.metric t)
      (hrotation t ht) (G.complete P ht) s)
  change deriv (axisWarpingRadius (G.flow.metric t) ∘
      ⇑(radialArclengthOrderIso (G.flow.metric t) (hrotation t ht) (G.complete P ht)).symm) s =
    deriv (axisWarpingRadius (G.flow.metric t))
      ((radialArclengthOrderIso (G.flow.metric t) (hrotation t ht) (G.complete P ht)).symm s) *
    (Real.sqrt (axisRadialCoefficient (G.flow.metric t)
      ((radialArclengthOrderIso (G.flow.metric t) (hrotation t ht) (G.complete P ht)).symm s)))⁻¹
  exact hh.deriv

theorem rawWarpingSlope_continuousOn_slab {T : ℝ} (hT : 0 ≤ T)
    (hTlt : T < G.lifetime) :
    ContinuousOn (Function.uncurry (rawWarpingSlope P G hrotation)) (Icc 0 T ×ˢ univ) := by
  let q (p : ℝ × ℝ) := (p.1, rawInverseRadius P G hrotation p.1 p.2)
  have hq : ContinuousOn q (Icc 0 T ×ˢ univ) :=
    continuousOn_fst.prodMk (rawInverseRadius_continuousOn_slab G P hrotation hT hTlt)
  have hm : MapsTo q (Icc 0 T ×ˢ univ) (Ico 0 G.lifetime ×ˢ univ) :=
    fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hTlt⟩, mem_univ _⟩
  have hnum := (raw_axisWarpingRadius_deriv_contDiffOn G).continuousOn.comp hq hm
  have hden := (raw_axisRadialSpeed_contDiffOn G).continuousOn.comp hq hm
  apply (hnum.div hden (fun p _ => (axisRadialSpeed_pos (G.flow.metric p.1) (q p).2).ne')).congr
  intro p hp
  exact rawWarpingSlope_eq_original_deriv G P hrotation ⟨hp.1.1, hp.1.2.trans_lt hTlt⟩ p.2

theorem rawWarpingRadius_continuousOn_slab {T : ℝ} (hT : 0 ≤ T)
    (hTlt : T < G.lifetime) :
    ContinuousOn (Function.uncurry (rawWarpingRadius P G hrotation)) (Icc 0 T ×ˢ univ) := by
  have hq := continuousOn_fst.prodMk (rawInverseRadius_continuousOn_slab G P hrotation hT hTlt)
  exact (raw_axisWarpingRadius_contDiffOn G).continuousOn.comp hq
    (fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hTlt⟩, mem_univ _⟩)

end PoincareConjecture.M35.Uniqueness
