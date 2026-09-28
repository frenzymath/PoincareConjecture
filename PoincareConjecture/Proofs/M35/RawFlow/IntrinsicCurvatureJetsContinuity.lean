import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSlabContinuity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)

private theorem spatial_deriv_contDiffOn {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Ico 0 G.lifetime ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2)
      (Ico 0 G.lifetime ×ˢ univ) := by
  let U : Set (ℝ × ℝ) := Ico 0 G.lifetime ×ˢ univ
  have hD := hF.fderivWithin ((uniqueDiffOn_Ico 0 G.lifetime).prod uniqueDiffOn_univ)
    (m := ∞) (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))).congr
  intro p hp
  have hm : ∀ᶠ r in 𝓝 p.2, (p.1, r) ∈ U :=
    Eventually.of_forall (fun r => ⟨hp.1, mem_univ r⟩)
  have hd := ((hF.differentiableOn (by simp)) p hp).hasFDerivWithinAt.comp_hasFDerivAt p.2
    (hasFDerivAt_prodMk_right p.1 p.2) hm
  have hh := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hd.fderiv
  simpa only [Function.comp_def, Function.uncurry, fderiv_apply_one_eq_deriv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using hh


noncomputable def rawIntrinsicAxisJet : ℕ → ℝ → ℝ → ℝ
  | 0, t, r => axisWarpingRadius (G.flow.metric t) r
  | j + 1, t, r => deriv (rawIntrinsicAxisJet j t) r / axisRadialSpeed (G.flow.metric t) r

theorem rawIntrinsicAxisJet_contDiffOn (j : ℕ) :
    ContDiffOn ℝ ∞ (Function.uncurry (rawIntrinsicAxisJet G j))
      (Ico 0 G.lifetime ×ˢ univ) := by
  induction j with
  | zero => exact raw_axisWarpingRadius_contDiffOn G
  | succ j ih =>
      exact (spatial_deriv_contDiffOn G ih).div (raw_axisRadialSpeed_contDiffOn G)
        (fun p _ => (axisRadialSpeed_pos (G.flow.metric p.1) p.2).ne')

theorem rawIntrinsicAxisJet_contDiff (j : ℕ) {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) :
    ContDiff ℝ ∞ (rawIntrinsicAxisJet G j t) := by
  apply contDiffOn_univ.mp
  exact (rawIntrinsicAxisJet_contDiffOn G j).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun r _ => ⟨ht, mem_univ r⟩)

variable (P : RicciFlowCurvatureTheory.{0})
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)



theorem raw_intrinsic_jet_eq_original (j : ℕ) {t : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (s : ℝ) :
    iteratedDeriv j (rawWarpingRadius P G hrotation t) s =
      rawIntrinsicAxisJet G j t (rawInverseRadius P G hrotation t s) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
      have heq : iteratedDeriv j (rawWarpingRadius P G hrotation t) =
          fun r => rawIntrinsicAxisJet G j t (rawInverseRadius P G hrotation t r) :=
        funext ih
      have hq : HasDerivAt (rawInverseRadius P G hrotation t)
          (axisRadialSpeed (G.flow.metric t) (rawInverseRadius P G hrotation t s))⁻¹ s := by
        have hfun : rawInverseRadius P G hrotation t =
            ⇑(radialArclengthOrderIso (G.flow.metric t) (hrotation t ht)
              (G.complete P ht)).symm := funext (rawInverseRadius_eq P G hrotation ht)
        rw [hfun]
        exact radialArclengthOrderIso_symm_hasDerivAt (G.flow.metric t)
          (hrotation t ht) (G.complete P ht) s
      have hj := ((rawIntrinsicAxisJet_contDiff G j ht).differentiable
        (by simp) (rawInverseRadius P G hrotation t s)).hasDerivAt
      rw [iteratedDeriv_succ, heq]
      simpa only [Function.comp_def, rawIntrinsicAxisJet, div_eq_mul_inv] using
        (hj.comp s hq).deriv



theorem raw_intrinsic_jet_continuousOn_slab (j : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hTlt : T < G.lifetime) :
    ContinuousOn (fun p : ℝ × ℝ =>
      iteratedDeriv j (rawWarpingRadius P G hrotation p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  have hq := continuousOn_fst.prodMk (rawInverseRadius_continuousOn_slab G P hrotation hT hTlt)
  have h := (rawIntrinsicAxisJet_contDiffOn G j).continuousOn.comp hq
    (fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hTlt⟩, mem_univ _⟩)
  apply h.congr
  intro p hp
  exact raw_intrinsic_jet_eq_original G P hrotation j ⟨hp.1.1, hp.1.2.trans_lt hTlt⟩ p.2

end PoincareConjecture.M35.Uniqueness
