import PoincareConjecture.Proofs.M35.RawFlow.ArclengthJointSmooth
import PoincareConjecture.Proofs.M35.RawFlow.Completeness










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)



noncomputable def rawInverseRadius (t s : ℝ) : ℝ :=
  if ht : t ∈ Ico 0 G.lifetime then
    (radialArclengthOrderIso (G.flow.metric t) (hrotation t ht) (G.complete P ht)).symm s
  else 0

theorem rawInverseRadius_eq {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) (s : ℝ) :
    rawInverseRadius P G hrotation t s =
      (radialArclengthOrderIso (G.flow.metric t) (hrotation t ht) (G.complete P ht)).symm s := by
  simp only [rawInverseRadius, dif_pos ht]

theorem radialArclength_rawInverseRadius {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) (s : ℝ) :
    radialArclength (G.flow.metric t) (rawInverseRadius P G hrotation t s) = s := by
  rw [rawInverseRadius_eq P G hrotation ht]
  exact (radialArclengthOrderIso (G.flow.metric t) (hrotation t ht)
    (G.complete P ht)).apply_symm_apply s

theorem rawInverseRadius_radialArclength {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) (r : ℝ) :
    rawInverseRadius P G hrotation t (radialArclength (G.flow.metric t) r) = r := by
  rw [rawInverseRadius_eq P G hrotation ht]
  exact (radialArclengthOrderIso (G.flow.metric t) (hrotation t ht)
    (G.complete P ht)).symm_apply_apply r

theorem rawInverseRadius_pos {t s : ℝ} (ht : t ∈ Ico 0 G.lifetime) (hs : 0 < s) :
    0 < rawInverseRadius P G hrotation t s := by
  rw [rawInverseRadius_eq P G hrotation ht]
  exact radialArclengthOrderIso_symm_pos (G.flow.metric t) (hrotation t ht) (G.complete P ht) hs



theorem rawInverseRadius_contDiffAt {p : ℝ × ℝ} (hp : p.1 ∈ Ioo 0 G.lifetime) :
    ContDiffAt ℝ ∞ (Function.uncurry (rawInverseRadius P G hrotation)) p := by
  have hpG : p.1 ∈ Ico 0 G.lifetime := ⟨hp.1.le, hp.2⟩
  let r := rawInverseRadius P G hrotation p.1 p.2
  let H (z : (ℝ × ℝ) × ℝ) := radialArclength (G.flow.metric z.1.1) z.2 - z.1.2
  have hH : ContDiffAt ℝ ∞ H (p, r) :=
    ((raw_radialArclength_contDiffAt G (p := (p.1, r)) hp).comp (p, r)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  have hvalue : H (p, r) = 0 := by
    dsimp only [H, r]
    rw [radialArclength_rawInverseRadius P G hrotation hpG, sub_self]
  let b := Real.sqrt (axisRadialCoefficient (G.flow.metric p.1) r)
  have hb : b ≠ 0 := (Real.sqrt_pos.mpr
    (axisRadialCoefficient_pos (G.flow.metric p.1) r)).ne'
  have hpart : fderiv ℝ H (p, r) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ b := by
    have hd := (hH.differentiableAt (by simp)).hasFDerivAt.comp r
      (hasFDerivAt_prodMk_right p r)
    have hs : HasDerivAt (fun a => H (p, a)) b r :=
      (radialArclength_hasDerivAt (G.flow.metric p.1) r).sub_const p.2
    exact hd.unique hs.hasFDerivAt
  have hinv : (fderiv ℝ H (p, r) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    rw [hpart]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℝ b⁻¹)
    · apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, ContinuousLinearMap.id_apply]
      field_simp [hb]
    · apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, ContinuousLinearMap.id_apply]
      field_simp [hb]
  let q := hH.implicitFunction (by simp) hinv
  have hq : ContDiffAt ℝ ∞ q p := hH.contDiffAt_implicitFunction (by simp) hinv
  have heq : ∀ᶠ z in 𝓝 p, H (z, q z) = 0 := by
    simpa only [hvalue] using hH.eventually_apply_implicitFunction (by simp) hinv
  have htime : ∀ᶠ z : ℝ × ℝ in 𝓝 p, z.1 ∈ Ioo 0 G.lifetime :=
    continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hp)
  apply hq.congr_of_eventuallyEq
  filter_upwards [heq, htime] with z hz hzt
  have hztG : z.1 ∈ Ico 0 G.lifetime := ⟨hzt.1.le, hzt.2⟩
  apply (radialArclength_strictMono (G.flow.metric z.1)).injective
  dsimp only [Function.uncurry]
  rw [radialArclength_rawInverseRadius P G hrotation hztG]
  change radialArclength (G.flow.metric z.1) (q z) - z.2 = 0 at hz
  exact (sub_eq_zero.mp hz).symm

theorem rawInverseRadius_contDiffOn :
    ContDiffOn ℝ ∞ (Function.uncurry (rawInverseRadius P G hrotation))
      (Ioo 0 G.lifetime ×ˢ univ) :=
  fun _ hq => (rawInverseRadius_contDiffAt P G hrotation hq.1).contDiffWithinAt

end PoincareConjecture.M35.Uniqueness
