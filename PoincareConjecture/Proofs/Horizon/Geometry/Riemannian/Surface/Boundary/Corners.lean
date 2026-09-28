import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.FrameAngle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem triangle_corner_angles
    (g : RiemannianMetric 2 S) (x : S) {e₁ e₂ Y : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0) {r : ℝ} (hr : 0 < r)
    (hY : 0 < g.inner x Y e₂) :
    let T := (Real.sqrt (g.inner x Y Y))⁻¹ • Y
    let V := Y - r • e₁
    let W := (Real.sqrt (g.inner x V V))⁻¹ • V
    let α := Real.arccos (g.inner x T e₁)
    let β := Real.arccos (g.inner x W e₁)
    0 < α ∧ α < β ∧ β < Real.pi ∧
      T = Real.cos α • e₁ + Real.sin α • e₂ ∧
      W = Real.cos β • e₁ + Real.sin β • e₂ ∧
      Real.arccos (g.inner x e₁ W) = β ∧
      Real.arccos (g.inner x W (-T)) = Real.pi + α - β ∧
      Real.arccos (g.inner x (-T) e₁) = Real.pi - α := by
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := Y - r • e₁
  have hV₂ : g.inner x V e₂ = g.inner x Y e₂ := by
    simp [V, horth]
  have hYne : Y ≠ 0 := by intro hz; simp [hz] at hY
  have hVne : V ≠ 0 := by intro hz; simp [hz] at hV₂; linarith
  have hqY : 0 < g.inner x Y Y := real_inner_self_pos.mpr hYne
  have hqV : 0 < g.inner x V V := real_inner_self_pos.mpr hVne
  let a := (Real.sqrt (g.inner x Y Y))⁻¹
  let b := (Real.sqrt (g.inner x V V))⁻¹
  let T := a • Y
  let W := b • V
  let α := Real.arccos (g.inner x T e₁)
  let β := Real.arccos (g.inner x W e₁)
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hqY)
  have hb : 0 < b := inv_pos.mpr (Real.sqrt_pos.mpr hqV)
  have huT : g.inner x T T = 1 := g.inner_normalize_eq_one x Y hqY
  have huW : g.inner x W W = 1 := g.inner_normalize_eq_one x V hqV
  have hT₂ : g.inner x T e₂ = a * g.inner x Y e₂ := by simp [T]
  have hW₂ : g.inner x W e₂ = b * g.inner x Y e₂ := by simp [W, hV₂]
  have hpT : 0 < g.inner x T e₂ := by rw [hT₂]; exact mul_pos ha hY
  have hpW : 0 < g.inner x W e₂ := by rw [hW₂]; exact mul_pos hb hY
  obtain ⟨hα, hT⟩ := g.unitField_eq_cos_sin_arccos x he₁ he₂ horth huT hpT
  obtain ⟨hβ, hW⟩ := g.unitField_eq_cos_sin_arccos x he₁ he₂ horth huW hpW
  have hdet : 0 < g.inner x T e₁ * g.inner x W e₂ -
      g.inner x T e₂ * g.inner x W e₁ := by
    have heq : g.inner x T e₁ * g.inner x W e₂ -
        g.inner x T e₂ * g.inner x W e₁ = a * b * r * g.inner x Y e₂ := by
      simp only [T, W, V, map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul,
        he₁, horth]
      ring
    rw [heq]
    exact mul_pos (mul_pos (mul_pos ha hb) hr) hY
  have hlt : α < β := Surface.arccos_lt_arccos_of_unit_det_pos
    ((g.inner_self_eq_frameCoordinates_sq x he₁ he₂ horth T).symm.trans huT)
    ((g.inner_self_eq_frameCoordinates_sq x he₁ he₂ horth W).symm.trans huW)
    hpT hpW hdet
  have hnT : -T = Real.cos (Real.pi + α) • e₁ + Real.sin (Real.pi + α) • e₂ := by
    rw [hT]
    change -(Real.cos α • e₁ + Real.sin α • e₂) = _
    simp only [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi, zero_mul,
      zero_add, sub_zero, neg_one_mul, neg_smul, neg_add_rev]
    exact add_comm _ _
  refine ⟨hα.1, hlt, hβ.2, hT, hW, ?_, ?_, ?_⟩
  · have h := g.arccos_inner_of_angle_sub x he₁ he₂ horth
      (show e₁ = Real.cos 0 • e₁ + Real.sin 0 • e₂ by simp) hW
      (show β - 0 ∈ Icc 0 Real.pi by constructor <;> linarith [hβ.1, hβ.2])
    simpa only [sub_zero] using h
  · exact g.arccos_inner_of_angle_sub x he₁ he₂ horth hW hnT
      (by constructor <;> linarith [hα.1, hβ.2])
  · have h := g.arccos_inner_of_angle_sub x he₁ he₂ horth hnT
      (show e₁ = Real.cos (2 * Real.pi) • e₁ + Real.sin (2 * Real.pi) • e₂ by simp)
      (show 2 * Real.pi - (Real.pi + α) ∈ Icc 0 Real.pi by
        constructor <;> linarith [hα.1, hα.2])
    convert h using 1
    ring

end PoincareConjecture.RiemannianMetric
