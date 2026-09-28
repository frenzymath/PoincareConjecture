import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.CurvatureDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem inner_self_eq_frameCoordinates_sq
    (g : RiemannianMetric 2 S) (x : S) {e₁ e₂ : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0) (v : TangentSpace (𝓡 2) x) :
    g.inner x v v = (g.inner x v e₁) ^ 2 + (g.inner x v e₂) ^ 2 := by
  have h := LeviCivitaData.gramDet_eq_frameDet_sq g x he₁ he₂ horth v e₁
  simp only [he₁, horth, mul_one, mul_zero, zero_sub, neg_sq] at h
  linarith

theorem eq_frameCoordinates_smul
    (g : RiemannianMetric 2 S) (x : S) {e₁ e₂ : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0) (v : TangentSpace (𝓡 2) x) :
    v = g.inner x v e₁ • e₁ + g.inner x v e₂ • e₂ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let r := v - (g.inner x v e₁ • e₁ + g.inner x v e₂ • e₂)
  have horth' : g.inner x e₂ e₁ = 0 := by rw [g.symm]; exact horth
  have hr₁ : g.inner x r e₁ = 0 := by
    simp [r, he₁, horth']
  have hr₂ : g.inner x r e₂ = 0 := by
    simp [r, he₂, horth]
  have hr : g.inner x r r = 0 := by
    rw [g.inner_self_eq_frameCoordinates_sq x he₁ he₂ horth r, hr₁, hr₂]
    norm_num
  have hz : r = 0 := inner_self_eq_zero.mp hr
  exact sub_eq_zero.mp hz

theorem inner_eq_frameCoordinates
    (g : RiemannianMetric 2 S) (x : S) {e₁ e₂ : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0) (v w : TangentSpace (𝓡 2) x) :
    g.inner x v w = g.inner x v e₁ * g.inner x w e₁ +
      g.inner x v e₂ * g.inner x w e₂ := by
  conv_lhs => rw [g.eq_frameCoordinates_smul x he₁ he₂ horth w]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

theorem aligned_frame_coordinates
    (g : RiemannianMetric 2 S) (x : S) {e₁ e₂ X Y : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (horth : g.inner x e₁ e₂ = 0)
    (halign : e₁ = (Real.sqrt (g.inner x X X))⁻¹ • X)
    (hdet : 0 < g.inner x X e₁ * g.inner x Y e₂ -
      g.inner x X e₂ * g.inner x Y e₁) :
    0 < Real.sqrt (g.inner x X X) ∧
      X = Real.sqrt (g.inner x X X) • e₁ ∧
      g.inner x X e₂ = 0 ∧ 0 < g.inner x Y e₂ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hXne : X ≠ 0 := by intro hz; simp [hz] at hdet
  have hs : 0 < Real.sqrt (g.inner x X X) :=
    Real.sqrt_pos.mpr (real_inner_self_pos.mpr hXne)
  have hXeq : X = Real.sqrt (g.inner x X X) • e₁ := by
    rw [halign]
    simp [smul_smul, hs.ne']
  have hX₁ : g.inner x X e₁ = Real.sqrt (g.inner x X X) := by
    conv_lhs => rw [hXeq]
    simp only [map_smul, smul_apply, smul_eq_mul, he₁, mul_one]
  have hX₂ : g.inner x X e₂ = 0 := by
    rw [hXeq]
    simp only [map_smul, smul_apply, smul_eq_mul, horth, mul_zero]
  rw [hX₁, hX₂, zero_mul, sub_zero] at hdet
  exact ⟨hs, hXeq, hX₂, (mul_pos_iff_of_pos_left hs).mp hdet⟩

end PoincareConjecture.RiemannianMetric
