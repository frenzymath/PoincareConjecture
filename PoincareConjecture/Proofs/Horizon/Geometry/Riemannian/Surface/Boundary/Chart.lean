import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.FrameAngle
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Stokes.Chart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in

theorem chartField_ne_zero
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {v : ℝ × ℝ} (hv : v ≠ 0) {x : S} (hx : x ∈ e.source) :
    mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) x ≠ 0 := by
  have hD : e.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e x).IsInvertible :=
    ⟨hD.mfderiv hx, rfl⟩
  intro hzero
  have h := congrArg (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e x) hzero
  simp only [mpullback, hinv.self_apply_inverse, map_zero] at h
  exact hv h

theorem normalized_chartField_properties
    (g : RiemannianMetric 2 S) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {v : ℝ × ℝ} (hv : v ≠ 0) :
    let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v)
    let T := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
    ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) e.source ∧
      ∀ x ∈ e.source, g.inner x (T x) (T x) = 1 := by
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpos (x : S) (hx : x ∈ e.source) :
      0 < g.inner x
        (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) x)
        (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) x) :=
    real_inner_self_pos.mpr (chartField_ne_zero e he hei hv hx)
  exact ⟨g.contMDiffOn_normalize
    (fun x hx => (contMDiffAt_chartField e he hei hx v).contMDiffWithinAt) hpos,
    fun x hx => g.inner_normalize_eq_one x _ (hpos x hx)⟩

omit [IsManifold (𝓡 2) ∞ S] in

theorem mfderiv_chart_line
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (p v : ℝ × ℝ) {t : ℝ} (ht : p + t • v ∈ e.target) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun s : ℝ => e.symm (p + s • v)) t ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => e.symm (p + s • v)) t 1 =
        mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) (e.symm (p + t • v)) := by
  have hc : ContDiff ℝ ∞ (fun s : ℝ => p + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hi := hei.contMDiffAt (e.open_target.mem_nhds ht)
  refine ⟨hi.comp t hc.contMDiff.contMDiffAt, ?_⟩
  rw [chartField_symm_apply e he hei ht]
  have hd : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add p
  have h := congrArg (fun L => L 1) (mfderiv_comp t
    (hi.mdifferentiableAt (by simp)) hd.differentiableAt.mdifferentiableAt)
  dsimp only [TangentSpace] at h
  simp only [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  exact h

theorem integral_chart_edge_turning
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source)
    (hunit₁ : ∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0)
    (p v : ℝ × ℝ) (hv : v ≠ 0) {s t : ℝ}
    (hsegment : ∀ r ∈ uIcc s t, p + r • v ∈ e.target)
    (hpos : ∀ x ∈ e.source, 0 < g.inner x
      (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) x) (e₂ x)) :
    let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v)
    let T := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
    let θ := fun x => Real.arccos (g.inner x (T x) (e₁ x))
    let γ := fun r : ℝ => e.symm (p + r • v)
    (∫ r in s..t, D.surfaceTurningForm e₁ e₂ T V (γ r)) =
      (∫ r in s..t, D.surfaceConnectionForm e₁ e₂ V (γ r)) + θ (γ t) - θ (γ s) := by
  dsimp only
  let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v)
  let T := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
  let γ := fun r : ℝ => e.symm (p + r • v)
  have hVpos (x : S) (hx : x ∈ e.source) : 0 < g.inner x (V x) (V x) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact real_inner_self_pos.mpr (chartField_ne_zero e he hei hv hx)
  obtain ⟨hT, huT⟩ := normalized_chartField_properties g e he hei hv
  have hTp (x : S) (hx : x ∈ e.source) : 0 < g.inner x (T x) (e₂ x) := by
    dsimp only [T]
    simp only [map_smul, smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (hVpos x hx))) (hpos x hx)
  have hθ := g.contMDiffOn_arccos_frameCoordinate he₁ hT hunit₁ hunit₂ horth huT hTp
  have hang (x : S) (hx : x ∈ e.source) :=
    (g.unitField_eq_cos_sin_arccos x (hunit₁ x hx) (hunit₂ x hx) (horth x hx)
      (huT x hx) (hTp x hx)).2
  have hint := D.integral_unitField_sub_connectionForm_of_angle e.open_source he₁ he₂ hT
    hunit₁ hunit₂ horth hθ hang
    (fun r hr => (mfderiv_chart_line e he hei p v (hsegment r hr)).1)
    (fun r hr => e.map_target (hsegment r hr))
  have hdiff : (∫ r in s..t, D.surfaceTurningForm e₁ e₂ T V (γ r) -
      D.surfaceConnectionForm e₁ e₂ V (γ r)) =
      Real.arccos (g.inner (γ t) (T (γ t)) (e₁ (γ t))) -
        Real.arccos (g.inner (γ s) (T (γ s)) (e₁ (γ s))) := by
    refine (intervalIntegral.integral_congr (fun r hr => ?_)).trans hint
    rw [(mfderiv_chart_line e he hei p v (hsegment r hr)).2]
    rfl
  have hV : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V) e.source :=
    fun x hx => (contMDiffAt_chartField e he hei hx v).contMDiffWithinAt
  have hγ : ContinuousOn γ (uIcc s t) := fun r hr =>
    (mfderiv_chart_line e he hei p v (hsegment r hr)).1.continuousAt.continuousWithinAt
  have hmaps : MapsTo γ (uIcc s t) e.source := fun r hr => e.map_target (hsegment r hr)
  have hκ := ((D.contMDiffOn_surfaceTurningForm e.open_source he₁ he₂ hT hV).continuousOn.comp
    hγ hmaps).intervalIntegrable (μ := MeasureTheory.volume)
  have hω : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (D.surfaceConnectionForm e₁ e₂ V) e.source := by
    intro x hx
    have hn := e.open_source.mem_nhds hx
    exact (D.contMDiffAt_inner_covariantDerivativeOnFields (hV.contMDiffAt hn)
      (he₁.contMDiffAt hn) (he₂.contMDiffAt hn)).contMDiffWithinAt
  have hiω := (hω.continuousOn.comp hγ hmaps).intervalIntegrable (μ := MeasureTheory.volume)
  have hsub := intervalIntegral.integral_sub
    (f := fun r => D.surfaceTurningForm e₁ e₂ T V (γ r))
    (g := fun r => D.surfaceConnectionForm e₁ e₂ V (γ r)) hκ hiω
  rw [hsub] at hdiff
  linarith

end PoincareConjecture.LeviCivitaData
