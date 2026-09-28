import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.FrameCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.FrameChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

noncomputable def surfaceTurningForm (D : LeviCivitaData g)
    (e₁ e₂ T V : (x : S) → TangentSpace (𝓡 2) x) (x : S) : ℝ :=
  g.inner x (D.connection T x (V x))
    (-g.inner x (T x) (e₂ x) • e₁ x + g.inner x (T x) (e₁ x) • e₂ x)

theorem contMDiffOn_surfaceTurningForm (D : LeviCivitaData g)
    {U : Set S} (hU : IsOpen U)
    {e₁ e₂ T V : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) U)
    (hV : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V) U) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (D.surfaceTurningForm e₁ e₂ T V) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : S → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  have hN := ((hT.inner_bundle he₂).neg.smul_section he₁).add_section
    ((hT.inner_bundle he₁).smul_section he₂)
  intro x hx
  have hn := hU.mem_nhds hx
  exact (D.contMDiffAt_inner_covariantDerivativeOnFields (hV.contMDiffAt hn)
    (hT.contMDiffAt hn) (hN.contMDiffAt hn)).contMDiffWithinAt

theorem integral_unitField_sub_connectionForm_of_angle
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U)
    {e₁ e₂ T : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) U)
    (hunit₁ : ∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0)
    {θ : S → ℝ} (hθ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ θ U)
    (hangle : ∀ x ∈ U, T x = Real.cos (θ x) • e₁ x + Real.sin (θ x) • e₂ x)
    {γ : ℝ → S} {s t : ℝ}
    (hγ : ∀ x ∈ uIcc s t, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ x)
    (hγU : MapsTo γ (uIcc s t) U) :
    let N := fun x => -g.inner x (T x) (e₂ x) • e₁ x +
      g.inner x (T x) (e₁ x) • e₂ x
    (∫ x in s..t,
      g.inner (γ x) (D.connection T (γ x)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1)) (N (γ x)) -
        g.inner (γ x) (D.connection e₁ (γ x)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1)) (e₂ (γ x))) =
      θ (γ t) - θ (γ s) := by
  dsimp only
  have hint := D.integral_connectionForm_rotate_angle hU he₁ he₂ hunit₁ hunit₂
    horth hθ hγ hγU
  refine (intervalIntegral.integral_congr (fun x hx => ?_)).trans hint
  have hxu := hγU hx
  have hn := hU.mem_nhds hxu
  have h₁ := (he₁.contMDiffAt hn).mdifferentiableAt (by simp)
  have h₂ := (he₂.contMDiffAt hn).mdifferentiableAt (by simp)
  have hθx := hθ.contMDiffAt hn
  have hc := (Real.contDiff_cos.contDiffAt.comp_contMDiffAt hθx).mdifferentiableAt (by simp)
  have hs := (Real.contDiff_sin.contDiffAt.comp_contMDiffAt hθx).mdifferentiableAt (by simp)
  have hrot := mdifferentiableAt_add_section (hc.smul_section h₁) (hs.smul_section h₂)
  have heq : T =ᶠ[𝓝 (γ x)] (Real.cos ∘ θ) • e₁ + (Real.sin ∘ θ) • e₂ :=
    Filter.mem_of_superset hn (fun y hy => hangle y hy)
  have hconn := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((hT.contMDiffAt hn).mdifferentiableAt (by simp)) hrot (by simp) heq
  have horth' : g.inner (γ x) (e₂ (γ x)) (e₁ (γ x)) = 0 := by
    rw [g.symm, horth (γ x) hxu]
  have hcT : g.inner (γ x) (T (γ x)) (e₁ (γ x)) = Real.cos (θ (γ x)) := by
    rw [hangle (γ x) hxu]
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hunit₁ (γ x) hxu, horth', mul_one, mul_zero, add_zero]
  have hsT : g.inner (γ x) (T (γ x)) (e₂ (γ x)) = Real.sin (θ (γ x)) := by
    rw [hangle (γ x) hxu]
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hunit₂ (γ x) hxu, horth (γ x) hxu, mul_one, mul_zero, zero_add]
  rw [hconn, hcT, hsT]
  rfl

theorem exists_angle_integral_unitField
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U)
    {e₁ e₂ T : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) U)
    (hunit₁ : ∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0)
    (hunitT : ∀ x ∈ U, g.inner x (T x) (T x) = 1)
    {I : Set ℝ} (hI : IsOpen I) (hconv : Convex ℝ I) (hne : I.Nonempty)
    {γ : ℝ → S} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ I)
    (hγU : MapsTo γ I U) {s t : ℝ} (hst : uIcc s t ⊆ I) :
    let a := fun x => g.inner x (T x) (e₁ x)
    let b := fun x => g.inner x (T x) (e₂ x)
    let N := (-b) • e₁ + a • e₂
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ ∞ θ I ∧
      (∀ x ∈ I, T (γ x) = Real.cos (θ x) • e₁ (γ x) +
        Real.sin (θ x) • e₂ (γ x)) ∧
      (∫ x in s..t,
        g.inner (γ x) (D.connection T (γ x)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1)) (N (γ x)) -
          g.inner (γ x) (D.connection e₁ (γ x)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1)) (e₂ (γ x))) = θ t - θ s := by
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : S → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  let a := fun x => g.inner x (T x) (e₁ x)
  let b := fun x => g.inner x (T x) (e₂ x)
  have ha : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ a U := hT.inner_bundle he₁
  have hb : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ b U := hT.inner_bundle he₂
  have hab (x : S) (hx : x ∈ U) : (a x) ^ 2 + (b x) ^ 2 = 1 :=
    (g.inner_self_eq_frameCoordinates_sq x (hunit₁ x hx) (hunit₂ x hx)
      (horth x hx) (T x)).symm.trans (hunitT x hx)
  have hdecomp (x : S) (hx : x ∈ U) : T x = (a • e₁ + b • e₂) x :=
    g.eq_frameCoordinates_smul x (hunit₁ x hx) (hunit₂ x hx) (horth x hx) (T x)
  obtain ⟨θ, hθ, hcoeff, hint⟩ := D.exists_angle_integral_connectionForm_rotate hU
    he₁ he₂ hunit₁ hunit₂ horth ha hb hab hI hconv hne hγ hγU hst
  refine ⟨θ, hθ, ?_, ?_⟩
  · intro x hx
    rw [(hcoeff x hx).1, (hcoeff x hx).2]
    exact hdecomp (γ x) (hγU hx)
  · refine (intervalIntegral.integral_congr (fun x hx => ?_)).trans hint
    have hn := hU.mem_nhds (hγU (hst hx))
    have hT' := (hT.contMDiffAt hn).mdifferentiableAt (by simp)
    have he₁' := (he₁.contMDiffAt hn).mdifferentiableAt (by simp)
    have he₂' := (he₂.contMDiffAt hn).mdifferentiableAt (by simp)
    have ha' := (ha.contMDiffAt hn).mdifferentiableAt (by simp)
    have hb' := (hb.contMDiffAt hn).mdifferentiableAt (by simp)
    have hrot := mdifferentiableAt_add_section
      (ha'.smul_section he₁') (hb'.smul_section he₂')
    have heq : T =ᶠ[𝓝 (γ x)] a • e₁ + b • e₂ :=
      Filter.mem_of_superset hn (fun y hy => hdecomp y hy)
    have hconn := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hT' hrot (by simp) heq
    rw [hconn]

end PoincareConjecture.LeviCivitaData
