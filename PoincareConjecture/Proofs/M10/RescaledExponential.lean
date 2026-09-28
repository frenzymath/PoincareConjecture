import PoincareConjecture.Proofs.M10.EndpointCoordinates
import PoincareConjecture.Proofs.M10.MetricCoordinates
import PoincareConjecture.Proofs.M10.RescaledSource
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


noncomputable def rescaledExponential (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) (y : EuclideanSpace ℝ (Fin n)) : M :=
  G.gamma ((2 * Real.sqrt τ)⁻¹ • metricCoordinates (F.metric T) p y) τ

set_option backward.isDefEq.respectTransparency false in

theorem rescaledExponential_mdifferentiableAt (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) (y : EuclideanSpace ℝ (Fin n)) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (fun s ↦ rescaledExponential G s y) τ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let Z := fun s : ℝ ↦ (2 * Real.sqrt s)⁻¹ • metricCoordinates (F.metric T) p y
  have hp := (inverse_double_sqrt_smul_hasDerivAt (metricCoordinates (F.metric T) p y) hτ).prodMk
    (hasDerivAt_id τ)
  have hp' : MDifferentiableAt (𝓘(ℝ, ℝ))
      ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) (fun s ↦ (Z s, s)) τ := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hp.differentiableAt.mdifferentiableAt
  have hγ := G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    (show (Z τ, τ) ∈ univ ×ˢ Ioo 0 τmax from ⟨mem_univ _, hτ, hmax⟩))
  have hc := (hγ.mdifferentiableAt (by simp)).comp (f := fun s ↦ (Z s, s)) τ hp'
  exact hc

set_option backward.isDefEq.respectTransparency false in

theorem rescaledExponential_velocity_eq_zero (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hvelocity : ∀ Z : TangentSpace (𝓡 n) p,
      curveVelocity (G.gamma Z) τ = G.toLExponentialFamily.sliceDifferential Z τ
        ((2 * τ)⁻¹ • Z)) (y : EuclideanSpace ℝ (Fin n)) :
    curveVelocity (n := n) (fun s ↦ rescaledExponential G s y) τ = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let Z := fun s : ℝ ↦ (2 * Real.sqrt s)⁻¹ • metricCoordinates (F.metric T) p y
  let z := (Z τ, τ)
  let q := G.gamma z.1 z.2
  have hz : z ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source :=
    mem_chart_source _ _
  have hp := (inverse_double_sqrt_smul_hasDerivAt (metricCoordinates (F.metric T) p y) hτ).prodMk
    (hasDerivAt_id τ)
  have hd := ((endpointCoordinates_contDiffAt G q z hz hq).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt (f := fun s ↦ (Z s, s)) τ hp
  have heval : fderiv ℝ (endpointCoordinates G q) z (-(2 * τ)⁻¹ • Z τ, 1) = 0 := by
    rw [show (-(2 * τ)⁻¹ • Z τ, (1 : ℝ)) =
      (-(2 * τ)⁻¹ • Z τ, 0) + (0, 1) by simp, map_add,
      endpointCoordinates_horizontal G q z hz hq,
      endpointCoordinates_time G q z hz hq, hvelocity]
    let L := (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q).continuousLinearMapAt ℝ q
    let D := G.toLExponentialFamily.sliceDifferential (Z τ) τ
    change (L.comp D) (-(2 * τ)⁻¹ • Z τ) + (L.comp D) ((2 * τ)⁻¹ • Z τ) = 0
    simp only [neg_smul, map_neg, neg_add_cancel]
  have hzero := (hd.congr_deriv heval).deriv
  have hγ := rescaledExponential_mdifferentiableAt G hτ hmax y
  change fderiv ℝ ((extChartAt (𝓡 n) q) ∘ (fun s ↦ rescaledExponential G s y)) τ 1 = 0 at hzero
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (f := fun s ↦ rescaledExponential G s y) τ
      (mdifferentiableAt_extChartAt (I := 𝓡 n) hq) hγ] at hzero
  change (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q) q)
    (curveVelocity (fun s ↦ rescaledExponential G s y) τ) = 0 at hzero
  rw [mfderiv_extChartAt_self] at hzero
  exact hzero

set_option backward.isDefEq.respectTransparency false in

theorem rescaledExponential_eq_of_radial_velocity
    (G : LExponentialGeometry F T τmax p) {b : ℝ} (hbmax : b ≤ τmax)
    (e : Diffeomorph (𝓡 n) (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞)
    (hvelocity : ∀ s ∈ Ioo 0 b, ∀ Z : TangentSpace (𝓡 n) p,
      curveVelocity (G.gamma Z) s = G.toLExponentialFamily.sliceDifferential Z s
        ((2 * s)⁻¹ • Z))
    (y : EuclideanSpace ℝ (Fin n)) {t c : ℝ} (ht : t ∈ Ioo 0 b) (hc : c ∈ Ioo 0 b) :
    rescaledExponential G t y = rescaledExponential G c y := by
  have hd (s : ℝ) (hs : s ∈ Ioo 0 b) :
      HasDerivAt (fun r ↦ e (rescaledExponential G r y)) 0 s := by
    have hγ := rescaledExponential_mdifferentiableAt G hs.1 (hs.2.trans_le hbmax) y
    have he := (e.contMDiffAt (x := rescaledExponential G s y)).mdifferentiableAt (by simp)
    have hcomp := he.comp (f := fun r ↦ rescaledExponential G r y) s hγ
    apply hcomp.differentiableAt.hasDerivAt.congr_deriv
    change fderiv ℝ (e ∘ (fun r ↦ rescaledExponential G r y)) s 1 = 0
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (f := fun r ↦ rescaledExponential G r y) s he hγ]
    change mfderiv (𝓡 n) (𝓡 n) e (rescaledExponential G s y)
      (curveVelocity (fun r ↦ rescaledExponential G r y) s) = 0
    rw [rescaledExponential_velocity_eq_zero G hs.1 (hs.2.trans_le hbmax) (hvelocity s hs) y,
      map_zero]
  apply e.injective
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 b).isPreconnected
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hd s hs).deriv) ht hc

end PoincareConjecture.M10
