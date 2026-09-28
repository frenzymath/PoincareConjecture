import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.CurvatureDensity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Area
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Stokes.Triangle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField Bundle
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

private theorem contMDiffAt_planar_const (v : ℝ × ℝ) (p : ℝ × ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ × ℝ)) ∞
      (fun y => TotalSpace.mk' (ℝ × ℝ) y (E := TangentSpace 𝓘(ℝ, ℝ × ℝ)) v) p := by
  rw [contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using
    (contMDiffAt_const (I := 𝓘(ℝ, ℝ × ℝ)) (I' := 𝓘(ℝ, ℝ × ℝ)) (c := v))⟩

theorem contMDiffAt_chartField
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {x : S} (hx : x ∈ e.source) (v : ℝ × ℝ) :
    ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (T% (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v))) x := by
  have hD : e.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  exact (contMDiffAt_planar_const v (e x)).mpullback_vectorField_preimage
    (he.contMDiffAt (e.open_source.mem_nhds hx)) ⟨hD.mfderiv hx, rfl⟩ (by simp)

private theorem mlieBracket_chartField
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    {x : S} (hx : x ∈ e.source) (v w : ℝ × ℝ) :
    mlieBracket (𝓡 2)
      (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v))
      (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => w)) x = 0 := by
  let : IsManifold (𝓡 2) (minSmoothness ℝ 2) S := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 2) 2 S)
  have hb := mpullback_mlieBracket
    ((contMDiffAt_planar_const v (e x)).mdifferentiableAt (by simp))
    ((contMDiffAt_planar_const w (e x)).mdifferentiableAt (by simp))
    (he.contMDiffAt (e.open_source.mem_nhds hx))
    (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  rw [← hb]
  have hzero : mlieBracket 𝓘(ℝ, ℝ × ℝ)
      (fun _ : ℝ × ℝ => v) (fun _ : ℝ × ℝ => w) = 0 := by
    funext p
    simp only [mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
    simp +instances
  rw [hzero]
  simp [mpullback]

theorem exists_aligned_positive_chart_frame
    (g : RiemannianMetric 2 S) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target) :
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    ∃ e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0) ∧
      (∀ x ∈ e.source, 0 <
        g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x)) ∧
      e₁ = fun x => (Real.sqrt (g.inner x (X x) (X x)))⁻¹ • X x := by
  apply g.exists_aligned_orthonormal_frame_of_independent_fields
    (fun x hx => (contMDiffAt_chartField e he hei hx (1, 0)).contMDiffWithinAt)
    (fun x hx => (contMDiffAt_chartField e he hei hx (0, 1)).contMDiffWithinAt)
  intro x hx
  have hD : e.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e x).IsInvertible :=
    ⟨hD.mfderiv hx, rfl⟩
  apply LinearIndependent.pair_iff.mpr
  intro a b hab
  have h := congrArg (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e x) hab
  simp only [mpullback, map_add, map_smul, map_zero, hinv.self_apply_inverse] at h
  change a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) = 0 at h
  exact ⟨by simpa using congrArg Prod.fst h, by simpa using congrArg Prod.snd h⟩

theorem exists_positive_chart_frame
    (g : RiemannianMetric 2 S) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target) :
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    ∃ e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0) ∧
      ∀ x ∈ e.source, 0 <
        g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x) := by
  obtain ⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp, _⟩ :=
    exists_aligned_positive_chart_frame g e he hei
  exact ⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp⟩

omit [IsManifold (𝓡 2) ∞ S] in

theorem chartField_symm_apply
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {p : ℝ × ℝ} (hp : p ∈ e.target) (v : ℝ × ℝ) :
    mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) (e.symm p) =
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) e.symm p v := by
  have hD : e.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (e.symm p)).IsInvertible :=
    ⟨hD.mfderiv (e.map_target hp), rfl⟩
  apply hD.mfderiv_injective (e.map_target hp)
  simp only [mpullback, hinv.self_apply_inverse]
  have h := congrArg (fun L => L v) (hD.comp_symm_deriv hp)
  exact h.symm

omit [IsManifold (𝓡 2) ∞ S] in
private theorem fderiv_chart_scalar
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {p : ℝ × ℝ} (hp : p ∈ e.target) {f : S → ℝ}
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (e.symm p)) (v : ℝ × ℝ) :
    fderiv ℝ (f ∘ e.symm) p v =
      mvfderiv (𝓡 2) f (e.symm p)
        (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) (e.symm p)) := by
  rw [chartField_symm_apply e he hei hp]
  have h := congrArg (fun L => L v) (mvfderiv_comp p hf
    ((hei.contMDiffAt (e.open_target.mem_nhds hp)).mdifferentiableAt (by simp)))
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] at h
  exact h

theorem scalarCurvature_frameDet_eq_chart_curl
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source)
    (hunit₁ : ∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0)
    {p : ℝ × ℝ} (hp : p ∈ e.target) :
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let x := e.symm p
    D.scalarCurvature x *
        (g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x)) =
      -2 * (fderiv ℝ (D.surfaceConnectionForm e₁ e₂ Y ∘ e.symm) p (1, 0) -
        fderiv ℝ (D.surfaceConnectionForm e₁ e₂ X ∘ e.symm) p (0, 1)) := by
  dsimp only
  have hx := e.map_target hp
  have hX := contMDiffAt_chartField e he hei hx (1, 0)
  have hY := contMDiffAt_chartField e he hei hx (0, 1)
  have h₁ := he₁.contMDiffAt (e.open_source.mem_nhds hx)
  have h₂ := he₂.contMDiffAt (e.open_source.mem_nhds hx)
  have hωX := (D.contMDiffAt_inner_covariantDerivativeOnFields hX h₁ h₂).mdifferentiableAt
    (by simp)
  have hωY := (D.contMDiffAt_inner_covariantDerivativeOnFields hY h₁ h₂).mdifferentiableAt
    (by simp)
  unfold surfaceConnectionForm
  rw [fderiv_chart_scalar e he hei hp hωY, fderiv_chart_scalar e he hei hp hωX]
  have h := D.scalarCurvature_mul_frameDet_eq_connectionForm e.open_source hx
    he₁ he₂ hunit₁ hunit₂ horth hX hY
  simp only [surfaceConnectionForm, covariantDerivativeOnFields,
    mlieBracket_chartField e he hx, map_zero, zero_apply, sub_zero] at h
  exact h

private theorem contDiffOn_chartConnectionForm
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source)
    (v : ℝ × ℝ) :
    ContDiffOn ℝ ∞
      (D.surfaceConnectionForm e₁ e₂
        (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v)) ∘ e.symm) e.target := by
  intro p hp
  have hx := e.map_target hp
  have hX := contMDiffAt_chartField e he hei hx v
  have h₁ := he₁.contMDiffAt (e.open_source.mem_nhds hx)
  have h₂ := he₂.contMDiffAt (e.open_source.mem_nhds hx)
  have hω := D.contMDiffAt_inner_covariantDerivativeOnFields hX h₁ h₂
  have h := contMDiffAt_iff_contDiffAt.mp
    (hω.comp p (hei.contMDiffAt (e.open_target.mem_nhds hp)))
  exact h.contDiffWithinAt

theorem integral_scalarCurvature_frameDet_triangle
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source)
    (hunit₁ : ∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0)
    (htriangle : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆ e.target) :
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let P := D.surfaceConnectionForm e₁ e₂ X ∘ e.symm
    let Q := D.surfaceConnectionForm e₁ e₂ Y ∘ e.symm
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u),
      let x := e.symm (u, v)
      D.scalarCurvature x *
        (g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x))) =
      -2 * ((∫ u in (0 : ℝ)..1, P (u, 0)) -
        (∫ u in (0 : ℝ)..1, P (u, 1 - u) - Q (u, 1 - u)) -
        ∫ v in (0 : ℝ)..1, Q (0, v)) := by
  dsimp only
  let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
  let P := D.surfaceConnectionForm e₁ e₂ X ∘ e.symm
  let Q := D.surfaceConnectionForm e₁ e₂ Y ∘ e.symm
  have hstokes := PoincareConjecture.Surface.integral_curl_triangle_of_contDiffOn P Q
    e.open_target htriangle
    ((D.contDiffOn_chartConnectionForm e he hei he₁ he₂ (1, 0)).of_le (by simp))
    ((D.contDiffOn_chartConnectionForm e he hei he₁ he₂ (0, 1)).of_le (by simp))
  have hi : (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u),
      let x := e.symm (u, v)
      D.scalarCurvature x *
        (g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x))) =
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u),
        -2 * (fderiv ℝ Q (u, v) (1, 0) - fderiv ℝ P (u, v) (0, 1)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (sub_nonneg.mpr hu.2)] at hv
    exact D.scalarCurvature_frameDet_eq_chart_curl e he hei he₁ he₂
      hunit₁ hunit₂ horth (htriangle ⟨hu.1, hv.1, by linarith [hv.2]⟩)
  change _ = -2 * ((∫ u in (0 : ℝ)..1, P (u, 0)) -
    (∫ u in (0 : ℝ)..1, P (u, 1 - u) - Q (u, 1 - u)) -
    ∫ v in (0 : ℝ)..1, Q (0, v))
  rw [hi]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [hstokes]

variable [MeasurableSpace S] [BorelSpace S] [T3Space S]

theorem integral_scalarCurvature_chartTriangle
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source)
    (hunit₁ : ∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0)
    (hpos : ∀ x ∈ e.source,
      let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
      let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
      0 < g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
        g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x))
    (htriangle : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆ e.target) :
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let P := D.surfaceConnectionForm e₁ e₂ X ∘ e.symm
    let Q := D.surfaceConnectionForm e₁ e₂ Y ∘ e.symm
    (∫ x in e.symm '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1},
      D.scalarCurvature x ∂g.volumeMeasure) =
      -2 * ((∫ u in (0 : ℝ)..1, P (u, 0)) -
        (∫ u in (0 : ℝ)..1, P (u, 1 - u) - Q (u, 1 - u)) -
        ∫ v in (0 : ℝ)..1, Q (0, v)) := by
  dsimp only
  let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
  have hdensity (p : ℝ × ℝ) (hp : p ∈ e.target) :
      g.planarVolumeDensity e.symm p =
        g.inner (e.symm p) (X (e.symm p)) (e₁ (e.symm p)) *
          g.inner (e.symm p) (Y (e.symm p)) (e₂ (e.symm p)) -
        g.inner (e.symm p) (X (e.symm p)) (e₂ (e.symm p)) *
          g.inner (e.symm p) (Y (e.symm p)) (e₁ (e.symm p)) := by
    have hx := e.map_target hp
    have h := g.planarVolumeDensity_eq_abs_frameDet e.symm p
      (e₁ (e.symm p)) (e₂ (e.symm p)) (hunit₁ _ hx) (hunit₂ _ hx) (horth _ hx)
    dsimp only at h
    rw [← chartField_symm_apply e he hei hp (1, 0),
      ← chartField_symm_apply e he hei hp (0, 1)] at h
    rw [abs_of_pos (hpos _ hx)] at h
    exact h
  rw [g.integral_image_eq_integral_planar_density e.symm hei he
    D.continuous_scalarCurvature.continuousOn
    PoincareConjecture.Surface.isCompact_standardTriangle.measurableSet htriangle]
  refine (PoincareConjecture.Surface.integral_standardTriangle_eq_iterated
    (fun p => D.scalarCurvature (e.symm p) * g.planarVolumeDensity e.symm p)
    (((D.continuous_scalarCurvature.comp_continuousOn e.symm.continuousOn).mul
      (g.continuousOn_planarVolumeDensity e.symm hei he)).mono htriangle)).trans ?_
  calc
    _ = ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u),
        let x := e.symm (u, v)
        D.scalarCurvature x *
          (g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
            g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le (sub_nonneg.mpr hu.2)] at hv
      exact congrArg (D.scalarCurvature (e.symm (u, v)) * ·)
        (hdensity (u, v) (htriangle ⟨hu.1, hv.1, by linarith [hv.2]⟩))
    _ = _ := D.integral_scalarCurvature_frameDet_triangle e he hei he₁ he₂
      hunit₁ hunit₂ horth htriangle

theorem exists_frame_integral_scalarCurvature_chartTriangle
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (htriangle : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆ e.target) :
    ∃ e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0) ∧
      (let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
       let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
       let P := D.surfaceConnectionForm e₁ e₂ X ∘ e.symm
       let Q := D.surfaceConnectionForm e₁ e₂ Y ∘ e.symm
       (∫ x in e.symm '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1},
         D.scalarCurvature x ∂g.volumeMeasure) =
         -2 * ((∫ u in (0 : ℝ)..1, P (u, 0)) -
           (∫ u in (0 : ℝ)..1, P (u, 1 - u) - Q (u, 1 - u)) -
           ∫ v in (0 : ℝ)..1, Q (0, v))) := by
  obtain ⟨e₁, e₂, he₁, he₂, hunit₁, hunit₂, horth, hpos⟩ :=
    exists_positive_chart_frame g e he hei
  exact ⟨e₁, e₂, he₁, he₂, hunit₁, hunit₂, horth,
    D.integral_scalarCurvature_chartTriangle e he hei he₁ he₂
      hunit₁ hunit₂ horth hpos htriangle⟩

end PoincareConjecture.LeviCivitaData
