import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Matching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Critical
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Arcs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev axis : E3 := EuclideanSpace.single 2 1

open Saddle.Nested

theorem prescribed_nested_model_chart_critical
    (d : OpenPartialHomeomorph E2 S2) (hd0 : 0 ∈ d.source)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hdform : ∀ x ∈ d.source,
      height (d x) = height (d 0) - (x 0)^2 + (x 1)^2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height (d 0) = 0 := by
  let σ : Fin 2 → Real := ![-1, 1]
  have hlocal : EqOn (height ∘ d)
      (fun x => height (d 0) + ∑ i : Fin 2, σ i * (x i)^2) d.source := by
    intro x hx
    simpa [σ, Fin.sum_univ_two, sub_eq_add_neg, add_assoc] using hdform x hx
  rw [mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eqOn
    height_contMDiff d hd hdi hd0 hlocal]
  exact (Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff
    (height (d 0)) σ (by intro i; fin_cases i <;> norm_num [σ]) 0).mpr rfl

theorem exists_filled_nested_matching_with_prescribed_chart
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) - (x 0)^2 + (x 1)^2)
    (d : OpenPartialHomeomorph E2 S2) (hd0 : 0 ∈ d.source)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hdform : ∀ x ∈ d.source,
      height (d x) = height (d 0) - (x 0)^2 + (x 1)^2)
    {s : Real} (hs : 0 < s) :
    ∃ r > 0, closedBall (0 : E2) r ⊆ d.source ∧
      (∀ x ∈ closedBall (0 : E2) r, Real.sqrt s • x ∈ e.source) ∧
      ∃ T F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y : E3, F y = T (shear (3 / 10) y)) ∧
        (∀ y : E3, inner Real v (T y) =
          inner Real v (f p) + s * (y 2 - height (d 0))) ∧
        F '' closedBall (0 : E3) 1 = T '' {y | polynomial (3 / 10) y ≤ 1} ∧
        F '' ball (0 : E3) 1 = T '' {y | polynomial (3 / 10) y < 1} ∧
        (∀ q : S2, inner Real v (F q) =
          inner Real v (f p) + s * (height q - height (d 0))) ∧
        ∀ x ∈ closedBall (0 : E2) r, F (d x) = f (e (Real.sqrt s • x)) := by
  have hp₀ := prescribed_nested_model_chart_critical d hd0 hd hdi hdform
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hfσ : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) + ∑ i : Fin 2, (![-1, 1] i : Real) * (x i)^2 := by
    intro x hx
    rw [hform x hx]
    simp [Fin.sum_univ_two]
    ring
  obtain ⟨J, a, ha, has, _, D, hDheight, _, hD⟩ :=
    exists_height_preserving_critical_graph_with_plane_action
      hf hv p hp e he0 hep he hei ![-1, 1] hfσ
  have hDform (x : E2) (hx : x ∈ closedBall (0 : E2) a) :
      D (f (e x)) = (J x : E3) + (inner Real v (f p)-(x 0)^2+(x 1)^2) • v := by
    rw [hD x hx]
    congr 2
    simp [Fin.sum_univ_two]
    ring
  have haxis (y : E3) : inner Real axis y = y 2 := by
    simp [axis, PiLp.inner_apply]
  have hmodelheight : (fun q : S2 => inner Real axis (shear (3 / 10) q)) = height :=
    funext (fun q => haxis (shear (3 / 10) q))
  have hmodelσ : ∀ x ∈ d.source, inner Real axis (shear (3 / 10) (d x)) =
      inner Real axis (shear (3 / 10) (d 0)) +
        ∑ i : Fin 2, (![-1, 1] i : Real) * (x i)^2 := by
    intro x hx
    rw [haxis, haxis]
    change height (d x) = height (d 0) + _
    rw [hdform x hx]
    simp [Fin.sum_univ_two]
    ring
  obtain ⟨J₀, b, hb, hbs, _, D₀, hD₀height, _, hD₀⟩ :=
    exists_height_preserving_critical_graph_with_plane_action
      (shear_sphere_smoothEmbedding (3 / 10)) (show ‖axis‖ = 1 by simp [axis])
      (d 0) (by rw [hmodelheight]; exact hp₀) d hd0 rfl hd hdi ![-1, 1] hmodelσ
  obtain ⟨H, hHheight, hH⟩ := Saddle.exists_scaled_saddle_transport hv
    (inner Real v (f p)-s*(height (d 0)+1)) hs J₀ J
  let T := (D₀.trans H).trans D.symm
  let F := (shear (3 / 10)).trans T
  have hT (y : E3) : T y = D.symm (H (D₀ y)) := rfl
  have hF (y : E3) : F y = T (shear (3 / 10) y) := rfl
  have hDi (y : E3) : inner Real v (D.symm y) = inner Real v y := by
    simpa only [D.apply_symm_apply] using (hDheight (D.symm y)).symm
  have hD₀h (y : E3) : D₀ y 2 = y 2 := by
    simpa only [haxis] using hD₀height y
  have hTheight (y : E3) : inner Real v (T y) =
      inner Real v (f p)+s*(y 2-height (d 0)) := by
    rw [hT, hDi, hHheight, hD₀h]
    ring
  let r := min b (a / Real.sqrt s)
  have hr : 0 < r := lt_min hb (div_pos ha hroot)
  have hrb : closedBall (0 : E2) r ⊆ closedBall (0 : E2) b :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hscale (x : E2) (hx : x ∈ closedBall (0 : E2) r) :
      Real.sqrt s • x ∈ closedBall (0 : E2) a := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hroot]
    have hx' := mem_closedBall_zero_iff.mp hx
    have hra : Real.sqrt s*r ≤ a := by
      have := (le_div_iff₀ hroot).mp (min_le_right b (a / Real.sqrt s))
      linarith
    exact (mul_le_mul_of_nonneg_left hx' hroot.le).trans hra
  have himage (K : Set E3) : F '' K = T '' (shear (3 / 10) '' K) := image_comp T _ K
  refine ⟨r, hr, (fun x hx => hbs (hrb hx)), (fun x hx => has (hscale x hx)),
    T, F, hF, hTheight, ?_, ?_, (fun q => hTheight (shear (3 / 10) q)), ?_⟩
  · rw [himage, shear_image_closedBall]
  · rw [himage, shear_image_ball]
  · intro x hx
    rw [hF, hT, hD₀ x (hrb hx), hH]
    have halg : inner Real v (f p)-s*(height (d 0)+1)+
        s*(inner Real axis (shear (3 / 10) (d 0))+
          ∑ i : Fin 2, (![-1, 1] i : Real)*(x i)^2+1) =
        inner Real v (f p)-((Real.sqrt s • x) 0)^2+((Real.sqrt s • x) 1)^2 := by
      rw [haxis]
      change inner Real v (f p)-s*(height (d 0)+1)+s*(height (d 0)+_+1) = _
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        neg_mul, one_mul, PiLp.smul_apply, smul_eq_mul, mul_pow,
        Real.sq_sqrt hs.le]
      ring
    rw [halg, ← hDform (Real.sqrt s • x) (hscale x hx), D.symm_apply_apply]

def negativeBranchReflection : E2 ≃ₗᵢ[Real] E2 where
  toFun x := WithLp.toLp 2 ![-x 0, x 1]
  invFun x := WithLp.toLp 2 ![-x 0, x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp
  norm_map' x := by
    change ‖WithLp.toLp 2 ![-x 0, x 1]‖ = ‖x‖
    have h1 := EuclideanSpace.real_norm_sq_eq x
    have h2 := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 ![-x 0, x 1])
    simp only [Fin.sum_univ_two] at h1 h2
    simp at h2
    nlinarith [norm_nonneg x, norm_nonneg (WithLp.toLp 2 ![-x 0, x 1])]

@[simp] theorem negativeBranchReflection_apply (x : E2) :
    negativeBranchReflection x = WithLp.toLp 2 ![-x 0, x 1] := rfl

@[simp] theorem negativeBranchReflection_negativeLevelArc (t s : Real) (i : Fin 2) :
    negativeBranchReflection (SaddleLevel.negativeLevelArc t i s) =
      SaddleLevel.negativeLevelArc t (Equiv.swap (0 : Fin 2) 1 i) s := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [SaddleLevel.negativeLevelArc, SaddleLevel.positiveLevelArc,
      SaddleLevel.saddleCoordinateSwap]

def negativeBranchReflectedChart (d : OpenPartialHomeomorph E2 S2) :
    OpenPartialHomeomorph E2 S2 :=
  negativeBranchReflection.toHomeomorph.toOpenPartialHomeomorph.trans d

@[simp] theorem negativeBranchReflectedChart_apply
    (d : OpenPartialHomeomorph E2 S2) (x : E2) :
    negativeBranchReflectedChart d x = d (negativeBranchReflection x) := rfl

@[simp] theorem mem_negativeBranchReflectedChart_source
    (d : OpenPartialHomeomorph E2 S2) (x : E2) :
    x ∈ (negativeBranchReflectedChart d).source ↔ negativeBranchReflection x ∈ d.source := by
  change (x ∈ (univ : Set E2) ∧ negativeBranchReflection x ∈ d.source) ↔ _
  simp

@[simp] theorem negativeBranchReflectedChart_zero (d : OpenPartialHomeomorph E2 S2) :
    negativeBranchReflectedChart d 0 = d 0 := by
  rw [negativeBranchReflectedChart_apply, map_zero]

theorem negativeBranchReflectedChart_smooth (d : OpenPartialHomeomorph E2 S2)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (negativeBranchReflectedChart d)
      (negativeBranchReflectedChart d).source :=
  hd.comp negativeBranchReflection.toContinuousLinearEquiv.toDiffeomorph.contMDiff.contMDiffOn
    (fun x hx => (mem_negativeBranchReflectedChart_source d x).mp hx)

theorem negativeBranchReflectedChart_symm_smooth (d : OpenPartialHomeomorph E2 S2)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (negativeBranchReflectedChart d).symm
      (negativeBranchReflectedChart d).target :=
  negativeBranchReflection.symm.toContinuousLinearEquiv.toDiffeomorph.contMDiff.comp_contMDiffOn
    (hdi.mono inter_subset_left)

theorem negativeBranchReflectedChart_ball_source (d : OpenPartialHomeomorph E2 S2)
    {r : Real} (hr : closedBall (0 : E2) r ⊆ d.source) :
    closedBall (0 : E2) r ⊆ (negativeBranchReflectedChart d).source := by
  intro x hx
  apply (mem_negativeBranchReflectedChart_source d x).mpr
  apply hr
  simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using hx

theorem negativeBranchReflectedChart_height
    (d : OpenPartialHomeomorph E2 S2) (h : S2 → Real)
    (hform : ∀ x ∈ d.source, h (d x) = h (d 0) - (x 0)^2 + (x 1)^2) :
    ∀ x ∈ (negativeBranchReflectedChart d).source,
      h (negativeBranchReflectedChart d x) =
        h (negativeBranchReflectedChart d 0) - (x 0)^2 + (x 1)^2 := by
  intro x hx
  rw [negativeBranchReflectedChart_apply, negativeBranchReflectedChart_zero,
    hform _ ((mem_negativeBranchReflectedChart_source d x).mp hx)]
  simp

@[simp] theorem negativePatchArc_negativeBranchReflectedChart
    (d : OpenPartialHomeomorph E2 S2) (r t : Real) (i : Fin 2) :
    SaddleLevel.negativePatchArc (negativeBranchReflectedChart d) r t i =
      SaddleLevel.negativePatchArc d r t (Equiv.swap (0 : Fin 2) 1 i) := by
  simp only [SaddleLevel.negativePatchArc, image_image,
    negativeBranchReflectedChart_apply, negativeBranchReflection_negativeLevelArc]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
