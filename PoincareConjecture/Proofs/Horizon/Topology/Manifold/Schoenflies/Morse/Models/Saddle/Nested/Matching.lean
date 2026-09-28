import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.MorseCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.NormalForm
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Matching.Transport







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev axis : E3 := EuclideanSpace.single 2 1
private instance : Fact (Module.finrank Real E3 = 2+1) := ⟨by simp⟩

theorem shear_sphere_smoothEmbedding (b : Real) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p : S2 => shear b p) := by
  have hc := contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3)
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    ((shear b).contMDiff.comp hc) ((shear b).injective.comp Subtype.val_injective)
  intro p
  rw [mfderiv_comp p (((shear b).contMDiff (p : E3)).mdifferentiableAt (by simp))
    ((hc p).mdifferentiableAt (by simp))]
  apply ((shear b).mfderivToContinuousLinearEquiv (by simp) (p : E3)).injective.comp
  convert! injective_mvfderiv_subtypeVal_sphere p



theorem exists_filled_nested_saddle_matching
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) - (x 0)^2 + (x 1)^2)
    {ε : Real} (hε : 0 < ε) :
    ∃ p₀ : S2, 1 < height p₀ ∧
      ∃ s : Real, 0 < s ∧ s < ε ∧ s*(height p₀-1) < ε ∧
      ∃ d : OpenPartialHomeomorph E2 S2,
        0 ∈ d.source ∧ d 0 = p₀ ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
        ∃ r > 0, closedBall (0 : E2) r ⊆ d.source ∧
          (∀ x ∈ closedBall (0 : E2) r, Real.sqrt s • x ∈ e.source) ∧
          ∃ T F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
            (∀ y : E3, F y = T (shear (3/10) y)) ∧
            (∀ y : E3, inner Real v (T y) = inner Real v (f p)+s*(y 2-height p₀)) ∧
            F '' closedBall (0 : E3) 1 = T '' {y | polynomial (3/10) y ≤ 1} ∧
            F '' ball (0 : E3) 1 = T '' {y | polynomial (3/10) y < 1} ∧
            (∀ q : S2, inner Real v (F q) =
              inner Real v (f p)+s*(height q-height p₀)) ∧
            ∀ x ∈ closedBall (0 : E2) r, F (d x) = f (e (Real.sqrt s • x)) := by
  obtain ⟨p₀, hc₀, hp₀, d, hd0, hdp, hd, hdi, hdform⟩ :=
    exists_saddle_coordinates_above_nested_cut
  let s := ε / (2 * height p₀)
  have hcpos : 0 < height p₀ := by linarith
  have hs : 0 < s := div_pos hε (by positivity)
  have hsε : s < ε := by
    dsimp [s]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * height p₀)).mpr
    nlinarith
  have hscε : s*(height p₀-1) < ε := by
    have hseq : s * (2 * height p₀) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
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
  have hmodelheight : (fun q : S2 => inner Real axis (shear (3/10) q)) = height :=
    funext (fun q => haxis (shear (3/10) q))
  have hmodelσ : ∀ x ∈ d.source, inner Real axis (shear (3/10) (d x)) =
      inner Real axis (shear (3/10) p₀) + ∑ i : Fin 2, (![-1, 1] i : Real) * (x i)^2 := by
    intro x hx
    rw [haxis, haxis]
    change height (d x) = height p₀ + _
    rw [hdform x hx]
    simp [Fin.sum_univ_two]
    ring
  obtain ⟨J₀, b, hb, hbs, _, D₀, hD₀height, _, hD₀⟩ :=
    exists_height_preserving_critical_graph_with_plane_action
      (shear_sphere_smoothEmbedding (3/10)) (show ‖axis‖ = 1 by simp [axis])
      p₀ (by rw [hmodelheight]; exact hp₀) d hd0 hdp hd hdi ![-1, 1] hmodelσ
  obtain ⟨H, hHheight, hH⟩ := exists_scaled_saddle_transport hv
    (inner Real v (f p)-s*(height p₀+1)) hs J₀ J
  let T := (D₀.trans H).trans D.symm
  let F := (shear (3/10)).trans T
  have hT (y : E3) : T y = D.symm (H (D₀ y)) := rfl
  have hF (y : E3) : F y = T (shear (3/10) y) := rfl
  have hDi (y : E3) : inner Real v (D.symm y) = inner Real v y := by
    simpa only [D.apply_symm_apply] using (hDheight (D.symm y)).symm
  have hD₀h (y : E3) : D₀ y 2 = y 2 := by
    simpa only [haxis] using hD₀height y
  have hTheight (y : E3) : inner Real v (T y) =
      inner Real v (f p)+s*(y 2-height p₀) := by
    rw [hT, hDi, hHheight, hD₀h]
    ring
  let r := min b (a/Real.sqrt s)
  have hr : 0 < r := lt_min hb (div_pos ha hroot)
  have hrb : closedBall (0 : E2) r ⊆ closedBall (0 : E2) b :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hscale (x : E2) (hx : x ∈ closedBall (0 : E2) r) :
      Real.sqrt s • x ∈ closedBall (0 : E2) a := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hroot]
    have hx' := mem_closedBall_zero_iff.mp hx
    have hra : Real.sqrt s*r ≤ a := by
      have := (le_div_iff₀ hroot).mp (min_le_right b (a/Real.sqrt s))
      linarith
    exact (mul_le_mul_of_nonneg_left hx' hroot.le).trans hra
  have himage (K : Set E3) : F '' K = T '' (shear (3/10) '' K) := image_comp T _ K
  refine ⟨p₀, hc₀, s, hs, hsε, hscε, d, hd0, hdp, hd, hdi, r, hr,
    (fun x hx => hbs (hrb hx)), (fun x hx => has (hscale x hx)), T, F, hF, hTheight,
    ?_, ?_, (fun q => hTheight (shear (3/10) q)), ?_⟩
  · rw [himage, shear_image_closedBall]
  · rw [himage, shear_image_ball]
  · intro x hx
    rw [hF, hT, hD₀ x (hrb hx), hH]
    have halg : inner Real v (f p)-s*(height p₀+1)+
        s*(inner Real axis (shear (3/10) p₀)+
          ∑ i : Fin 2, (![-1, 1] i : Real)*(x i)^2+1) =
        inner Real v (f p)-((Real.sqrt s • x) 0)^2+((Real.sqrt s • x) 1)^2 := by
      rw [haxis]
      change inner Real v (f p)-s*(height p₀+1)+s*(height p₀+_+1) = _
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        neg_mul, one_mul, PiLp.smul_apply, smul_eq_mul, mul_pow,
        Real.sq_sqrt hs.le]
      ring
    rw [halg, ← hDform (Real.sqrt s • x) (hscale x hx), D.symm_apply_apply]

end Poincare.Manifold.Schoenflies.Saddle.Nested
