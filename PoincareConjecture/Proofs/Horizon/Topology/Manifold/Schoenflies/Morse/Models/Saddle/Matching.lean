import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Normalized
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Matching.Transport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2+1) := ⟨by simp⟩

theorem exists_filled_saddle_matching
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) - (x 0)^2 + (x 1)^2)
    {ε : Real} (hε : 0 < ε) :
    ∃ s : Real, 0 < s ∧ s < ε ∧ 3*s/2 < ε ∧
      ∃ d : OpenPartialHomeomorph E2 S2,
        0 ∈ d.source ∧ d 0 = saddlePoint ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
        ∃ r > 0, closedBall (0 : E2) r ⊆ d.source ∧
          (∀ x ∈ closedBall (0 : E2) r, Real.sqrt s • x ∈ e.source) ∧
          ∃ T F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
            (∀ y : E3, F y = T (shear y)) ∧
            (∀ y : E3, inner Real v (T y) = inner Real v (f p)+s*(y 2+1)) ∧
            F '' closedBall (0 : E3) 1 = T '' {y | polynomial y ≤ 1} ∧
            F '' ball (0 : E3) 1 = T '' {y | polynomial y < 1} ∧
            F '' sphere (0 : E3) 1 =
              (T '' band) ∪ ((T ∘ lowerCap 1) '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
                ((T ∘ lowerCap (-1)) '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
                ((T ∘ upperCap) '' closedBall (0 : E2) (Real.sqrt (3/4))) ∧
            (∀ q : S2, inner Real v (F q) = inner Real v (f p)+s*(height q+1)) ∧
            ∀ x ∈ closedBall (0 : E2) r, F (d x) = f (e (Real.sqrt s • x)) := by
  let s := ε/4
  have hs : 0 < s := by dsimp [s]; positivity
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
  obtain ⟨d, hd0, hdp, hd, hdi, J₀, b, hb, hbs, _, D₀, hD₀, _, _, hpatch⟩ :=
    exists_height_preserving_quadratic_model
  obtain ⟨H, hHheight, hH⟩ := exists_scaled_saddle_transport hv (inner Real v (f p)) hs J₀ J
  let T := (D₀.trans H).trans D.symm
  let F := shear.trans T
  have hT (y : E3) : T y = D.symm (H (D₀ y)) := rfl
  have hF (y : E3) : F y = T (shear y) := rfl
  have hDi (y : E3) : inner Real v (D.symm y) = inner Real v y := by
    simpa only [D.apply_symm_apply] using (hDheight (D.symm y)).symm
  have hTheight (y : E3) : inner Real v (T y) = inner Real v (f p)+s*(y 2+1) := by
    rw [hT, hDi, hHheight, hD₀]
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
    exact le_trans (mul_le_mul_of_nonneg_left hx' hroot.le) hra
  have himage (K : Set E3) : F '' K = T '' (shear '' K) := image_comp T shear K
  refine ⟨s, hs, by dsimp [s]; linarith, by dsimp [s]; linarith,
    d, hd0, hdp, hd, hdi, r, hr, fun x hx => hbs (hrb hx),
    fun x hx => has (hscale x hx), T, F, hF, hTheight, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himage, shear_image_closedBall]
  · rw [himage, shear_image_ball]
  · rw [himage, shear_image_sphere_eq_band_union_caps,
      image_union, image_union, image_union, image_comp, image_comp, image_comp]
  · intro q
    exact hTheight (shear q)
  · intro x hx
    rw [hF, hT, hpatch x (hrb hx), hH]
    have halg : inner Real v (f p)+s*((-1-(x 0)^2+(x 1)^2)+1) =
        inner Real v (f p)-((Real.sqrt s • x) 0)^2+((Real.sqrt s • x) 1)^2 := by
      simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hs.le]
      ring
    rw [halg, ← hDform (Real.sqrt s • x) (hscale x hx), D.symm_apply_apply]

end Poincare.Manifold.Schoenflies.Saddle
