import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PrescribedModelChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open Saddle.Nested SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_filled_nested_candidate_pair
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) - (x 0)^2 + (x 1)^2)
    {s : Real} (hs : 0 < s) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      0 ∈ d.source ∧ 1 < height (d 0) ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) height (d 0) = 0 ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      (∀ x ∈ d.source, height (d x) = height (d 0) - (x 0)^2 + (x 1)^2) ∧
      ∃ r > 0, closedBall (0 : E2) r ⊆ d.source ∧
        closedBall (0 : E2) r ⊆ (negativeBranchReflectedChart d).source ∧
        (∀ x ∈ closedBall (0 : E2) r, Real.sqrt s • x ∈ e.source) ∧
        ∃ T F : Fin 2 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ i y, F i y = T i (shear (3 / 10) y)) ∧
          (∀ i y, inner Real v (T i y) =
            inner Real v (f p) + s * (y 2 - height (d 0))) ∧
          (∀ i, F i '' closedBall (0 : E3) 1 =
            T i '' {y | polynomial (3 / 10) y ≤ 1}) ∧
          (∀ i, F i '' ball (0 : E3) 1 =
            T i '' {y | polynomial (3 / 10) y < 1}) ∧
          (∀ i (q : S2), inner Real v (F i q) =
            inner Real v (f p) + s * (height q - height (d 0))) ∧
          (∀ x ∈ closedBall (0 : E2) r, F 0 (d x) = f (e (Real.sqrt s • x))) ∧
          (∀ x ∈ closedBall (0 : E2) r,
            F 1 (negativeBranchReflectedChart d x) = f (e (Real.sqrt s • x))) ∧
          ∀ t u i, negativeBranchReflectedChart d (negativeLevelArc t i u) =
            d (negativeLevelArc t (Equiv.swap (0 : Fin 2) 1 i) u) := by
  obtain ⟨p₀, hc₀, hp₀, d, hd0, hdp, hd, hdi, hdform⟩ :=
    exists_saddle_coordinates_above_nested_cut
  have hdheight : ∀ x ∈ d.source,
      height (d x) = height (d 0) - (x 0)^2 + (x 1)^2 := by
    simpa only [hdp] using hdform
  obtain ⟨r₀, hr₀, hr₀source, hactual₀, T₀, F₀, hF₀, hT₀,
      hclosed₀, hopen₀, hheight₀, hmatch₀⟩ :=
    exists_filled_nested_matching_with_prescribed_chart hf hv p hp e he0 hep he hei hform
      d hd0 hd hdi hdheight hs
  have hrd0 : 0 ∈ (negativeBranchReflectedChart d).source := by
    apply (mem_negativeBranchReflectedChart_source d 0).mpr
    simpa only [map_zero] using hd0
  obtain ⟨r₁, hr₁, hr₁source, _, T₁, F₁, hF₁, hT₁,
      hclosed₁, hopen₁, hheight₁, hmatch₁⟩ :=
    exists_filled_nested_matching_with_prescribed_chart hf hv p hp e he0 hep he hei hform
      (negativeBranchReflectedChart d) hrd0 (negativeBranchReflectedChart_smooth d hd)
      (negativeBranchReflectedChart_symm_smooth d hdi)
      (negativeBranchReflectedChart_height d height hdheight) hs
  have hsub₀ : closedBall (0 : E2) (min r₀ r₁) ⊆ closedBall (0 : E2) r₀ :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hsub₁ : closedBall (0 : E2) (min r₀ r₁) ⊆ closedBall (0 : E2) r₁ :=
    closedBall_subset_closedBall (min_le_right _ _)
  refine ⟨d, hd0, by simpa only [hdp] using hc₀, by rw [hdp]; exact hp₀,
    hd, hdi, hdheight, min r₀ r₁, lt_min hr₀ hr₁, hsub₀.trans hr₀source,
    hsub₁.trans hr₁source, (fun x hx => hactual₀ x (hsub₀ hx)),
    ![T₀, T₁], ![F₀, F₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i y
    fin_cases i
    · exact hF₀ y
    · exact hF₁ y
  · intro i y
    fin_cases i
    · exact hT₀ y
    · change inner Real v (T₁ y) = _
      simpa only [negativeBranchReflectedChart_zero] using hT₁ y
  · intro i
    fin_cases i
    · exact hclosed₀
    · exact hclosed₁
  · intro i
    fin_cases i
    · exact hopen₀
    · exact hopen₁
  · intro i q
    fin_cases i
    · exact hheight₀ q
    · change inner Real v (F₁ q) = _
      simpa only [negativeBranchReflectedChart_zero] using hheight₁ q
  · intro x hx
    exact hmatch₀ x (hsub₀ hx)
  · intro x hx
    exact hmatch₁ x (hsub₁ hx)
  · intro t u i
    rw [negativeBranchReflectedChart_apply, negativeBranchReflection_negativeLevelArc]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
