import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Noncrossing
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.NormalForm
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Isolated



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1





theorem exists_normalized_exterior_noncrossing_square
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε) :
    ∃ J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ, ∃ a > 0,
      closedBall (0 : E2) a ⊆ e.source ∧
      ∃ A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
          (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y : E3, inner Real v (D y) = inner Real v y) ∧
        (∀ (t : Real) (x : (Real ∙ v)ᗮ), D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        (∀ x ∈ closedBall (0 : E2) a,
          D (f (e x)) = (J x : E3) +
            (inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2) • v) ∧
        ∃ r : Real, 0 < r ∧ r < ε ∧ closedSquare r ⊆ ball (0 : E2) a ∧
          (∀ q : S2, inner Real v (f q) = inner Real v (f p) ->
            (planarProjection J (D (f q)) ∈ closedSquare r ↔ q ∈ e '' closedSquare r)) ∧
          (∀ q : S2, inner Real v (f q) = inner Real v (f p) ->
            (planarProjection J (D (f q)) ∈ openSquare r ↔ q ∈ e '' openSquare r)) ∧
          {q : S2 | inner Real v (f q) = inner Real v (f p) ∧
            planarProjection J (D (f q)) ∈ closedSquare r \ openSquare r} =
              range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
          Function.Injective (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
          ∀ (α β : Real -> S2),
            ContinuousOn α (Icc (0 : Real) 1) -> ContinuousOn β (Icc (0 : Real) 1) ->
            MapsTo α (Icc (0 : Real) 1)
              ({q | inner Real v (f q) = inner Real v (f p)} \ e '' openSquare r) ->
            MapsTo β (Icc (0 : Real) 1)
              ({q | inner Real v (f q) = inner Real v (f p)} \ e '' openSquare r) ->
            α 0 = e (contact r (1, 1)) -> α 1 = e (contact r (0, 0)) ->
            β 0 = e (contact r (0, 1)) -> β 1 = e (contact r (1, 0)) ->
            ¬ Disjoint (α '' Icc (0 : Real) 1) (β '' Icc (0 : Real) 1) := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (f q)) :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  have hfσ : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) + ∑ i : Fin 2, (![-1, 1] i : Real) * x i ^ 2 := by
    intro x hx
    rw [hform x hx]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_one_mul, one_mul]
    ring
  have hσ : ∀ i : Fin 2, (![-1, 1] i : Real) ≠ 0 := by
    intro i
    fin_cases i <;> norm_num
  have hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0 := by
    rw [← hep]
    exact (mfderiv_eq_zero_iff_eq_zero_in_morse_coordinates hh e he hei
      (inner Real v (f p)) ![-1, 1] hσ hfσ he0).mpr rfl
  obtain ⟨J, a, ha, has, A, D, hDheight, hDplane, hD⟩ :=
    exists_height_preserving_critical_graph_with_plane_action
      hf hv p hp e he0 hep he hei ![-1, 1] hfσ
  have hgraph : ∀ x ∈ closedBall (0 : E2) a,
      D (f (e x)) = (J x : E3) +
        (inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2) • v := by
    intro x hx
    rw [hD x hx]
    congr 2
    simp [Fin.sum_univ_two]
    ring
  exact ⟨J, a, ha, has, A, D, hDheight, hDplane, hgraph,
    exists_exterior_noncrossing_square hf hv p e hep ha has J D hDheight hgraph hε⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
