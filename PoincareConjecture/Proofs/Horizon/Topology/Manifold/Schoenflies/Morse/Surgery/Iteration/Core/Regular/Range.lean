import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular.CapBelt



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {v : E3} {g : S2 → E3} {B : Set Real}


def truncatedImage (D : SphereSurgeryCoreCap v g B) (θ : Real) : Set E3 :=
  (D.parametrization '' closedBall 0 1) ∩
    {y : E3 | θ ≤ (inner Real v y - D.center) / D.scale}

theorem truncatedImage_subset_range (D : SphereSurgeryCoreCap v g B) (θ : Real) :
    D.truncatedImage θ ⊆ range g := by
  intro y hy
  have hm := D.image_closedBall.symm ▸ hy.1
  obtain ⟨p, _, rfl⟩ := hm
  exact mem_range_self _

private theorem mem_truncated_or_annular_belt
    (D : SphereSurgeryCoreCap v g B)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {η : Real}
    (hslices : ∀ θ ∈ Icc (0 : Real) η,
      (D.chart '' closedBall 0 1) ∩
        {p : S2 | inner Real v (g p) = D.center + D.scale * θ} =
          range (fun q : S1 => F (q, D.center + D.scale * θ)))
    {y : E3} (hy : y ∈ D.parametrization '' closedBall 0 1) :
    y ∈ D.truncatedImage η ∨ ∃ θ ∈ Icc (0 : Real) η,
      y ∈ g '' range (fun q : S1 => F (q, D.center + D.scale * θ)) := by
  by_cases hlarge : η ≤ (inner Real v y - D.center) / D.scale
  · exact Or.inl ⟨hy, hlarge⟩
  · obtain ⟨x, hx, rfl⟩ := hy
    let θ := (inner Real v (D.parametrization x) - D.center) / D.scale
    have hθ : θ ∈ Icc (0 : Real) η :=
      ⟨D.normalized_height_nonneg hx, (lt_of_not_ge hlarge).le⟩
    refine Or.inr ⟨θ, hθ, ?_⟩
    rw [← hslices θ hθ]
    refine ⟨D.chart x, ⟨mem_image_of_mem D.chart hx, ?_⟩, D.parametrization_eq x hx⟩
    change inner Real v (g (D.chart x)) = D.center + D.scale * θ
    rw [D.parametrization_eq x hx]
    dsimp [θ]
    field_simp [D.scale_ne_zero]
    ring



theorem exists_widened_annular_range
    (D E : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hDE : D.center < E.center) (hDscale : D.scale < 0) (hEscale : 0 < E.scale)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {δ : Real} (hδ : 0 < δ)
    (hFs : F.source = univ ×ˢ Ioo (D.center - δ) (E.center + δ))
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo (D.center - δ) (E.center + δ) →
      inner Real v (g (F (q, t))) = t)
    (hDboundary : D.chart '' sphere (0 : E2) 1 ⊆ F.target)
    (hEboundary : E.chart '' sphere (0 : E2) 1 ⊆ F.target)
    (hrange : range g = (D.parametrization '' closedBall 0 1) ∪
      (g '' (F '' (univ ×ˢ Icc D.center E.center))) ∪
        (E.parametrization '' closedBall 0 1)) :
    ∃ α β : Real, 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧
      D.center + D.scale * α ∈ Ioo (D.center - δ) (E.center + δ) ∧
      E.center + E.scale * β ∈ Ioo (D.center - δ) (E.center + δ) ∧
      range g = D.truncatedImage α ∪
        (g '' (F '' (univ ×ˢ Icc (D.center + D.scale * α) (E.center + E.scale * β)))) ∪
        E.truncatedImage β ∧
      (∀ θ ∈ Icc (0 : Real) α,
        range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
          (g (F (q, D.center + D.scale * θ)))) =
            D.planeMap '' sphere (0 : Hemisphere.Plane v) 1) ∧
      (∀ θ ∈ Icc (0 : Real) β,
        range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
          (g (F (q, E.center + E.scale * θ)))) =
            E.planeMap '' sphere (0 : Hemisphere.Plane v) 1) := by
  obtain ⟨α, hα, hα1, hD⟩ := D.exists_annular_cap_belt hg F hFs hF hFi hheight
    (by constructor <;> linarith) hDboundary
  obtain ⟨β, hβ, hβ1, hE⟩ := E.exists_annular_cap_belt hg F hFs hF hFi hheight
    (by constructor <;> linarith) hEboundary
  have hlow : D.center + D.scale * α < D.center := by nlinarith
  have hupp : E.center < E.center + E.scale * β := by nlinarith
  refine ⟨α, β, hα, hα1, hβ, hβ1, (hD α ⟨hα.le, le_rfl⟩).1,
    (hE β ⟨hβ.le, le_rfl⟩).1, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro y hy
      rw [hrange] at hy
      rcases hy with (hyD | hyF) | hyE
      · rcases mem_truncated_or_annular_belt D F (fun θ hθ => (hD θ hθ).2.1) hyD with
          hy | ⟨θ, hθ, p, ⟨q, rfl⟩, rfl⟩
        · exact Or.inl (Or.inl hy)
        · refine Or.inl (Or.inr ⟨F (q, D.center + D.scale * θ), ?_, rfl⟩)
          refine ⟨(q, D.center + D.scale * θ), ⟨mem_univ _, ?_⟩, rfl⟩
          constructor <;> nlinarith [hθ.1, hθ.2]
      · apply Or.inl ∘ Or.inr
        apply image_mono (image_mono (prod_mono Subset.rfl ?_)) hyF
        intro t ht
        exact ⟨hlow.le.trans ht.1, ht.2.trans hupp.le⟩
      · rcases mem_truncated_or_annular_belt E F (fun θ hθ => (hE θ hθ).2.1) hyE with
          hy | ⟨θ, hθ, p, ⟨q, rfl⟩, rfl⟩
        · exact Or.inr hy
        · refine Or.inl (Or.inr ⟨F (q, E.center + E.scale * θ), ?_, rfl⟩)
          refine ⟨(q, E.center + E.scale * θ), ⟨mem_univ _, ?_⟩, rfl⟩
          constructor <;> nlinarith [hθ.1, hθ.2]
    · rintro y ((hyD | ⟨p, _, rfl⟩) | hyE)
      · exact D.truncatedImage_subset_range α hyD
      · exact mem_range_self p
      · exact E.truncatedImage_subset_range β hyE
  · intro θ hθ
    exact D.projected_slice_eq_circle F _ (hD θ hθ).2.2
  · intro θ hθ
    exact E.projected_slice_eq_circle F _ (hE θ hθ).2.2

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
