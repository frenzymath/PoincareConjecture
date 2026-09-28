import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OrientedCollar
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLTriangleBoundary

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

theorem exists_synchronized_collar_boundary_homeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A₀ A₁ : Set E} {L d : ℝ} {m n : ℕ}
    (Q₀ : Polygon E (m + 3)) (Q₁ : Polygon E (n + 3))
    (hQ₀ : Q₀.HasSimplicialEdges) (hQ₀i : Function.Injective Q₀)
    (hsub₀ : Q₀.boundary ℝ ⊆ A₀) (hsub₁ : Q₁.boundary ℝ ⊆ A₁)
    (c₀ : squareAnnulus L d ≃ₜ A₀) (c₁ : squareAnnulus L d ≃ₜ A₁)
    (hc₀ : c₀.IsFinitePL) (hc₁ : c₁.IsFinitePL)
    (hlevel₀ : ∀ p, (c₀ p : E) ∈ Q₀.boundary ℝ ↔ depth L p = d)
    (hlevel₁ : ∀ p, (c₁ p : E) ∈ Q₁.boundary ℝ ↔ depth L p = d) :
    ∃ eb : Q₀.boundary ℝ ≃ₜ Q₁.boundary ℝ,
      eb.IsFinitePL ∧ eb.symm.IsFinitePL ∧
      (∀ x : Q₀.boundary ℝ,
        (eb x : E) = c₁ (c₀.symm ⟨x, hsub₀ x.property⟩)) ∧
      ∀ (p : squareAnnulus L d) (hp : depth L p = d),
        (eb ⟨c₀ p, (hlevel₀ p).mpr hp⟩ : E) = c₁ p := by
  let e := c₀.symm.trans c₁
  obtain ⟨f, hf, hef⟩ := hc₀.symm.trans hc₁
  obtain ⟨_, heQ, _⟩ := Q₀.exists_finitePL_triangle_boundary_model hQ₀ hQ₀i
    TriangleDiskModel.rightTriangle TriangleDiskModel.independent_rightTriangle
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := heQ
  have hfQ : FinitePiecewiseAffineOn f (Q₀.boundary ℝ) := by
    rw [← hKs]
    exact hf.restrict K hK (hKs.subset.trans hsub₀)
  have hfi : InjOn f (Q₀.boundary ℝ) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hef ⟨x, hsub₀ hx⟩).trans (hxy.trans (hef ⟨y, hsub₀ hy⟩).symm))))
  have him : f '' Q₀.boundary ℝ = Q₁.boundary ℝ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hsub₀ hx⟩]
      apply (hlevel₁ _).mpr
      apply (hlevel₀ _).mp
      change (c₀ (c₀.symm ⟨x, hsub₀ hx⟩) : E) ∈ Q₀.boundary ℝ
      simpa only [c₀.apply_symm_apply] using hx
    · intro hy
      let p := c₁.symm ⟨y, hsub₁ hy⟩
      have hp : depth L p = d := (hlevel₁ p).mp (by
        simpa only [p, c₁.apply_symm_apply] using hy)
      refine ⟨c₀ p, (hlevel₀ p).mpr hp, ?_⟩
      rw [← hef]
      change (c₁ (c₀.symm (c₀ p)) : E) = y
      rw [c₀.symm_apply_apply]
      exact congrArg Subtype.val (c₁.apply_symm_apply _)
  obtain ⟨b, hb, hbf⟩ := hfQ.exists_homeomorph_image hfi
  let eb := b.trans (Homeomorph.setCongr him)
  have heb : eb.IsFinitePL := by
    obtain ⟨g, hg, hbg⟩ := hb
    exact ⟨g, hg, hbg⟩
  have heval (x : Q₀.boundary ℝ) :
      (eb x : E) = c₁ (c₀.symm ⟨x, hsub₀ x.property⟩) :=
    (hbf x).trans (hef ⟨x, hsub₀ x.property⟩).symm
  refine ⟨eb, heb, heb.symm, heval, ?_⟩
  intro p hp
  rw [heval]
  exact congrArg (fun q ↦ (c₁ q : E)) (c₀.symm_apply_apply p)

end Dehn
