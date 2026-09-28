import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.HalfspaceSign
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLLocalSignComposition











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem plLocalSign_eq_of_halfspace_agreement
    (h g : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) (hg : g ∈ piecewiseAffineGroupoid E)
    (ell m : E →ᴬ[ℝ] ℝ) (v : E) (hv : ell.contLinear v = 1)
    (hside : ∀ y ∈ h.source, 0 ≤ m (h y) ↔ 0 ≤ ell y)
    (gside : ∀ y ∈ g.source, 0 ≤ m (g y) ↔ 0 ≤ ell y)
    (hagree : ∀ y ∈ h.source ∩ g.source, ell y = 0 → h y = g y)
    {x : E} (hxh : x ∈ h.source) (hxg : x ∈ g.source) (hx : ell x = 0) :
    plLocalSign h hh ⟨x, hxh⟩ = plLocalSign g hg ⟨x, hxg⟩ := by
  let r := g.restr h.source
  have hr : r ∈ piecewiseAffineGroupoid E := closedUnderRestriction' hg h.open_source
  let c := r.trans h.symm
  have hc : c ∈ piecewiseAffineGroupoid E :=
    (piecewiseAffineGroupoid E).trans hr ((piecewiseAffineGroupoid E).symm hh)
  have hcsource (y : E) (hy : y ∈ c.source) :
      y ∈ g.source ∧ y ∈ h.source ∧ g y ∈ h.target :=
    ⟨hy.1.1, interior_subset hy.1.2, hy.2⟩
  have hcside : ∀ y ∈ c.source, 0 ≤ ell (c y) ↔ 0 ≤ ell y := by
    intro y hy
    have hs := hcsource y hy
    have hi := hside (h.symm (g y)) (h.map_target hs.2.2)
    rw [h.right_inv hs.2.2] at hi
    exact hi.symm.trans (gside y hs.1)
  have hcfix : ∀ y ∈ c.source, ell y = 0 → c y = y := by
    intro y hy he
    have hs := hcsource y hy
    change h.symm (g y) = y
    rw [← hagree y ⟨hs.2.1, hs.1⟩ he]
    exact h.left_inv hs.2.1
  have heq := hagree x ⟨hxh, hxg⟩ hx
  have hxr : x ∈ r.source := ⟨hxg, by simpa [h.open_source.interior_eq] using hxh⟩
  have hxc : x ∈ c.source := ⟨hxr, by change g x ∈ h.target; rw [← heq]; exact h.map_source hxh⟩
  have hpos := plLocalSign_eq_one_of_halfspace_fixed c hc ell v hv hcside hcfix ⟨x, hxc⟩ hx
  rw [plLocalSign_trans r h.symm hr ((piecewiseAffineGroupoid E).symm hh) ⟨x, hxc⟩] at hpos
  have hs : plLocalSign h.symm ((piecewiseAffineGroupoid E).symm hh)
      ⟨g x, hxc.2⟩ = plLocalSign h hh ⟨x, hxh⟩ := by
    convert plLocalSign_symm h hh ⟨x, hxh⟩ using 1 <;> simp only [heq]
  have hp : plLocalSign h hh ⟨x, hxh⟩ * plLocalSign g hg ⟨x, hxg⟩ = 1 :=
    (congrArg₂ (fun a b : SignType => a * b) hs
      (plLocalSign_restr g hg h.open_source ⟨x, hxr⟩)).symm.trans hpos
  generalize plLocalSign h hh ⟨x, hxh⟩ = a at hp ⊢
  generalize plLocalSign g hg ⟨x, hxg⟩ = b at hp ⊢
  cases a <;> cases b <;> simp_all

end Geometry
