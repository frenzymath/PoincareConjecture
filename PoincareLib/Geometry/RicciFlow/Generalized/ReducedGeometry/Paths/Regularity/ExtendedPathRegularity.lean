import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.CurveVelocityRegularity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackReparametrization

/-!
# Interior smoothness from an actual velocity extension

Morgan-Tian Definition 6.7 and Lemma 6.8, pp. 108-109. The frozen
extension and actual derivative equation express the path as a solution
of a smooth tangent field. The manifold velocity bootstrap gives every
interior derivative without minimality or the Euler equation.
-/

set_option autoImplicit false
-- Pullback tangent fibers are the actual model fibers over the spatial projection.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

noncomputable section

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

/-- Every admissible path with an actual smooth velocity extension
is smooth on its original strict interval, the interior regularity
used in Definition 6.7 and Lemma 6.8, pp. 108-109. -/
theorem backwardPath_contMDiffOn_of_velocity_extension
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ p.curve (Ioo τ₁ τ₂) := by
  obtain ⟨U, _, hgraph, hE⟩ := E.joint_smooth
  let base : ContMDiffMap ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (spacetimeModel n) (ℝ × G.Point) G.Point ∞ := ⟨Prod.snd, contMDiff_snd⟩
  let : ∀ z, AddCommGroup
      (((base : ℝ × G.Point → G.Point) *ᵖ
        (TangentSpace (spacetimeModel n) : G.Point → Type _)) z) :=
    fun z => inferInstanceAs (AddCommGroup (TangentSpace (spacetimeModel n) (base z)))
  let : ∀ z, Module ℝ
      (((base : ℝ × G.Point → G.Point) *ᵖ
        (TangentSpace (spacetimeModel n) : G.Point → Type _)) z) :=
    fun z => inferInstanceAs (Module ℝ (TangentSpace (spacetimeModel n) (base z)))
  let V : ∀ z,
      ((base : ℝ × G.Point → G.Point) *ᵖ (TangentSpace (spacetimeModel n) : G.Point → Type _)) z :=
    fun z => G.spacetime.timeVector z.2
  let W : ∀ z,
      ((base : ℝ × G.Point → G.Point) *ᵖ (TangentSpace (spacetimeModel n) : G.Point → Type _)) z :=
    fun z => (E.extension z.1 z.2).val
  have ht : ContMDiff (spacetimeModel n) (spacetimeModel n).tangent ∞
      (fun q : G.Point => Bundle.TotalSpace.mk' (SpacetimeModelVector n)
        (E := (TangentSpace (spacetimeModel n) : G.Point → Type _)) q
        (G.spacetime.timeVector q)) := G.spacetime.timeVector_smooth
  have htime := ht.comp base.contMDiff
  have hi : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (spacetimeModel n).tangent ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
        Bundle.TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : G.Point → Type _)) v.proj v.2.val) :=
    G.spacetime.horizontal_inclusion_smooth
  have hfield := hi.comp_contMDiffOn hE
  have hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (((𝓘(ℝ, ℝ)).prod (spacetimeModel n)).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun z => Bundle.TotalSpace.mk' (SpacetimeModelVector n) z (V z)) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base V U z).mpr
      (htime.contMDiffOn z hz)
  have hW : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (((𝓘(ℝ, ℝ)).prod (spacetimeModel n)).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun z => Bundle.TotalSpace.mk' (SpacetimeModelVector n) z (W z)) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base W U z).mpr (hfield z hz)
  have hsum := hV.neg_section.add_section hW
  have hactual : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (spacetimeModel n).tangent ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk' (SpacetimeModelVector n) z.2
        (-G.spacetime.timeVector z.2 + (E.extension z.1 z.2).val)) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base (fun z => -V z + W z) U z).mp
      (hsum z hz)
  apply contMDiffOn_of_smooth_curveVelocity isOpen_Ioo
    (p.curve_regular.mdifferentiableOn (by simp))
    (fun t q => -G.spacetime.timeVector q + (E.extension t q).val) hactual hgraph
  intro t ht
  rw [E.agrees t ht]
  exact p.derivative_eq t ht

end PoincareMT.M14
