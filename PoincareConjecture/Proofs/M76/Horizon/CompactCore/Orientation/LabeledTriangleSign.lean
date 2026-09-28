import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.FrontierChartSign
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.CompatibleChartLabels










set_option autoImplicit false

open Set

namespace Geometry

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace X]

theorem labeled_frontier_triangle_sign_eq
    (b : Module.Basis (Fin 3) ℝ F)
    (H J : OpenPartialHomeomorph X F)
    (hPL : H.symm.trans J ∈ piecewiseAffineGroupoid F)
    (N : Set X) (ell m : F →ᴬ[ℝ] ℝ) (n n' : F)
    (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (hH : ∀ y ∈ H.source, y ∈ N ↔ 0 ≤ ell (H y))
    (hJ : ∀ y ∈ J.source, y ∈ N ↔ 0 ≤ m (J y))
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (g : E → X) (hi : InjOn g (convexHull ℝ (range p)))
    (hgH : MapsTo g (convexHull ℝ (range p)) H.source)
    (hgJ : MapsTo g (convexHull ℝ (range p)) J.source)
    (hgN : MapsTo g (convexHull ℝ (range p)) (frontier N))
    (A D : E →ᴬ[ℝ] F)
    (hA : EqOn (H ∘ g) A (convexHull ℝ (range p)))
    (hD : EqOn (J ∘ g) D (convexHull ℝ (range p)))
    (labelH labelJ : LocallyConstant (convexHull ℝ (range p)) PLOrientationSheet)
    (hchange : ∀ z : convexHull ℝ (range p),
      (labelJ z).val =
        plLocalSign (H.symm.trans J) hPL
          ⟨H (g z), H.map_source (hgH z.property), by
            change H.symm (H (g z)) ∈ J.source
            rw [H.left_inv (hgH z.property)]
            exact hgJ z.property⟩ * (labelH z).val) :
    ∀ z w : convexHull ℝ (range p),
      (labelH z).val *
          SignType.sign (b.det ![A (p 1) - A (p 0), A (p 2) - A (p 0), n]) =
        (labelJ w).val *
          SignType.sign (b.det ![D (p 1) - D (p 0), D (p 2) - D (p 0), n']) := by
  have himage : convexHull ℝ (range (A ∘ p)) = A '' convexHull ℝ (range p) := by
    simpa only [range_comp, ContinuousAffineMap.coe_toAffineMap] using
      (A.toAffineMap.image_convexHull (range p)).symm
  obtain ⟨y, hy⟩ := (range_nonempty (A ∘ p)).convexHull.intrinsicInterior
    (convex_convexHull ℝ _)
  obtain ⟨q, hq, hAq⟩ := himage ▸ intrinsicInterior_subset hy
  let qT : convexHull ℝ (range p) := ⟨q, hq⟩
  have hcoord : H (g q) = y := (hA hq).trans hAq
  let x : (H.symm.trans J).source :=
    ⟨H (g q), H.map_source (hgH hq), by
      change H.symm (H (g q)) ∈ J.source
      rw [H.left_inv (hgH hq)]
      exact hgJ hq⟩
  have hs := plLocalSign_mul_frontier_chart_triangle_sign b H J hPL N ell m n n'
    hn hn' hH hJ p hp g hi hgH hgJ hgN A D hA hD x (by
      change H (g q) ∈ intrinsicInterior ℝ (convexHull ℝ (range (A ∘ p)))
      rw [hcoord]
      exact hy)
  have hlabel := hchange qT
  change (labelJ qT).val = plLocalSign (H.symm.trans J) hPL x * (labelH qT).val at hlabel
  have hsq : plLocalSign (H.symm.trans J) hPL x *
      plLocalSign (H.symm.trans J) hPL x = 1 := by
    have hne := plLocalSign_ne_zero (H.symm.trans J) hPL x
    cases he : plLocalSign (H.symm.trans J) hPL x <;> simp_all
  let : PreconnectedSpace (convexHull ℝ (range p)) :=
    isPreconnected_iff_preconnectedSpace.mp (convex_convexHull ℝ (range p)).isPreconnected
  intro z w
  rw [labelH.apply_eq_of_preconnectedSpace z qT, labelJ.apply_eq_of_preconnectedSpace w qT]
  rw [hlabel, ← hs]
  rw [mul_mul_mul_comm, hsq, one_mul]

end Geometry
