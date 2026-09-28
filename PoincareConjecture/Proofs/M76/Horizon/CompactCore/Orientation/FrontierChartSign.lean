import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.BoundaryTriangleSign
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.AffineChartTransition

set_option autoImplicit false

open Set

namespace Geometry

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace X]

theorem plLocalSign_mul_frontier_chart_triangle_sign
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
    (x : (H.symm.trans J).source)
    (hx : (x : F) ∈ intrinsicInterior ℝ (convexHull ℝ (range (A ∘ p)))) :
    plLocalSign (H.symm.trans J) hPL x *
        SignType.sign (b.det ![A (p 1) - A (p 0), A (p 2) - A (p 0), n]) =
      SignType.sign (b.det ![D (p 1) - D (p 0), D (p 2) - D (p 0), n']) := by
  let r := H.symm.trans J
  have hAi : InjOn A (convexHull ℝ (range p)) := by
    intro y hy z hz heq
    apply hi hy hz
    exact H.injOn (hgH hy) (hgH hz)
      ((hA hy).trans (heq.trans (hA hz).symm))
  have hformula (z : E) (hz : z ∈ convexHull ℝ (range p)) : r (A z) = D z := by
    change J (H.symm (A z)) = D z
    rw [← hA hz]
    change J (H.symm (H (g z))) = D z
    rw [H.left_inv (hgH hz)]
    exact hD hz
  obtain ⟨hpA, B, hB⟩ := exists_affine_transition_on_convexHull p hp A D hAi r hformula
  have himage : convexHull ℝ (range (A ∘ p)) = A '' convexHull ℝ (range p) := by
    simpa only [range_comp, ContinuousAffineMap.coe_toAffineMap] using
      (A.toAffineMap.image_convexHull (range p)).symm
  have hsource : convexHull ℝ (range (A ∘ p)) ⊆ r.source := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := himage ▸ hy
    rw [← hA hz]
    exact ⟨H.map_source (hgH hz), by
      change H.symm (H (g z)) ∈ J.source
      rw [H.left_inv (hgH hz)]
      exact hgJ hz⟩
  have hside (y : F) (hy : y ∈ r.source) : 0 ≤ m (r y) ↔ 0 ≤ ell y := by
    have hleft := hH (H.symm y) (H.map_target hy.1)
    rw [H.right_inv hy.1] at hleft
    exact (hJ (H.symm y) hy.2).symm.trans hleft
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz : ell.contLinear n = 0 := congrArg (fun L : F →ₗ[ℝ] ℝ => L n) he
    rw [hn] at hz
    norm_num at hz
  have hfront := H.isImage_frontier_of_affine_nonneg ell hell hH
  have hz (i : Fin 3) : ell ((A ∘ p) i) = 0 := by
    have hpi := subset_convexHull ℝ (range p) (mem_range_self i)
    change ell (A (p i)) = 0
    rw [← hA hpi]
    exact (hfront.apply_mem_iff (hgH hpi)).mpr (hgN hpi)
  have hsign := plLocalSign_mul_triangle_det_sign b r hPL ell m n n' B hn hn'
    (A ∘ p) hpA hz hsource hside hB x hx
  have hvertices (i : Fin 3) : B (A (p i)) = D (p i) :=
    (hB (subset_convexHull ℝ _ (mem_range_self i))).symm.trans
      (hformula (p i) (subset_convexHull ℝ _ (mem_range_self i)))
  simpa only [Function.comp_apply, hvertices] using hsign

end Geometry
