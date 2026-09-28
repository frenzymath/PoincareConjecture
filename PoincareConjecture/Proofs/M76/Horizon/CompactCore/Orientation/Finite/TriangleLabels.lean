import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.LabeledTriangleSign
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.FrontierStarCoordinates

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]

theorem component_labeled_triangle_sign_eq
    (J : SimplicialComplex ℝ E) (g : E → X) (N : Set X)
    (q : κ → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (q i).symm.trans (q j) ∈ piecewiseAffineGroupoid V3)
    (label : ∀ i, LocallyConstant {z : J.space | g z ∈ (q i).source} PLOrientationSheet)
    (hchange : ∀ i j (z : J.space) (hi : g z ∈ (q i).source)
      (hj : g z ∈ (q j).source),
      (label j ⟨z, hj⟩).val =
        plAtlasTransitionSign q hcompat i j ⟨g z, hi, hj⟩ * (label i ⟨z, hi⟩).val)
    (b : Module.Basis (Fin 3) ℝ V3)
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hspace : convexHull ℝ (range p) ⊆ J.space)
    (hgi : InjOn g J.space) (hfront : MapsTo g J.space (frontier N))
    (i j : κ) (ell m : V3 →ᴬ[ℝ] ℝ) (n n' : V3)
    (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (hi : MapsTo g (convexHull ℝ (range p)) (q i).source)
    (hj : MapsTo g (convexHull ℝ (range p)) (q j).source)
    (hsidei : ∀ y ∈ (q i).source, y ∈ N ↔ 0 ≤ ell (q i y))
    (hsidej : ∀ y ∈ (q j).source, y ∈ N ↔ 0 ≤ m (q j y))
    (A D : E →ᴬ[ℝ] V3)
    (hA : EqOn (q i ∘ g) A (convexHull ℝ (range p)))
    (hD : EqOn (q j ∘ g) D (convexHull ℝ (range p)))
    (z w : convexHull ℝ (range p)) :
    (label i ⟨⟨z, hspace z.property⟩, hi z.property⟩).val *
        SignType.sign (b.det ![q i (g (p 1)) - q i (g (p 0)),
          q i (g (p 2)) - q i (g (p 0)), n]) =
      (label j ⟨⟨w, hspace w.property⟩, hj w.property⟩).val *
        SignType.sign (b.det ![q j (g (p 1)) - q j (g (p 0)),
          q j (g (p 2)) - q j (g (p 0)), n']) := by
  let restrict (k : κ) (hk : MapsTo g (convexHull ℝ (range p)) (q k).source) :
      C(convexHull ℝ (range p), {z : J.space | g z ∈ (q k).source}) :=
    ⟨fun x => ⟨⟨x, hspace x.property⟩, hk x.property⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  have h := labeled_frontier_triangle_sign_eq b (q i) (q j) (hcompat i j)
    N ell m n n' hn hn' hsidei hsidej p hp g (hgi.mono hspace) hi hj
    (fun _ hx => hfront (hspace hx)) A D hA hD
    (LocallyConstant.comap (restrict i hi) (label i))
    (LocallyConstant.comap (restrict j hj) (label j))
    (fun x => hchange i j ⟨x, hspace x.property⟩ (hi x.property) (hj x.property)) z w
  have hAi (k : Fin 3) : A (p k) = q i (g (p k)) :=
    (hA (subset_convexHull ℝ _ (mem_range_self k))).symm
  have hDj (k : Fin 3) : D (p k) = q j (g (p k)) :=
    (hD (subset_convexHull ℝ _ (mem_range_self k))).symm
  simpa only [hAi, hDj, LocallyConstant.coe_comap_apply, restrict,
    ContinuousMap.coe_mk] using h

theorem frontier_triangle_coordinate_det_ne_zero
    (J : SimplicialComplex ℝ E) (g : E → X) (N : Set X)
    (hgi : InjOn g J.space) (hfront : MapsTo g J.space (frontier N))
    (b : Module.Basis (Fin 3) ℝ V3)
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hspace : convexHull ℝ (range p) ⊆ J.space)
    (H : OpenPartialHomeomorph X V3) (ell : V3 →ᴬ[ℝ] ℝ) (n : V3)
    (hn : ell.contLinear n = 1)
    (hsource : MapsTo g (convexHull ℝ (range p)) H.source)
    (hside : ∀ y ∈ H.source, y ∈ N ↔ 0 ≤ ell (H y))
    (A : E →ᴬ[ℝ] V3) (hA : EqOn (H ∘ g) A (convexHull ℝ (range p))) :
    b.det ![H (g (p 1)) - H (g (p 0)), H (g (p 2)) - H (g (p 0)), n] ≠ 0 := by
  have hAi : InjOn A (convexHull ℝ (range p)) := by
    intro x hx y hy he
    apply hgi (hspace hx) (hspace hy)
    apply H.injOn (hsource hx) (hsource hy)
    exact (hA hx).trans (he.trans (hA hy).symm)
  have hpa := A.toAffineMap.affineIndependent_comp_of_injOn_convexHull hp hAi
  have heq : A.toAffineMap ∘ p = H ∘ g ∘ p := by
    funext k
    exact (hA (subset_convexHull ℝ _ (mem_range_self k))).symm
  rw [heq] at hpa
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz : ell.contLinear n = 0 := congrArg (fun L : V3 →ₗ[ℝ] ℝ => L n) he
    rw [hn] at hz
    norm_num at hz
  have hf := H.isImage_frontier_of_affine_nonneg ell hell hside
  apply boundary_triangle_det_ne_zero b ell n hn (H ∘ g ∘ p) hpa
  intro k
  have hk := subset_convexHull ℝ (range p) (mem_range_self k)
  exact (hf.apply_mem_iff (hsource hk)).mpr (hfront (hspace hk))

end PoincareConjecture.M76
