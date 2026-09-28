import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.TriangleLabels

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem exists_frontier_triangle_sign
    (e : ι → OpenPartialHomeomorph X V3)
    (K J : SimplicialComplex ℝ E) (hJK : J ≤ K) (g : E → X) (N : Set X)
    (hgi : InjOn g K.space) (hfront : MapsTo g J.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (C ∘ g) ∧
      (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)))
    (b : Module.Basis (Fin 3) ℝ V3)
    (t : Finset E) (ht : t ∈ J.faces) (p : Fin 3 → E)
    (hp : AffineIndependent ℝ p) (hpt : ∀ k, p k ∈ t) :
    let charts := {H : OpenPartialHomeomorph X V3 |
      ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3}
    let q : charts → OpenPartialHomeomorph X V3 := Subtype.val
    ∀ (hq : ∀ H D, (q H).symm.trans (q D) ∈ piecewiseAffineGroupoid V3)
      (label : ∀ H, LocallyConstant {z : J.space | g z ∈ (q H).source} PLOrientationSheet),
      (∀ H D (z : J.space) (hH : g z ∈ (q H).source) (hD : g z ∈ (q D).source),
        (label D ⟨z, hD⟩).val =
          plAtlasTransitionSign q hq H D ⟨g z, hH, hD⟩ * (label H ⟨z, hH⟩).val) →
      ∃ s : SignType, s ≠ 0 ∧
        ∀ (H : charts) (ell : V3 →ᴬ[ℝ] ℝ) (n : V3)
          (_hn : ell.contLinear n = 1)
          (hH : MapsTo g (convexHull ℝ (range p)) (q H).source)
          (_hside : ∀ y ∈ (q H).source, y ∈ N ↔ 0 ≤ ell (q H y))
          (D : E →ᴬ[ℝ] V3) (_hD : EqOn (q H ∘ g) D (convexHull ℝ (range p)))
          (z : convexHull ℝ (range p)),
          s = (label H ⟨⟨z, J.convexHull_subset_space ht
            (convexHull_mono (by rintro _ ⟨k, rfl⟩; exact hpt k) z.property)⟩,
              hH z.property⟩).val *
            SignType.sign (b.det ![q H (g (p 1)) - q H (g (p 0)),
              q H (g (p 2)) - q H (g (p 0)), n]) := by
  intro charts q hq label hchange
  have hspace : convexHull ℝ (range p) ⊆ J.space :=
    fun _ hx => J.convexHull_subset_space ht
      (convexHull_mono (by rintro _ ⟨k, rfl⟩; exact hpt k) hx)
  have hp0 : p 0 ∈ J.vertices := J.mem_vertices.mpr
    (J.down_closed ht (Finset.singleton_subset_iff.mpr (hpt 0)) (Finset.singleton_nonempty _))
  obtain ⟨C, ell, n, hC, hsource, haff, hi, hn, hside, hplane⟩ :=
    exists_frontier_subcomplex_star_coordinates e K J hJK g N hgi hfront hstars (p 0) hp0
  let H : charts := ⟨C, hC⟩
  have htstar : t ∈ (J.closedStar (p 0)).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hpt 0)] using ht⟩
  have hhull : convexHull ℝ (range p) ⊆ (J.closedStar (p 0)).space :=
    fun _ hx => (J.closedStar (p 0)).convexHull_subset_space htstar
      (convexHull_mono (by rintro _ ⟨k, rfl⟩; exact hpt k) hx)
  have hHs : MapsTo g (convexHull ℝ (range p)) (q H).source :=
    fun _ hx => hsource (hhull hx)
  obtain ⟨A, hA⟩ := haff t htstar
  have hAp : EqOn (q H ∘ g) A (convexHull ℝ (range p)) :=
    fun _ hx => hA (convexHull_mono (by rintro _ ⟨k, rfl⟩; exact hpt k) hx)
  let z0 : convexHull ℝ (range p) := ⟨p 0, subset_convexHull ℝ _ (mem_range_self 0)⟩
  let s := (label H ⟨⟨z0, hspace z0.property⟩, hHs z0.property⟩).val *
    SignType.sign (b.det ![C (g (p 1)) - C (g (p 0)), C (g (p 2)) - C (g (p 0)), n])
  have hgiJ : InjOn g J.space := hgi.mono (Geometry.SimplicialComplex.space_subset_of_le hJK)
  have hdet := frontier_triangle_coordinate_det_ne_zero J g N hgiJ hfront b p hp hspace
    C ell n hn hHs hside A hAp
  refine ⟨s, ?_, ?_⟩
  · apply mul_ne_zero
    · exact (label H ⟨⟨z0, hspace z0.property⟩, hHs z0.property⟩).property
    · exact sign_ne_zero.mpr hdet
  · intro D m n' hn' hDs hDside B hB w
    exact component_labeled_triangle_sign_eq J g N q hq label hchange b p hp hspace
      hgiJ hfront H D ell m n n' hn hn' hHs hDs hside hDside A B hAp hB z0 w

end PoincareConjecture.M76
