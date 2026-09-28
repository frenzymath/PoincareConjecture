import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeLinkInterval
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FlatSphereSideConnectedLinks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FlatSphereSideFacets
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FlatSphereSideInteriorFacets
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FullSubcomplexStars










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem isFinitePLBallPair_sphere_side_edge_link
    (K N P M : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hPK : P ≤ K) (hMK : M ≤ K) (hNP : N ≤ P) (hNM : N ≤ M)
    (hNfull : ∀ t ∈ P.faces, (∀ v ∈ t, v ∈ N.vertices) → t ∈ N.faces)
    (hPpure : ∀ t ∈ P.faces, ∃ u ∈ P.faces, t ⊆ u ∧ u.card = 4)
    (hNcard : ∀ t ∈ N.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ N.faces) (hsc : s.card = 2)
    (hends : (N.faceLink s).vertices.ncard = 2)
    {p : E} (hps : p ∈ s) {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hP : (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0})
    (hM : (M.closedStar p).space = (K.closedStar p).space ∩ {x | f x 0 ≤ 0})
    (hzero : ∀ x ∈ (K.closedStar p).space, x ∈ N.space ↔ f x 0 = 0)
    (hcover : ∀ t ∈ (K.closedStar p).faces, t ∈ P.faces ∨ t ∈ M.faces) :
    IsFinitePLBallPair ℝ (P.faceLink s).space (N.faceLink s).space := by
  classical
  have hPfinite : P.faces.Finite := hK.subset hPK
  have hpN : p ∈ N.vertices := N.down_closed hs
    (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  have hNstar : (N.closedStar p).space = (K.closedStar p).space ∩ {x | f x 0 = 0} := by
    rw [P.closedStar_space_eq_inter_of_full N hPfinite hNP hNfull hpN, hP]
    ext x
    constructor
    · rintro ⟨⟨hxK, _⟩, hxN⟩
      exact ⟨hxK, (hzero x hxK).mp hxN⟩
    · rintro ⟨hxK, hxzero⟩
      exact ⟨⟨hxK, by change 0 ≤ f x 0; rw [hxzero]⟩, (hzero x hxK).mpr hxzero⟩
  have hfacets (t : Finset E) (ht : t ∈ P.faces) (hst : s ⊆ t) (htc : t.card = 3) :
      (t ∈ N.faces → (P.faceLink t).vertices.ncard = 1) ∧
      (t ∉ N.faces → (P.faceLink t).vertices.ncard = 2) := by
    constructor
    · intro htN
      exact (K.faceLink_ncard_eq_one_each_side_of_flat_chart N P M hK hPK hMK hNP hNM
        htN htc (hst hps) hf hinj hint hP hM hNstar hcover).1
    · intro htN
      exact K.faceLink_ncard_eq_two_of_flat_side_unmarked N P hK hPK hNP hNfull
        ht htc htN (hst hps) hpN hf hinj hint hP hNstar
  have hconn := K.isConnected_faceLink_of_flat_side_chart P N hK hPK hNP
    hs hps hf hinj hint hP hzero
  exact P.isFinitePLBallPair_boundary_edge_link_of_local_incidence N hPfinite hNP
    hPpure hNcard hfacets hs hsc hends hconn

end Geometry.SimplicialComplex
