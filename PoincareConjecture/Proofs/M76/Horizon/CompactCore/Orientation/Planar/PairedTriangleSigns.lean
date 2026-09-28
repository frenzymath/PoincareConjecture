import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Planar.ZeroPlaneProjection










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem AffineOnFaces.opposite_centroid_signs_in_zero_plane
    (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (hdim : Module.finrank ℝ F = 3)
    (ell : F →ᴬ[ℝ] ℝ) (n o : F) (hn : ell.contLinear n = 1)
    (ho : ell o = 0) (hplane : ∀ x ∈ K.space, ell (f x) = 0)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = 2) (htc : t.card = 3) (huc : u.card = 3)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (L : F →ₗ[ℝ] ℝ) (hzero : ∀ x ∈ s, L (f x - o) = 0)
    (v : E) (hv : v ∈ K.space) (hvL : L (f v - o) ≠ 0) :
    (L (f (t.centroid ℝ id) - o) < 0 ∧ 0 < L (f (u.centroid ℝ id) - o)) ∨
      (0 < L (f (t.centroid ℝ id) - o) ∧ L (f (u.centroid ℝ id) - o) < 0) := by
  obtain ⟨P, _, hon, hPi, hdimP⟩ := exists_zero_plane_projection ell n o hn ho
  have hdim2 : Module.finrank ℝ (LinearMap.ker ell.toAffineMap.linear) = 2 := by omega
  let q := P ∘ f
  have hq : K.AffineOnFaces q := hf.postcomp P
  have hqi : InjOn q K.space := by
    intro x hx y hy he
    exact hi hx hy (hPi (hplane x hx) (hplane y hy) he)
  let L' : LinearMap.ker ell.toAffineMap.linear →ₗ[ℝ] ℝ :=
    L.comp (LinearMap.ker ell.toAffineMap.linear).subtype
  have heval (x : E) (hx : x ∈ K.space) : L' (q x) = L (f x - o) := by
    change L (P (f x)) = L (f x - o)
    rw [hon _ (hplane x hx)]
  have hL : L'.toAffineMap.linear ≠ 0 := by
    intro he
    have hz : L' (q v) = 0 := congrArg (fun M : LinearMap.ker ell.toAffineMap.linear →ₗ[ℝ] ℝ => M (q v)) he
    exact hvL ((heval v hv).symm.trans hz)
  have hsign := hq.opposite_centroid_signs hqi hs ht hu
    (hsc.trans hdim2.symm) (by omega) (by omega) hst hsu htu L'.toAffineMap hL
    (by intro x hx; exact (heval x (K.subset_space hs hx)).trans (hzero x hx))
  change (L' (q (t.centroid ℝ id)) < 0 ∧ 0 < L' (q (u.centroid ℝ id))) ∨
    (0 < L' (q (t.centroid ℝ id)) ∧ L' (q (u.centroid ℝ id)) < 0) at hsign
  rw [heval _ (K.convexHull_subset_space ht
    (t.centroid_mem_convexHull (K.nonempty_of_mem_faces ht))),
    heval _ (K.convexHull_subset_space hu
      (u.centroid_mem_convexHull (K.nonempty_of_mem_faces hu)))] at hsign
  exact hsign

end Geometry.SimplicialComplex
