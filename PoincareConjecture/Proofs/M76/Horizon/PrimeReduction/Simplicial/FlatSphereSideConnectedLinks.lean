import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence










set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem isConnected_faceLink_of_flat_side_chart
    (K P N : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hPK : P ≤ K) (hNP : N ≤ P)
    {s : Finset E} (hs : s ∈ N.faces) {p : E} (hps : p ∈ s)
    {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hfi : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hside : (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0})
    (hzero : ∀ x ∈ (K.closedStar p).space, x ∈ N.space ↔ f x 0 = 0) :
    IsConnected (P.faceLink s).space := by
  classical
  let Q := P.closedStar p
  have hQK : Q ≤ K.closedStar p := fun _ ht => ⟨hPK ht.1, hPK ht.2⟩
  have hQs : Q.space ⊆ (K.closedStar p).space := space_subset_of_le hQK
  have hQ : Q.faces.Finite := finite_closedStar_faces (hK.subset hPK) p
  have hsQ : s ∈ Q.faces := ⟨hNP hs, by
    simpa only [Finset.insert_eq_of_mem hps] using hNP hs⟩
  have hfQ : Q.AffineOnFaces f := fun t ht => hf t (hQK ht)
  have hiQ : InjOn f Q.space := hfi.mono hQs
  let J := hfQ.embeddedImage hiQ
  have hJ : J.faces.Finite := hfQ.embeddedImage_finite hiQ hQ
  have hJs : J.space = f '' Q.space := hfQ.embeddedImage_space hiQ
  have hsJ : s.image f ∈ J.faces :=
    (hfQ.image_mem_embeddedImage_iff hiQ (Q.subset_space hsQ)).mpr hsQ
  let ell : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj 0).toContinuousAffineMap
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have he := congrArg (fun A : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => A (fun _ => 1)) h
    change (1 : ℝ) = 0 at he
    exact one_ne_zero he
  have hJhalf : J.space ⊆ {x | 0 ≤ ell x} := by
    rw [hJs]
    rintro y ⟨x, hx, rfl⟩
    exact (hside.subset hx).2
  have hplane : ∀ y ∈ affineSpan ℝ (s.image f : Set (Fin 3 → ℝ)), ell y = 0 := by
    have hv : EqOn ell.toAffineMap (AffineMap.const ℝ (Fin 3 → ℝ) 0)
        (s.image f : Set (Fin 3 → ℝ)) := by
      rintro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (hzero x (hQs (Q.subset_space hsQ hx))).mp (N.subset_space hs hx)
    exact fun y hy => AffineMap.eqOn_affineSpan hv hy
  have hlink : IsConnected (J.faceLink (s.image f)).space := by
    apply J.isConnected_faceLink_of_halfspace_patch hJ hsJ ell hell
      (V := interior (f '' (K.closedStar p).space)) hJhalf hplane isOpen_interior
    · rintro y ⟨hy, hy0⟩
      obtain ⟨x, hx, rfl⟩ := interior_subset hy
      rw [hJs]
      exact ⟨x, hside.symm.subset ⟨hx, hy0⟩, rfl⟩
    · exact ⟨f p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hint⟩
  have hsource := hfQ.isConnected_faceLink_of_embeddedImage hiQ hQ hsQ hlink
  have hQl : Q.faceLink s = P.faceLink s := by
    change (P.closedStar p).faceLink s = P.faceLink s
    rw [← P.closedFaceStar_singleton_eq_closedStar]
    exact P.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hQl] at hsource

end Geometry.SimplicialComplex
