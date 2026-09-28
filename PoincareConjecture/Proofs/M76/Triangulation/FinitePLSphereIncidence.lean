import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereDisks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskStarSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarPurity
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount












set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem IsFinitePL.exists_height_aligned_surface_complex
    {s : Set E} {C : Set F} {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3) (A : E →ᵃ[ℝ] ℝ) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = s ∧
      K.RespectsAffineHyperplane A ∧
      (∀ t ∈ K.faces, ∃ u ∈ K.faces, u.card = 3 ∧ t ⊆ u) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      ∀ p ∈ K.vertices, IsConnected (K.link p).space := by
  have hcopy := he
  obtain ⟨_, ⟨J, hJ, hJs, _⟩, _⟩ := hcopy
  have hlocal (x : J.space) : ∃ d q : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ J.space ∧ (x : E) ∈ d \ q ∧
        IsOpen ((Subtype.val : J.space → E) ⁻¹' (d \ q)) := by
    obtain ⟨d, q, hd, hds, hx, hopen⟩ :=
      he.exists_local_ball_pairs_of_convex_frontier hC hcv hne
        (V := ℝ × ℝ) (by simpa using hdim) ⟨x, hJs.subset x.property⟩
    refine ⟨d, q, hd, hds.trans hJs.symm.subset, hx, ?_⟩
    exact hopen.preimage (Homeomorph.setCongr hJs).continuous
  obtain ⟨K, hK, hKJ, hKA, hstars⟩ :=
    J.exists_faceAffine_vertex_stars_of_local_ball_pairs hJ hlocal A
  have hdim2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  refine ⟨K, hK, hKJ.space_eq.trans hJs, hKA, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, htu, huc⟩ := K.exists_full_coface_of_faceAffine_vertex_stars hK hstars t ht
    exact ⟨u, hu, by simpa only [hdim2] using huc, htu⟩
  · intro t ht htc
    have hlink := K.faceLink_ncard_eq_two_of_faceAffine_vertex_stars hK hstars t ht
      (htc.trans hdim2.symm)
    rw [K.ncard_faceLink_vertices_eq_cofaces, htc] at hlink
    exact hlink
  · intro p hp
    have hlink := K.isConnected_faceLink_of_faceAffine_vertex_stars hK hstars {p} hp
      (by simp [hdim2])
    simpa only [Geometry.SimplicialComplex.faceLink_singleton_eq_link] using hlink

end Homeomorph
