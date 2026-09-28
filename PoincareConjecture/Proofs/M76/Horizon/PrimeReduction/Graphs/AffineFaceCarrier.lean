import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceSpan
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]



theorem exists_finite_affine_face_carrier
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (A : E →ᴬ[ℝ] F) :
    ∃ T : SimplicialComplex ℝ F, T.faces.Finite ∧
      T.space = convexHull ℝ (A '' (s : Set E)) := by
  classical
  let R := K.finiteFaceSpan {⟨s, hs⟩}
  have hR : R.faces.Finite := K.finiteFaceSpan_finite _
  have hsR : s ∈ R.faces := (K.finiteFaceSpan_faces _ _).mpr
    ⟨K.nonempty_of_mem_faces hs, ⟨s, hs⟩, by simp, Finset.Subset.rfl⟩
  have hRs : R.space = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
      obtain ⟨_, u, hu, htu⟩ := (K.finiteFaceSpan_faces _ _).mp ht
      have hus : u = ⟨s, hs⟩ := by simpa only [Finset.mem_singleton] using hu
      have hts : t ⊆ s := by simpa only [hus] using htu
      exact convexHull_mono (Finset.coe_subset.mpr hts) hxt
    · exact R.convexHull_subset_space hsR
  obtain ⟨T, hT, hTs, _⟩ := (R.affineOnFaces_affine A).exists_finite_triangulation_image hR
  exact ⟨T, hT, hTs.trans ((congrArg (fun U : Set E => A '' U) hRs).trans
    (A.toAffineMap.image_convexHull _))⟩

end Geometry.SimplicialComplex
