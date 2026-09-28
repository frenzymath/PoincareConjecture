import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FinitePLBallPurity
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.VertexStarSideCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FullSubcomplexStars











set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem exists_tetrahedral_coface_of_flat_side_stars
    (K T P N : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hTK : T ≤ K) (hPT : P ≤ T) (hNP : N ≤ P)
    (hfull : ∀ a ∈ T.faces, (∀ v ∈ a, v ∈ P.vertices) → a ∈ P.faces)
    (hcover : T.faces = ⋃ p : N.vertices, (K.closedStar p).faces)
    (hcharts : ∀ p : N.vertices, ∃ f : E → (Fin 3 → ℝ),
      (K.closedStar p).AffineOnFaces f ∧ InjOn f (K.closedStar p).space ∧
      f p 0 = 0 ∧ f p ∈ interior (f '' (K.closedStar p).space) ∧
      (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0}) :
    ∀ a ∈ P.faces, ∃ b ∈ P.faces, a ⊆ b ∧ b.card = 4 := by
  intro a ha
  obtain ⟨p, hpa⟩ := mem_iUnion.mp (hcover.subset (hPT ha))
  have hPK : P ≤ K := fun _ hs => hTK (hPT hs)
  have hpP : (p : E) ∈ P.vertices := hNP p.property
  have hpK : (p : E) ∈ K.vertices := hPK hpP
  have hstarT : K.closedStar (p : E) ≤ T := by
    intro b hb
    exact hcover.symm.subset (mem_iUnion.mpr ⟨p, hb⟩)
  have hjoinT : insert (p : E) a ∈ T.faces := hstarT
    ⟨hpa.2, by simpa only [Finset.insert_idem] using hpa.2⟩
  have hjoinP : insert (p : E) a ∈ P.faces := hfull _ hjoinT (by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hpP
    · exact P.face_subset_vertices ha hv)
  have haPstar : a ∈ (P.closedStar p).faces := ⟨ha, hjoinP⟩
  obtain ⟨f, hf, hfi, hzero, hint, hside⟩ := hcharts p
  obtain ⟨_, _, _, _, _, _, _, _, hball, _, _, _⟩ :=
    K.exists_closedStar_side_chart P hK hPK hpK hf hfi hzero hint hside
  have hstarle : P.closedStar (p : E) ≤ K.closedStar p :=
    fun _ hs => ⟨hPK hs.1, hPK hs.2⟩
  have hfP : (P.closedStar p).AffineOnFaces f := fun b hb => hf b (hstarle hb)
  obtain ⟨b, hb, hab, hbc⟩ := (P.closedStar p).exists_full_coface_of_finitePLBallPair_chart
    (finite_closedStar_faces (hK.subset hPK) p) hball hfP
    (hfi.mono (space_subset_of_le hstarle)) haPstar
  exact ⟨b, hb.1, hab, by simpa using hbc⟩

end Geometry.SimplicialComplex
