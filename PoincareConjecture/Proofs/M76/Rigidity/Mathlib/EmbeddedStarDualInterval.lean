import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedFaceDimension
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarCofaces
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompleteCofaceDualBlock










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]




theorem exists_dual_interval_of_embedded_star
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = Module.finrank ℝ F)
    {p : E} (hps : p ∈ s) (f : E → F)
    (hf : (K.closedStar p).AffineOnFaces f)
    (hi : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space)) :
    ∃ t ∈ K.faces, ∃ u ∈ K.faces,
      s ⊆ t ∧ s ⊆ u ∧ t.card = Module.finrank ℝ F + 1 ∧
      u.card = Module.finrank ℝ F + 1 ∧ t ≠ u ∧
      (∀ v ∈ K.faces, s ⊆ v → v.card = Module.finrank ℝ F + 1 → v = t ∨ v = u) ∧
      IsFinitePLBallPair ℝ (K.barycentricDualBlock s).space
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      s.centroid ℝ id ∈ (K.barycentricDualBlock s).space \
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id, u.centroid ℝ id} := by
  classical
  have hK : K.faces.Finite := Set.toFinite _
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hcofaces⟩ :=
    K.exists_paired_facet_of_embedded_star hK hs hscard hps f hf hi hint
  let N := K.closedStar p
  have hN : N.faces.Finite := hK.subset (fun _ hv => hv.1)
  let : Fintype N.faces := hN.fintype
  have hNK : N ≤ K := fun _ hv => hv.1
  have hcomplete (v : Finset E) (hv : v ∈ K.faces) (hsv : s ⊆ v) : v ∈ N.faces :=
    ⟨hv, by simpa only [Finset.insert_eq_of_mem (hsv hps)] using hv⟩
  have hsN : s ∈ N.faces := hcomplete s hs Subset.rfl
  have htN : t ∈ N.faces := hcomplete t ht hst
  have huN : u ∈ N.faces := hcomplete u hu hsu
  have hbound : ∀ v ∈ N.faces, v.card ≤ Module.finrank ℝ F + 1 :=
    fun _ hv => hf.face_card_le_of_injOn hi hv
  have hcofacesN : ∀ v ∈ N.faces, s ⊆ v →
      v.card = Module.finrank ℝ F + 1 → v = t ∨ v = u :=
    fun v hv => hcofaces v hv.1
  have heq : N.barycentricDualBlock s = K.barycentricDualBlock s :=
    K.barycentricDualBlock_eq_of_cofaces_in_subcomplex N hNK s hcomplete
  have hpair := N.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    hbound hsN htN huN hscard htc huc hst hsu htu hcofacesN
  have hlink := N.barycentricDualBlock_link_space_of_paired_facet
    hbound hsN htN huN hscard htc huc hst hsu hcofacesN
  rw [heq] at hpair hlink
  exact ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hcofaces, hpair.1, hpair.2, hlink⟩

end Geometry.SimplicialComplex
