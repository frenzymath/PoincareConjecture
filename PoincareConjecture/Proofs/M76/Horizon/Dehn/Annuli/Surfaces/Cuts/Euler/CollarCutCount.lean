import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.Euler.AnnulusCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.Euler.DisjointUnion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplement
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.ComponentEulerSum



set_option autoImplicit false
open Set Metric Geometry
open scoped BigOperators

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype β]

theorem collar_cut_surfaceEulerCount
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (A : Bool → SimplicialComplex ℝ E) (hN : N.faces = ⋃ b, (A b).faces)
    (hAdis : Disjoint (A false).space (A true).space)
    (c : ∀ b, PLAnnularStrip.squareAnnulus 1 (1 / 8 : ℝ) ≃ₜ (A b).space)
    (hc : ∀ b, (c b).IsFinitePL)
    (B : β → SimplicialComplex ℝ E)
    (hB : (N ⊓ K.closedFaceComplement N).faces = ⋃ i, (B i).faces)
    (hBdis : Pairwise (fun i j ↦ Disjoint (B i).space (B j).space))
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (B i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL) :
    (K.closedFaceComplement N).surfaceEulerCount = K.surfaceEulerCount := by
  have hNA (b : Bool) : A b ≤ N := by
    intro s hs
    change s ∈ N.faces
    rw [hN]
    exact mem_iUnion.mpr ⟨b, hs⟩
  have hAf (b : Bool) : (A b).faces.Finite := hK.subset ((hNA b).trans hNK)
  have hApair : Pairwise (fun i j ↦ Disjoint (A i).space (A j).space) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hAdis
    · exact hAdis.symm
    · exact (hij rfl).elim
  have hNzero : N.surfaceEulerCount = 0 := by
    rw [N.surfaceEulerCount_disjoint_family A hAf hN hApair]
    exact Finset.sum_eq_zero (fun b _ ↦ annulus_surfaceEulerCount (A b) (hAf b) (c b) (hc b))
  have hBK (i : β) : B i ≤ K := by
    intro s hs
    have hmem : s ∈ (N ⊓ K.closedFaceComplement N).faces := by
      rw [hB]
      exact mem_iUnion.mpr ⟨i, hs⟩
    exact hNK hmem.1
  have hBf (i : β) : (B i).faces.Finite := hK.subset (hBK i)
  have hBzero : (N ⊓ K.closedFaceComplement N).surfaceEulerCount = 0 := by
    rw [(N ⊓ K.closedFaceComplement N).surfaceEulerCount_disjoint_family B hBf hB hBdis]
    exact Finset.sum_eq_zero (fun i _ ↦ circle_surfaceEulerCount (B i) (hBf i)
      (gamma i) (hgamma i))
  have h := K.closedFaceComplement_euler N hK hNK
  omega

theorem barycentric_collar_cut_surfaceEulerCount
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (hdim : ∀ s ∈ K.faces, s.card ≤ 3)
    (N : SimplicialComplex ℝ E) (hNK : N ≤ K.barycentricSubdivision)
    (A : Bool → SimplicialComplex ℝ E) (hN : N.faces = ⋃ b, (A b).faces)
    (hAdis : Disjoint (A false).space (A true).space)
    (c : ∀ b, PLAnnularStrip.squareAnnulus 1 (1 / 8 : ℝ) ≃ₜ (A b).space)
    (hc : ∀ b, (c b).IsFinitePL)
    (B : β → SimplicialComplex ℝ E)
    (hB : (N ⊓ K.barycentricSubdivision.closedFaceComplement N).faces = ⋃ i, (B i).faces)
    (hBdis : Pairwise (fun i j ↦ Disjoint (B i).space (B j).space))
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (B i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL) :
    (K.barycentricSubdivision.closedFaceComplement N).surfaceEulerCount = K.surfaceEulerCount := by
  have hK : K.faces.Finite := Set.toFinite _
  have hD := K.barycentricSubdivision_finite
  have hDs := K.barycentricSubdivision_isSubdivision.space_eq
  have hdimD : ∀ s ∈ K.barycentricSubdivision.faces, s.card ≤ 3 := by
    intro s hs
    exact K.barycentricSubdivision.face_card_le_of_hull_subset_finite_carrier K hK hs
      ((K.barycentricSubdivision.convexHull_subset_space hs).trans hDs.subset) hdim
  exact (collar_cut_surfaceEulerCount K.barycentricSubdivision N hD hNK A hN hAdis c hc
    B hB hBdis gamma hgamma).trans
      (K.barycentricSubdivision.surfaceEulerCount_eq_of_space_eq K hD hK hdimD hdim hDs)

end PoincareConjecture.M76.Dehn.Annuli
