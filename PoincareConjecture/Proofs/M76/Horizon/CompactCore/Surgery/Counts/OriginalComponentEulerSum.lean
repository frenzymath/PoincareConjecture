import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.ComponentEulerSum
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.FinitePLImageFaceBounds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PLSurfaceCount
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains
open scoped BigOperators

namespace PoincareConjecture.M76

open Classical in
theorem surfaceEulerCount_eq_original_component_sum
    {E G X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {F : Set X}
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (hdim : ∀ s ∈ A.faces, s.card ≤ 3)
    {n : ℕ} (pick : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (g : E → X) (hg : PolyhedralPLInCharts e g A.space) (hgi : InjOn g A.space)
    (hcover : (⋃ i, g '' (A.edgeComponentComplex (pick i)).space) = F)
    (phi : X → G) (hphi : InjOn phi F)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (T : SimplicialComplex ℝ G) (hT : T.faces.Finite) (hTs : T.space = phi '' F) :
    T.surfaceEulerCount = ∑ i, (A.edgeComponentComplex (pick i)).surfaceEulerCount := by
  let S := A.selectedEdgeComponents (Finset.univ.map pick)
  have hSA : S ≤ A := A.selectedEdgeComponents_le _
  have hS : S.faces.Finite := hA.subset hSA
  have hSspace : S.space = ⋃ i, (A.edgeComponentComplex (pick i)).space := by
    rw [show S.space = _ from A.selectedEdgeComponents_space _]
    ext z
    simp
  have hgF : g '' S.space = F := by
    rw [hSspace, image_iUnion]
    exact hcover
  have hgS : PolyhedralPLInCharts e g S.space :=
    hg.restrict_finite S hS (SimplicialComplex.space_subset_of_le hSA)
  have hPL : FinitePiecewiseAffineOn (phi ∘ g) S.space :=
    hgS.finitePiecewiseAffineOn_comp S hS hphiPL
  have hImage : (phi ∘ g) '' S.space = T.space := by
    rw [hTs, ← hgF, image_image]
    rfl
  have hdimS : ∀ s ∈ S.faces, s.card ≤ 3 := fun s hs => hdim s (hSA hs)
  have hdimT := hPL.face_card_le_of_image hS hdimS T hImage.symm.subset
  have hInjective : InjOn (phi ∘ g) S.space := by
    intro x hx y hy hxy
    apply hgi (SimplicialComplex.space_subset_of_le hSA hx)
      (SimplicialComplex.space_subset_of_le hSA hy)
    exact hphi (hgF.subset ⟨x, hx, rfl⟩) (hgF.subset ⟨y, hy, rfl⟩) hxy
  have hcount := hPL.surfaceEulerCount_eq_of_injOn hS hT hdimS hdimT hInjective hImage
  exact hcount.symm.trans (A.selectedEdgeComponents_surfaceEulerCount_indexed hA pick)

open Classical in
theorem surfaceEulerCount_eq_original_component_genus_sum
    {E G X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {F : Set X}
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (hdim : ∀ s ∈ A.faces, s.card ≤ 3)
    {n : ℕ} (pick : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (g : E → X) (hg : PolyhedralPLInCharts e g A.space) (hgi : InjOn g A.space)
    (hcover : (⋃ i, g '' (A.edgeComponentComplex (pick i)).space) = F)
    (phi : X → G) (hphi : InjOn phi F)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (T : SimplicialComplex ℝ G) (hT : T.faces.Finite) (hTs : T.space = phi '' F)
    (genus : Fin n → ℕ)
    (hgenus : ∀ i, Nat.card (A.edgeComponentComplex (pick i)).vertices +
      Nat.card (Triangle
        (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * genus i = Nat.card (Edge
        (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    T.surfaceEulerCount = ∑ i, (2 - 2 * (genus i : ℤ)) := by
  rw [surfaceEulerCount_eq_original_component_sum A hA hdim pick g hg hgi hcover
    phi hphi hphiPL T hT hTs]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (A.edgeComponentComplex (pick i)).surfaceEulerCount_eq_two_sub_residual (hgenus i)

end PoincareConjecture.M76
