import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionMarkedImages
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionRetainedIntersections
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.RetainedFrontierClosure
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionOldComponent
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClosedComplementSubcomplex
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialCompatibleUnion











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_retained_frontier_graph_model
    {E Eold X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup Eold] [NormedSpace ℝ Eold]
    [FiniteDimensional ℝ Eold] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (phi : X → E) (hphi : Continuous phi) (hinj : InjOn phi (F ∪ P.closedStrip))
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hFK : phi '' F ⊆ K.space) (hBK : phi '' P.closedStrip ⊆ K.space)
    {n : ℕ} (Old : Fin n → SimplicialComplex ℝ Eold) (g : Eold → X)
    (hOld : ∀ i, (Old i).faces.Finite)
    (hg : ∀ i, PolyhedralPLInCharts e g (Old i).space)
    (hOldF : (⋃ i, g '' (Old i).space) = F) :
    ∃ (R Aold Anew Retained Annulus CapUnion : SimplicialComplex ℝ E)
      (Caps Rims : Bool → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      Aold ≤ R ∧ Anew ≤ R ∧ Retained ≤ R ∧ Annulus ≤ R ∧ CapUnion ≤ R ∧
      Aold.space = phi '' F ∧
      Anew.space = phi '' ((F \ P.openStrip) ∪ P.endDisks) ∧
      Retained.space = phi '' (F \ P.openStrip) ∧
      Annulus.space = phi '' (F ∩ P.closedStrip) ∧
      CapUnion.space = phi '' P.endDisks ∧
      Aold.faces = Retained.faces ∪ Annulus.faces ∧
      Anew.faces = Retained.faces ∪ CapUnion.faces ∧
      Retained ⊓ Annulus = Retained ⊓ CapUnion ∧
      CapUnion.faces = (Caps false).faces ∪ (Caps true).faces ∧
      (∀ b, Caps b ≤ R ∧ (Caps b).space = phi '' P.capDisk b) ∧
      (∀ b, Rims b ≤ R ∧ (Rims b).space = phi '' P.capRimSet b) ∧
      ∀ b, Retained ⊓ Caps b = Rims b := by
  obtain ⟨R, A, Block, Ann, Caps, Rims, hR, hRK, hAR, hAs, _, _, hAnnR, hAnns,
    hCaps, hRims⟩ :=
    P.exists_marked_compression_images phi hphiPL K hK hFK hBK Old g hOld hg hOldF
  have hAnnEq : Ann.space = phi '' (F ∩ P.closedStrip) := by
    rw [hAnns, P.frontier_mark_inter_closedStrip hcut hsmall]
  have hAnnA : Ann ≤ A := R.le_of_common_subcomplex_space_subset Ann A hAnnR hAR (by
    rw [hAnnEq, hAs]
    exact image_mono inter_subset_left)
  obtain ⟨Retained, hRetA, _, hRetSpace, _⟩ :=
    A.exists_closedComplement_subcomplex Ann (hR.subset hAR) hAnnA
  have hRetR : Retained ≤ R := hRetA.trans hAR
  have hRetEq : Retained.space = phi '' (F \ P.openStrip) := by
    rw [hRetSpace, hAs, hAnnEq]
    exact P.closure_graph_frontier_sdiff_annulus hF hcut hsmall hlateral
      phi hphi (hinj.mono subset_union_left)
  let CapUnion := (Caps false).unionOfCompatible (Caps true)
    (fun _ hs _ ht => R.inter_subset_convexHull ((hCaps false).1 hs) ((hCaps true).1 ht))
  have hCapUR : CapUnion ≤ R := by
    rintro s (hs | hs)
    · exact (hCaps false).1 hs
    · exact (hCaps true).1 hs
  have hCapUSpace : CapUnion.space = phi '' P.endDisks := by
    rw [show CapUnion.space = _ from (Caps false).space_unionOfCompatible _ _,
      (hCaps false).2, (hCaps true).2, ← image_union, P.endDisks_eq_capDisks]
  let Anew := Retained.unionOfCompatible CapUnion
    (fun _ hs _ ht => R.inter_subset_convexHull (hRetR hs) (hCapUR ht))
  have hNewR : Anew ≤ R := by
    rintro s (hs | hs)
    · exact hRetR hs
    · exact hCapUR hs
  have hNewSpace : Anew.space = phi '' ((F \ P.openStrip) ∪ P.endDisks) := by
    rw [show Anew.space = _ from Retained.space_unionOfCompatible _ _,
      hRetEq, hCapUSpace, image_union]
  let Aunion := Retained.unionOfCompatible Ann
    (fun _ hs _ ht => R.inter_subset_convexHull (hRetR hs) (hAnnR ht))
  have hUnionR : Aunion ≤ R := by
    rintro s (hs | hs)
    · exact hRetR hs
    · exact hAnnR hs
  have hUnionSpace : Aunion.space = A.space := by
    rw [show Aunion.space = _ from Retained.space_unionOfCompatible _ _,
      hRetEq, hAnnEq, ← image_union, P.retained_union_annulus, hAs]
  have hUnionEq : Aunion = A := le_antisymm
    (R.le_of_common_subcomplex_space_subset _ _ hUnionR hAR hUnionSpace.subset)
    (R.le_of_common_subcomplex_space_subset _ _ hAR hUnionR hUnionSpace.symm.subset)
  have hRetSub : F \ P.openStrip ⊆ F ∪ P.closedStrip := sdiff_subset.trans subset_union_left
  have hAnnSub : F ∩ P.closedStrip ⊆ F ∪ P.closedStrip :=
    inter_subset_left.trans subset_union_left
  have hCapSub : P.endDisks ⊆ F ∪ P.closedStrip :=
    P.endDisks_subset_closedStrip.trans subset_union_right
  have hGlueSpace : (Retained ⊓ Ann).space = (Retained ⊓ CapUnion).space := by
    rw [R.space_inf_eq_inter_of_le _ _ hRetR hAnnR,
      R.space_inf_eq_inter_of_le _ _ hRetR hCapUR, hRetEq, hAnnEq, hCapUSpace,
      ← hinj.image_inter hRetSub hAnnSub, ← hinj.image_inter hRetSub hCapSub,
      P.retained_inter_annulus_eq_inter_endDisks]
  have hGlue : Retained ⊓ Ann = Retained ⊓ CapUnion := le_antisymm
    (R.le_of_common_subcomplex_space_subset _ _ (inf_le_left.trans hRetR)
      (inf_le_left.trans hRetR) hGlueSpace.subset)
    (R.le_of_common_subcomplex_space_subset _ _ (inf_le_left.trans hRetR)
      (inf_le_left.trans hRetR) hGlueSpace.symm.subset)
  refine ⟨R, A, Anew, Retained, Ann, CapUnion, Caps, Rims,
    hR, hRK, hAR, hNewR, hRetR, hAnnR, hCapUR, hAs, hNewSpace, hRetEq,
    hAnnEq, hCapUSpace, ?_, rfl, hGlue, rfl, hCaps, hRims, ?_⟩
  · rw [← hUnionEq]
    rfl
  · intro b
    have hCapbSub : P.capDisk b ⊆ F ∪ P.closedStrip := by
      apply Subset.trans ?_ hCapSub
      rw [P.endDisks_eq_capDisks]
      cases b
      · exact subset_union_left
      · exact subset_union_right
    have heq : (Retained ⊓ Caps b).space = (Rims b).space := by
      rw [R.space_inf_eq_inter_of_le _ _ hRetR (hCaps b).1,
        hRetEq, (hCaps b).2, (hRims b).2,
        ← hinj.image_inter hRetSub hCapbSub, P.retained_inter_capDisk hcut hsmall b]
    exact le_antisymm
      (R.le_of_common_subcomplex_space_subset _ _ (inf_le_left.trans hRetR)
        (hRims b).1 heq.subset)
      (R.le_of_common_subcomplex_space_subset _ _ (hRims b).1
        (inf_le_left.trans hRetR) heq.symm.subset)

end PoincareConjecture.M76.OriginalDiskProduct
