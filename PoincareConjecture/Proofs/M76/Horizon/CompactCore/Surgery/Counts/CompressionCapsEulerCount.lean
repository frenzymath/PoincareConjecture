import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapParametrization
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PLSurfaceCount
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.FinitePLImageFaceBounds
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.SquareRimEulerCount

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SimplicialComplex

theorem surfaceEulerCount_eq_add_of_disjoint_subcomplex_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (U A B : SimplicialComplex ℝ E) (hA : A.faces.Finite) (hB : B.faces.Finite)
    (hAU : A ≤ U) (hBU : B ≤ U) (hspace : U.space = A.space ∪ B.space)
    (hdisj : Disjoint A.space B.space) :
    U.surfaceEulerCount = A.surfaceEulerCount + B.surfaceEulerCount := by
  let C : Bool → SimplicialComplex ℝ E := fun b => if b then B else A
  have hCU : ∀ b, C b ≤ U := by intro b; cases b <;> assumption
  have hcover : U.space = ⋃ b ∈ (Finset.univ : Finset Bool), (C b).space := by
    rw [hspace]
    ext x
    simp [C, Bool.exists_bool, or_comm]
  have hfaces : U.faces = A.faces ∪ B.faces := by
    rw [U.faces_eq_biUnion_of_subcomplex_cover C hCU Finset.univ hcover]
    ext s
    simp [C, Bool.exists_bool, or_comm]
  have hempty : (A ⊓ B).space = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact disjoint_left.mp hdisj (A.convexHull_subset_space hs.1 hxs)
      (B.convexHull_subset_space hs.2 hxs)
  have h := A.surfaceEulerCount_union_add_inter B U hA hB hfaces
  rw [(A ⊓ B).surfaceEulerCount_eq_zero_of_space_empty hempty, add_zero] at h
  exact h

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {L N : Set X} {j : V2 → X}

private theorem capDisk_subset_closedStrip (P : OriginalDiskProduct e L j) (b : Bool) :
    P.capDisk b ⊆ P.closedStrip := by
  intro y hy
  apply P.endDisks_subset_closedStrip
  rw [P.endDisks_eq_capDisks]
  cases b with
  | false => exact Or.inl hy
  | true => exact Or.inr hy

theorem cap_image_surfaceEulerCount
    (P : OriginalDiskProduct e L j) (phi : X → E)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphi : InjOn phi N) (hstrip : P.closedStrip ⊆ N) (b : Bool)
    (Cap : SimplicialComplex ℝ E) (hCap : Cap.faces.Finite)
    (hspace : Cap.space = phi '' P.capDisk b) :
    Cap.surfaceEulerCount = 1 := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Disk, hDisk, hDisks, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  have hPL : PolyhedralPLInCharts e (P.capParameter b) Disk.space :=
    hDisks.symm ▸ P.polyhedral_capParameter b
  have hf := hPL.finitePiecewiseAffineOn_comp Disk hDisk hphiPL
  have hcap (z : V2) (hz : z ∈ Disk.space) : P.capParameter b z ∈ P.capDisk b := by
    rw [← P.capParameter_image_disk b]
    exact mem_image_of_mem _ (hDisks.subset hz)
  have hinj : InjOn (phi ∘ P.capParameter b) Disk.space := by
    intro x hx y hy heq
    have hxy := hphi (hstrip (capDisk_subset_closedStrip P b (hcap x hx)))
      (hstrip (capDisk_subset_closedStrip P b (hcap y hy))) heq
    exact congrArg Subtype.val ((P.embedding_capParameter b).injective
      (show (fun z : D => P.capParameter b z) ⟨x, hDisks.subset hx⟩ =
        (fun z : D => P.capParameter b z) ⟨y, hDisks.subset hy⟩ from hxy))
  have himage : (phi ∘ P.capParameter b) '' Disk.space = Cap.space := by
    rw [hspace, hDisks, ← P.capParameter_image_disk b, image_image]
    rfl
  have hdimD : ∀ s ∈ Disk.faces, s.card ≤ 3 := by
    intro s hs
    have h := (Disk.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa using h
  have hcount : Disk.surfaceEulerCount = 1 := by
    have hc : Convex ℝ Disk.space := hDisks.symm ▸ convex_closedBall (0 : V2) 1
    have hne : Disk.space.Nonempty := hDisks.symm ▸ ⟨0, mem_closedBall_self zero_le_one⟩
    letI : ContractibleSpace Disk.space := hc.contractibleSpace hne
    exact Disk.surfaceEulerCount_eq_one_of_planar_contractible (by simp) hDisk
  have hdim := hf.face_card_le_of_image hDisk hdimD Cap himage.symm.subset
  exact (hf.surfaceEulerCount_eq_of_injOn hDisk hCap hdimD hdim hinj himage).symm.trans hcount

theorem cap_rim_image_surfaceEulerCount
    (P : OriginalDiskProduct e L j) (phi : X → E)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphi : InjOn phi N) (hstrip : P.closedStrip ⊆ N) (b : Bool)
    (Rim : SimplicialComplex ℝ E) (hRim : Rim.faces.Finite)
    (hspace : Rim.space = phi '' P.capRimSet b) :
    Rim.surfaceEulerCount = 0 := by
  obtain ⟨Square, hSquare, hSquares⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  have hPL := (P.polyhedral_capParameter b).restrict_finite Square hSquare
    (hSquares.subset.trans sphere_subset_closedBall)
  have hf := hPL.finitePiecewiseAffineOn_comp Square hSquare hphiPL
  have hmem (z : V2) (hz : z ∈ Square.space) : z ∈ D :=
    sphere_subset_closedBall (hSquares.subset hz)
  have hcap (z : V2) (hz : z ∈ Square.space) : P.capParameter b z ∈ P.capDisk b := by
    rw [← P.capParameter_image_disk b]
    exact mem_image_of_mem _ (hmem z hz)
  have hinj : InjOn (phi ∘ P.capParameter b) Square.space := by
    intro x hx y hy heq
    have hxy := hphi (hstrip (capDisk_subset_closedStrip P b (hcap x hx)))
      (hstrip (capDisk_subset_closedStrip P b (hcap y hy))) heq
    exact congrArg Subtype.val ((P.embedding_capParameter b).injective
      (show (fun z : D => P.capParameter b z) ⟨x, hmem x hx⟩ =
        (fun z : D => P.capParameter b z) ⟨y, hmem y hy⟩ from hxy))
  have himage : (phi ∘ P.capParameter b) '' Square.space = Rim.space := by
    rw [hspace, hSquares, ← P.capParameter_image_rim b, image_image]
    rfl
  have hdimS : ∀ s ∈ Square.faces, s.card ≤ 3 := by
    intro s hs
    have h := (Square.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa using h
  have hdim := hf.face_card_le_of_image hSquare hdimS Rim himage.symm.subset
  exact (hf.surfaceEulerCount_eq_of_injOn hSquare hRim hdimS hdim hinj himage).symm.trans
    (CompressionCylinder.square_rim_surfaceEulerCount Square hSquare hSquares)

theorem caps_image_surfaceEulerCount
    (P : OriginalDiskProduct e L j) (phi : X → E)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphi : InjOn phi N) (hstrip : P.closedStrip ⊆ N)
    (Caps : Bool → SimplicialComplex ℝ E) (Union : SimplicialComplex ℝ E)
    (hCaps : ∀ b, (Caps b).faces.Finite)
    (hspace : ∀ b, (Caps b).space = phi '' P.capDisk b)
    (hsub : ∀ b, Caps b ≤ Union)
    (hUnion : Union.space = (Caps false).space ∪ (Caps true).space) :
    Union.surfaceEulerCount = 2 := by
  have hdisj : Disjoint (Caps false).space (Caps true).space := by
    rw [hspace false, hspace true]
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy := hphi (hstrip (capDisk_subset_closedStrip P false hx))
      (hstrip (capDisk_subset_closedStrip P true hy)) heq.symm
    exact disjoint_left.mp (P.disjoint_capDisks false) hx (hxy.symm ▸ hy)
  rw [Union.surfaceEulerCount_eq_add_of_disjoint_subcomplex_cover
    (Caps false) (Caps true) (hCaps false) (hCaps true) (hsub false) (hsub true) hUnion hdisj,
    P.cap_image_surfaceEulerCount phi hphiPL hphi hstrip false
      (Caps false) (hCaps false) (hspace false),
    P.cap_image_surfaceEulerCount phi hphiPL hphi hstrip true
      (Caps true) (hCaps true) (hspace true)]
  norm_num

theorem cap_rims_image_surfaceEulerCount
    (P : OriginalDiskProduct e L j) (phi : X → E)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphi : InjOn phi N) (hstrip : P.closedStrip ⊆ N)
    (Rims : Bool → SimplicialComplex ℝ E) (Union : SimplicialComplex ℝ E)
    (hRims : ∀ b, (Rims b).faces.Finite)
    (hspace : ∀ b, (Rims b).space = phi '' P.capRimSet b)
    (hsub : ∀ b, Rims b ≤ Union)
    (hUnion : Union.space = (Rims false).space ∪ (Rims true).space) :
    Union.surfaceEulerCount = 0 := by
  have hdisj : Disjoint (Rims false).space (Rims true).space := by
    rw [hspace false, hspace true]
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxc := P.capRimSet_subset_capDisk false hx
    have hyc := P.capRimSet_subset_capDisk true hy
    have hxy := hphi (hstrip (capDisk_subset_closedStrip P false hxc))
      (hstrip (capDisk_subset_closedStrip P true hyc)) heq.symm
    exact disjoint_left.mp (P.disjoint_capDisks false) hxc (hxy.symm ▸ hyc)
  rw [Union.surfaceEulerCount_eq_add_of_disjoint_subcomplex_cover
    (Rims false) (Rims true) (hRims false) (hRims true) (hsub false) (hsub true) hUnion hdisj,
    P.cap_rim_image_surfaceEulerCount phi hphiPL hphi hstrip false
      (Rims false) (hRims false) (hspace false),
    P.cap_rim_image_surfaceEulerCount phi hphiPL hphi hstrip true
      (Rims true) (hRims true) (hspace true), add_zero]

end PoincareConjecture.M76.OriginalDiskProduct
