import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.BallPolygonContactDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.BallPartitionRefinement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperDiskSelectedHole

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_remaining_piece_contact_disk
    {E κ γ δ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite κ] [Finite γ] [Finite δ]
    {S Q T : Set E} (B R : κ → Set E)
    (hB : ∀ b, IsFinitePLBallPair V3 (B b) (R b))
    (hR : ∀ b, R b = B b ∩ (Q ∪ T)) (hcover : (⋃ b, B b) = S)
    (hinter : Pairwise fun b c => B b ∩ B c ⊆ T)
    (C : γ → SimplicialComplex ℝ E) (hC : ∀ c, (C c).faces.Finite)
    (hconn : ∀ c, IsConnected (C c).space) (hCS : ∀ c, (C c).space ⊆ S)
    (hdis : Pairwise fun c d => Disjoint (C c).space (C d).space)
    (hcut : ∀ c, Disjoint (C c).space T)
    (n : δ → ℕ) (P : ∀ j, Polygon E (n j + 3))
    (hP : ∀ j, (P j).HasSimplicialEdges) (hi : ∀ j, Function.Injective (P j))
    (hPdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    (hwhole : (⋃ j, (P j).boundary ℝ) = Q ∩ ⋃ c, (C c).space)
    (hne : (Q ∩ ⋃ c, (C c).space).Nonempty) :
    ∃ j d, IsFinitePLBallPair (ℝ × ℝ) d ((P j).boundary ℝ) ∧
      d ⊆ S ∧ d ∩ Q = (P j).boundary ℝ ∧
      d ∩ (T ∪ ⋃ c, (C c).space) = (P j).boundary ℝ := by
  classical
  choose owner howner howner_unique using fun c =>
    exists_unique_disk_owner_away_from_cuts B (fun b => (hB b).isCompact.isClosed)
      hcover hinter (hconn c) (hCS c) (hcut c)
  have hout (c : γ) (b : κ) (hne : owner c ≠ b) : Disjoint (C c).space (B b) := by
    apply disjoint_left.mpr
    intro x hxc hxb
    exact disjoint_left.mp (hcut c) hxc (hinter hne ⟨howner c hxc,hxb⟩)
  have hPconn (j : δ) : IsConnected ((P j).boundary ℝ) := by
    obtain ⟨H⟩ := (P j).nonempty_boundary_homeomorph_circle (hP j) (hi j)
    exact isConnected_iff_connectedSpace.mpr (H.connectedSpace_iff.mpr inferInstance)
  have hPwhole (j : δ) : (P j).boundary ℝ ⊆ Q ∩ ⋃ c, (C c).space :=
    (subset_iUnion _ j).trans hwhole.subset
  choose piece hpiece hpiece_unique using fun j =>
    (hPconn j).exists_unique_subset_finite_disjoint_closed (fun c => (C c).space)
      (fun c => ((C c).isCompact_space_of_finite (hC c)).isClosed) hdis
      ((hPwhole j).trans inter_subset_right)
  obtain ⟨x,hxQ,hxC⟩ := hne
  obtain ⟨c,hxc⟩ := mem_iUnion.mp hxC
  let b := owner c
  let I := {d : γ // owner d = b}
  let J := {j : δ // owner (piece j) = b}
  obtain ⟨M,hM,hMs,_⟩ := SimplicialComplex.exists_finite_triangulation_iUnion
    (fun d : I => C d) (fun d => hC d)
  have hMB : M.space ⊆ B b := by
    rw [hMs]
    rintro y hy
    obtain ⟨d,hd⟩ := mem_iUnion.mp hy
    exact d.property ▸ howner d hd
  have hMcut : Disjoint M.space T := by
    rw [hMs]
    exact disjoint_iUnion_left.mpr (fun d => hcut d)
  have hMJ : R b ∩ M.space = ⋃ j : J, (P j).boundary ℝ := by
    apply Subset.antisymm
    · rintro y ⟨hyR,hyM⟩
      have hyQ : y ∈ Q := by
        rcases ((hR b).subset hyR).2 with h | h
        · exact h
        · exact (disjoint_left.mp hMcut hyM h).elim
      obtain ⟨d,hyd⟩ := mem_iUnion.mp (hMs.subset hyM)
      obtain ⟨j,hyj⟩ := mem_iUnion.mp (hwhole.symm.subset
        ⟨hyQ,mem_iUnion.mpr ⟨d,hyd⟩⟩)
      have hpd : piece j = d := by
        by_contra hne
        exact disjoint_left.mp (hdis hne) (hpiece j hyj) hyd
      exact mem_iUnion.mpr ⟨⟨j,hpd ▸ d.property⟩,hyj⟩
    · intro y hy
      obtain ⟨j,hyj⟩ := mem_iUnion.mp hy
      have hyC := hpiece j hyj
      have hyM : y ∈ M.space := hMs.symm.subset
        (mem_iUnion.mpr ⟨⟨piece j,j.property⟩,hyC⟩)
      exact ⟨(hR b).symm.subset ⟨hMB hyM,Or.inl ((hPwhole j hyj).1)⟩,hyM⟩
  have hxM : x ∈ M.space := hMs.symm.subset (mem_iUnion.mpr ⟨⟨c,rfl⟩,hxc⟩)
  have hxR : x ∈ R b := (hR b).symm.subset ⟨howner c hxc,Or.inl hxQ⟩
  have hJne : Nonempty J := by
    obtain ⟨j,_⟩ := mem_iUnion.mp (hMJ.subset ⟨hxR,hxM⟩)
    exact ⟨j⟩
  let : Nonempty J := hJne
  obtain ⟨j,d,hd,hdB,hdR,hdM⟩ := exists_ball_polygon_contact_disk (hB b) M hM hMB
    (fun j : J => n j) (fun j : J => P j) (fun j => hP j) (fun j => hi j)
    (fun j => (subset_iUnion _ j).trans (hMJ.symm.subset.trans inter_subset_left))
    (fun i j hij => hPdis (fun heq => hij (Subtype.ext heq))) hMJ
  have hrQ : (P j).boundary ℝ ⊆ Q := (hPwhole j).trans inter_subset_left
  have hdQ : d ∩ Q = (P j).boundary ℝ := by
    apply Subset.antisymm
    · rintro y ⟨hyd,hyQ⟩
      exact hdR.subset ⟨hyd,(hR b).symm.subset ⟨hdB hyd,Or.inl hyQ⟩⟩
    · intro y hy
      exact ⟨hd.1 hy,hrQ hy⟩
  refine ⟨j,d,hd,hdB.trans ((subset_iUnion _ b).trans hcover.subset),hdQ,?_⟩
  apply Subset.antisymm
  · rintro y ⟨hyd,hyT | hyC⟩
    · exact hdR.subset ⟨hyd,(hR b).symm.subset ⟨hdB hyd,Or.inr hyT⟩⟩
    · obtain ⟨a,hya⟩ := mem_iUnion.mp hyC
      have ha : owner a = b := by
        by_contra hn
        exact disjoint_left.mp (hout a b hn) hya (hdB hyd)
      exact hdM.subset ⟨hyd,hMs.symm.subset (mem_iUnion.mpr ⟨⟨a,ha⟩,hya⟩)⟩
  · intro y hy
    exact ⟨hd.1 hy,Or.inr ((hPwhole j hy).2)⟩

end PoincareConjecture.M76
