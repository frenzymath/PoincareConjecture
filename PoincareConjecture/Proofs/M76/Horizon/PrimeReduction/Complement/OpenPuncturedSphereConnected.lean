import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SphereBallEnlargement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalPuncturedSphereDiskCut
import PoincareConjecture.Proofs.Horizon.Topology.Connected.IntervalNeighborhoods











set_option autoImplicit false
open Set Metric Geometry

namespace Geometry.CubicalThreeSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)



theorem exists_connected_punctured_sphere_around_compact
    {κ : Type*} [Finite κ] (A r : κ → Set V4)
    (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ sphere)
    (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (A i \ r i)))
    {K : Set V4} (hK : IsCompact K) (hKsub : K ⊆ sphere \ ⋃ i, A i) :
    ∃ B t : κ → Set V4,
      (∀ i, IsFinitePLBallPair V3 (B i) (t i) ∧ B i ⊆ sphere ∧
        A i ⊆ B i \ t i ∧ Disjoint (B i) K ∧
        IsOpen ((Subtype.val : sphere → V4) ⁻¹' (B i \ t i))) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      IsConnected (sphere \ ⋃ i, B i \ t i) ∧
      K ⊆ sphere \ ⋃ i, B i \ t i ∧
      (sphere \ ⋃ i, B i \ t i) ⊆ sphere \ ⋃ i, A i := by
  classical
  have hAK (i : κ) : A i ⊆ Kᶜ := by
    intro x hx hKx
    exact (hKsub hKx).2 (mem_iUnion.mpr ⟨i, hx⟩)
  obtain ⟨U, hU, hUdis⟩ :=
    Poincare.Topology.exists_pairwise_disjoint_open_supersets_of_isCompact
      A (fun _ => Kᶜ) (fun i => (hA i).isCompact) hdis
      (fun _ => hK.isClosed.isOpen_compl) hAK
  have hSc : IsCompact sphere := (isCompact_closedBall (0 : V4) 1).of_isClosed_subset
    isClosed_frontier isClosed_closedBall.frontier_subset
  have henlarge (i : κ) : ∃ B t : Set V4,
      IsFinitePLBallPair V3 B t ∧ B ⊆ sphere ∧ A i ⊆ B \ t ∧ B ⊆ U i ∧
      IsOpen ((Subtype.val : sphere → V4) ⁻¹' (B \ t)) := by
    obtain ⟨B, t, hB, hBS, hAB, havoid, hBo, _⟩ :=
      (hA i).exists_sphere_ball_enlargement (hAS i) (hopen i)
        (hSc.diff (hU i).1) sdiff_subset
        (disjoint_left.mpr (fun _ hx hy => hy.2 ((hU i).2.1 hx)))
    have hBU : B ⊆ U i := by
      intro x hx
      by_contra hxu
      exact disjoint_left.mp havoid hx ⟨hBS hx, hxu⟩
    exact ⟨B, t, hB, hBS, hAB, hBU, hBo⟩
  choose B t hB hBS hAB hBU hBo using henlarge
  have hBdis : Pairwise (fun i j => Disjoint (B i) (B j)) :=
    fun i j hij => (hUdis hij).mono (hBU i) (hBU j)
  have hBK (i : κ) : Disjoint (B i) K :=
    disjoint_left.mpr (fun _ hx hxK => (hU i).2.2 (hBU i hx) hxK)
  refine ⟨B, t, fun i => ⟨hB i, hBS i, hAB i, hBK i, hBo i⟩, hBdis,
    isConnected_punctured_sphere_of_isOpen B t hB hBS hBdis hBo, ?_, ?_⟩
  · intro x hx
    refine ⟨(hKsub hx).1, ?_⟩
    intro hxb
    obtain ⟨i, hxi, _⟩ := mem_iUnion.mp hxb
    exact disjoint_left.mp (hBK i) hxi hx
  · rintro x ⟨hxS, hxb⟩
    refine ⟨hxS, ?_⟩
    intro hxa
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxa
    exact hxb (mem_iUnion.mpr ⟨i, hAB i hxi⟩)



theorem isPreconnected_open_punctured_sphere
    {κ : Type*} [Finite κ] (A r : κ → Set V4)
    (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ sphere)
    (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (A i \ r i))) :
    IsPreconnected (sphere \ ⋃ i, A i) := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨B, t, _, _, hconn, hpoints, hsub⟩ :=
    exists_connected_punctured_sphere_around_compact A r hA hAS hdis hopen
      (isCompact_singleton.insert x) (show ({x, y} : Set V4) ⊆ sphere \ ⋃ i, A i by
        intro z hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy)
  exact ⟨sphere \ ⋃ i, B i \ t i, hsub, hpoints (by simp), hpoints (by simp),
    hconn.isPreconnected⟩



theorem isConnected_open_punctured_sphere
    {κ : Type*} [Finite κ] (A r : κ → Set V4)
    (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ sphere)
    (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (A i \ r i)))
    (hne : (sphere \ ⋃ i, A i).Nonempty) :
    IsConnected (sphere \ ⋃ i, A i) :=
  ⟨hne, isPreconnected_open_punctured_sphere A r hA hAS hdis hopen⟩

end Geometry.CubicalThreeSphere
