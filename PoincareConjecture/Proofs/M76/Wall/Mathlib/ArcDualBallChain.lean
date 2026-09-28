import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteIndexedBallChain
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FullArcDualContacts
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcNeighborhoodBoundaryContact
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcDualBoundaryAvoidance
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates













set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex







theorem isFinitePLBallPair_arc_dual_chain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K A D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hAK : A ≤ K) (hDK : D ≤ K)
    (hfullA : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    (hfullD : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ D.vertices) → s ∈ D.faces)
    {n : ℕ} (p : Fin (n + 2) → E) (hinj : Function.Injective p)
    (hverts : A.vertices = range p)
    (hedge : ∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ A.faces)
    (hcover : A.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ))
    (hcontact : A.space ∩ D.space = {p 0, p (Fin.last (n + 1))})
    (hballs : ∀ v ∈ A.vertices,
      IsFinitePLBallPair (Fin 3 → ℝ) (K.barycentricDualBlock {v}).space
        (((K.barycentricDualBlock {v}).link v).space ∪
          (D.barycentricDualBlock {v}).space))
    (hdisks : ∀ s ∈ A.faces, s.card = 2 →
      IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock s).space
        ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space) :
    let T := fun i : Fin (n + 2) =>
      ((K.barycentricDualBlock {p i}).link (p i)).space ∪
        (D.barycentricDualBlock {p i}).space
    let J := fun i : Fin (n + 1) => (K.barycentricDualBlock {p i.castSucc, p i.succ}).space
    let Q := fun i : Fin (n + 1) =>
      ((K.barycentricDualBlock {p i.castSucc, p i.succ}).link
        (({p i.castSucc, p i.succ} : Finset E).centroid ℝ id)).space
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (K.barycentricNeighborhood A).space
        ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
      (D.barycentricDualBlock {p 0}).space ⊆ ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
      (D.barycentricDualBlock {p (Fin.last (n + 1))}).space ⊆
        ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
      (K.barycentricNeighborhood A).space ∩ D.space =
        (D.barycentricDualBlock {p 0}).space ∪
          (D.barycentricDualBlock {p (Fin.last (n + 1))}).space := by
  let B := fun i : Fin (n + 2) => (K.barycentricDualBlock {p i}).space
  let T := fun i : Fin (n + 2) =>
    ((K.barycentricDualBlock {p i}).link (p i)).space ∪
      (D.barycentricDualBlock {p i}).space
  let J := fun i : Fin (n + 1) => (K.barycentricDualBlock {p i.castSucc, p i.succ}).space
  let Q := fun i : Fin (n + 1) =>
    ((K.barycentricDualBlock {p i.castSucc, p i.succ}).link
      (({p i.castSucc, p i.succ} : Finset E).centroid ℝ id)).space
  have hp (i : Fin (n + 2)) : p i ∈ A.vertices := by
    rw [hverts]
    exact mem_range_self i
  have hpne : p 0 ≠ p (Fin.last (n + 1)) := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    change 0 = n + 1 at hv
    omega
  obtain ⟨hfeet, hne₀, hne₁, _⟩ := K.arc_neighborhood_boundary_contact
    A D hAK hDK hfullA hpne hcontact
  have hfinite : (A.space ∩ D.space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hcard (i : Fin (n + 1)) : ({p i.castSucc, p i.succ} : Finset E).card = 2 := by
    have hne : p i.castSucc ≠ p i.succ := by
      intro he
      have hv := congrArg Fin.val (hinj he)
      change i.val = i.val + 1 at hv
      omega
    simp [hne]
  obtain ⟨hcontacts, hlinks, hfar, hjoints⟩ :=
    K.full_arc_dual_contacts A hAK hfullA p hinj hp hedge hcover
  let c : (Fin 3 → ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  have hB (i : Fin (n + 2)) : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B i) (T i) :=
    (hballs (p i) (hp i)).model_equiv c
  have hJ (i : Fin (n + 1)) : IsFinitePLBallPair (ℝ × ℝ) (J i) (Q i) :=
    hdisks _ (hedge i) (hcard i)
  have hboundary (i : Fin (n + 1)) : J i ⊆ T i.castSucc ∧ J i ⊆ T i.succ :=
    ⟨(hlinks i).1.trans subset_union_left, (hlinks i).2.trans subset_union_left⟩
  have hfootD (v : E) : (D.barycentricDualBlock {v}).space ⊆ D.space :=
    fun _ hx => D.barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le (D.barycentricDualBlock_le {v}) hx)
  have havoid (i : Fin (n + 1)) :
      Disjoint (D.barycentricDualBlock {p 0}).space (J i) ∧
        Disjoint (D.barycentricDualBlock {p (Fin.last (n + 1))}).space (J i) := by
    have hd := (K.arc_edge_dual_disjoint_boundary A D hAK hDK hfullD hfinite
      (hedge i) (hcard i)).1
    exact ⟨hd.symm.mono (hfootD _) Subset.rfl, hd.symm.mono (hfootD _) Subset.rfl⟩
  have hchain := isFinitePLBallPair_fin_ball_chain B T J Q hB hJ hcontacts hboundary
    hfar hjoints subset_union_right subset_union_right hne₀ hne₁ havoid
  have hwhole : (K.barycentricNeighborhood A).space = ⋃ i, B i := by
    rw [K.barycentricNeighborhood_space_eq_iUnion_dualBlocks, hverts]
    ext x
    constructor
    · intro hx
      obtain ⟨v, ⟨i, rfl⟩, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨i, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨p i, mem_range_self i, hxi⟩
  rw [← hwhole] at hchain
  exact ⟨hchain.1, hchain.2.1, hchain.2.2, hfeet⟩

end Geometry.SimplicialComplex
