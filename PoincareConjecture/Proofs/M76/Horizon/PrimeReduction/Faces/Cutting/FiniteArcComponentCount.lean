import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Cutting.FiniteArcDiskDecomposition
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBoundaryCollarTopology
import Mathlib.Topology.Connected.Clopen









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem disk_partition_components
    {E V κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ E] [Finite κ] {S Q T : Set E} (B R : κ → Set E)
    (hB : ∀ k, IsFinitePLBallPair V (B k) (R k))
    (hR : ∀ k, R k = B k ∩ (Q ∪ T))
    (hcover : (⋃ k, B k) = S)
    (hinter : Pairwise fun k l => B k ∩ B l ⊆ T) :
    Nonempty (κ ≃ ConnectedComponents (S \ T : Set E)) ∧
      (∀ k x, x ∈ B k \ T → connectedComponentIn (S \ T) x = B k \ T) ∧
      (∀ k, closure (B k \ T) = B k) := by
  classical
  have hconn (k : κ) : IsConnected (B k \ T) := by
    have h := (hB k).isConnected_sdiff_of_subset_boundary
      (show B k ∩ T ⊆ R k from fun x hx => (hR k).symm.subset ⟨hx.1, Or.inr hx.2⟩)
    have he : B k \ (B k ∩ T) = B k \ T := by ext x; simp only [mem_sdiff, mem_inter_iff]; tauto
    rwa [he] at h
  have hclosure (k : κ) : closure (B k \ T) = B k := by
    have h := (hB k).closure_sdiff_of_subset_boundary
      (show B k ∩ T ⊆ R k from fun x hx => (hR k).symm.subset ⟨hx.1, Or.inr hx.2⟩)
    have he : B k \ (B k ∩ T) = B k \ T := by ext x; simp only [mem_sdiff, mem_inter_iff]; tauto
    rwa [he] at h
  have hsub (k : κ) : B k \ T ⊆ S \ T :=
    fun x hx => ⟨hcover.subset (mem_iUnion.mpr ⟨k, hx.1⟩), hx.2⟩
  have hcomp (k : κ) (x : E) (hx : x ∈ B k \ T) :
      connectedComponentIn (S \ T) x = B k \ T := by
    have hxcomp := mem_connectedComponentIn (hsub k hx)
    obtain ⟨l, hl, _⟩ := exists_unique_disk_owner_away_from_cuts B
      (fun l => (hB l).isCompact.isClosed) hcover hinter
      (isConnected_connectedComponentIn_iff.mpr (hsub k hx))
      ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (disjoint_left.mpr (fun y hy hyT => (connectedComponentIn_subset _ _ hy).2 hyT))
    have hlk : l = k := by
      by_contra hn
      exact hx.2 (hinter hn ⟨hl hxcomp, hx.1⟩)
    subst l
    apply Subset.antisymm
    · exact fun y hy => ⟨hl hy, (connectedComponentIn_subset _ _ hy).2⟩
    · exact (hconn k).isPreconnected.subset_connectedComponentIn hx (hsub k)
  choose x hx using fun k => (hconn k).nonempty
  let point (k : κ) : (S \ T : Set E) := ⟨x k, hsub k (hx k)⟩
  let f : κ → ConnectedComponents (S \ T : Set E) := fun k => ConnectedComponents.mk (point k)
  have hcoe (x y : (S \ T : Set E)) : ConnectedComponents.mk x = ConnectedComponents.mk y ↔
      (x : E) ∈ connectedComponentIn (S \ T) y := by
    rw [ConnectedComponents.coe_eq_coe', connectedComponentIn_eq_image y.property]
    constructor
    · exact fun h => mem_image_of_mem Subtype.val h
    · rintro ⟨z, hz, he⟩
      have hzx : z = x := Subtype.ext he
      rwa [hzx] at hz
  have hfinj : Function.Injective f := by
    intro k l he
    have hm := (hcoe (point k) (point l)).mp he
    have hm' : x k ∈ B l \ T := (hcomp l (x l) (hx l)).subset hm
    by_contra hn
    exact (hx k).2 (hinter hn ⟨(hx k).1, hm'.1⟩)
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe z
    obtain ⟨k, hyk⟩ := mem_iUnion.mp (hcover.symm.subset y.property.1)
    refine ⟨k, (hcoe (point k) y).mpr ?_⟩
    exact (hcomp k y ⟨hyk, y.property.2⟩).symm.subset (hx k)
  exact ⟨⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩⟩, hcomp, hclosure⟩




theorem finite_proper_arc_component_count
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] {S Q : Set E}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (D : ι → Set E) (p q : ι → E)
    (hD : ∀ i, IsFinitePLBallPair ℝ (D i) {p i, q i})
    (hpq : ∀ i, p i ≠ q i) (hsub : ∀ i, D i ⊆ S)
    (hrim : ∀ i, ({p i, q i} : Set E) = D i ∩ Q)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    Finite (ConnectedComponents (S \ ⋃ i, D i : Set E)) ∧
      Nat.card (ConnectedComponents (S \ ⋃ i, D i : Set E)) = Nat.card ι + 1 ∧
      ∀ x ∈ S \ ⋃ i, D i,
        IsFinitePLBallPair (ℝ × ℝ) (closure (connectedComponentIn (S \ ⋃ i, D i) x))
          (closure (connectedComponentIn (S \ ⋃ i, D i) x) ∩ (Q ∪ ⋃ i, D i)) := by
  obtain ⟨κ, hκ, B, R, hcard, hB, hR, hcover, hinter⟩ :=
    exists_finite_proper_arc_disk_decomposition hS D p q hD hpq hsub hrim hdis
  let : Finite κ := hκ
  obtain ⟨⟨e⟩, hcomp, hclosure⟩ := disk_partition_components B R hB hR hcover hinter
  refine ⟨Finite.of_equiv κ e, (Nat.card_congr e).symm.trans hcard, ?_⟩
  intro x hx
  obtain ⟨k, hxk⟩ := mem_iUnion.mp (hcover.symm.subset hx.1)
  rw [hcomp k x ⟨hxk, hx.2⟩, hclosure k, ← hR k]
  exact hB k

end PoincareConjecture.M76
