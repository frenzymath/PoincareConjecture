import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.FiniteDiskIncidence

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem exists_marked_disk_cut_ball_partition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] {S Q : Set E}
    (hS : IsFinitePLBallPair V3 S Q) (D q : ι → Set E)
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (q i))
    (hsub : ∀ i, D i ⊆ S) (hrim : ∀ i, D i ∩ Q = q i)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    ∃ κ : Type, Finite κ ∧ ∃ (B R : κ → Set E) (ends : ι → Bool → κ),
      Nat.card κ = Nat.card ι + 1 ∧
      (∀ k, IsFinitePLBallPair V3 (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (Q ∪ ⋃ i, D i)) ∧
      (⋃ k, B k) = S ∧
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i, D i) ∧
      (∀ i, ends i false ≠ ends i true) ∧
      (∀ i k, ((k = ends i false ∨ k = ends i true) → B k ∩ D i = D i) ∧
        (k ≠ ends i false → k ≠ ends i true → Disjoint (B k) (D i))) ∧
      (∀ k, R k = (B k ∩ Q) ∪ ⋃ i : {i // k = ends i false ∨ k = ends i true}, D i) ∧
      (∀ i b, D i ⊆ R (ends i b)) ∧
      (∀ k x, x ∈ B k \ ⋃ i, D i →
        connectedComponentIn (S \ ⋃ i, D i) x = B k \ ⋃ i, D i) ∧
      (∀ k, closure (B k \ ⋃ i, D i) = B k) := by
  classical
  obtain ⟨κ,hκ,B,R,hcard,hB,hR,hcover,hinter,howners,hcomp,hclosure⟩ :=
    exists_finite_disk_partition_with_whole_incidence hS D q hD hsub hrim hdis
  let : Finite κ := hκ
  choose a b hab ha hb hother using howners
  let ends : ι → Bool → κ := fun i c => if c then b i else a i
  have hcontact (i : ι) (k : κ) :
      B k ∩ D i = if k = ends i false ∨ k = ends i true then D i else ∅ := by
    change B k ∩ D i = if k = a i ∨ k = b i then D i else ∅
    split_ifs with hk
    · apply inter_eq_right.mpr
      rcases hk with rfl | rfl
      · exact ha i
      · exact hb i
    · exact disjoint_iff_inter_eq_empty.mp
        ((hother i k (fun he => hk (Or.inl he)) (fun he => hk (Or.inr he))).symm)
  refine ⟨κ,hκ,B,R,ends,hcard,hB,hR,hcover,hinter,hab,?_,?_,?_,hcomp,hclosure⟩
  · intro i k
    exact ⟨fun hk => by simpa only [if_pos hk] using hcontact i k,
      fun hka hkb => (hother i k hka hkb).symm⟩
  · intro k
    rw [hR k]
    ext x
    constructor
    · rintro ⟨hxB,hxQ | hxD⟩
      · exact Or.inl ⟨hxB,hxQ⟩
      · obtain ⟨i,hxi⟩ := mem_iUnion.mp hxD
        have hk : k = ends i false ∨ k = ends i true := by
          by_contra hk
          have hx := (hcontact i k).subset ⟨hxB,hxi⟩
          simpa only [if_neg hk,mem_empty_iff_false] using hx
        exact Or.inr (mem_iUnion.mpr ⟨⟨i,hk⟩,hxi⟩)
    · rintro (⟨hxB,hxQ⟩ | hxD)
      · exact ⟨hxB,Or.inl hxQ⟩
      · obtain ⟨i,hxi⟩ := mem_iUnion.mp hxD
        have hx : x ∈ B k ∩ D i := (hcontact i k).symm.subset
          (by simpa only [if_pos i.property] using hxi)
        exact ⟨hx.1,Or.inr (mem_iUnion.mpr ⟨i,hxi⟩)⟩
  · intro i c x hx
    apply (hR (ends i c)).symm.subset
    refine ⟨?_,Or.inr (mem_iUnion.mpr ⟨i,hx⟩)⟩
    cases c
    · exact ha i hx
    · exact hb i hx

end PoincareConjecture.M76.PrismBelt
