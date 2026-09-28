import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MarkedDiskIncidence









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem exists_face_arc_disk_owners
    {E ι γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] {Q : Set E}
    (D q : ι → Set E) (d r : γ → Set E)
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (q i))
    (hrim : ∀ i, D i ∩ Q = q i)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hd : ∀ j, IsFinitePLBallPair ℝ (d j) (r j))
    (hsub : ∀ j, d j ⊆ Q ∩ ⋃ i, D i) :
    ∃ owner : γ → ι,
      (∀ j, d j ⊆ q (owner j)) ∧
      (∀ j i, i ≠ owner j → Disjoint (d j) (D i)) := by
  have hpair : Pairwise fun i j => D i ∩ D j ⊆ (∅ : Set E) := by
    intro i j hij
    exact (disjoint_iff_inter_eq_empty.mp (hdis hij)).subset
  have hown (j : γ) : ∃! i, d j ⊆ D i :=
    exists_unique_disk_owner_away_from_cuts D (fun i => (hD i).isCompact.isClosed)
      rfl hpair (hd j).isConnected ((hsub j).trans inter_subset_right) (disjoint_empty _)
  choose owner howner hunique using hown
  refine ⟨owner, ?_, ?_⟩
  · intro j x hx
    exact (hrim (owner j)).subset ⟨howner j hx, (hsub j hx).1⟩
  · intro j i hi
    exact (hdis (Ne.symm hi)).mono_left (howner j)



theorem exists_unique_face_region_boundary_owner
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite κ] {S Q T F : Set E}
    (B R : κ → Set E)
    (hB : ∀ k, IsFinitePLBallPair V3 (B k) (R k))
    (hR : ∀ k, R k = B k ∩ (Q ∪ T))
    (hcover : (⋃ k, B k) = S)
    (hinter : Pairwise fun k l => B k ∩ B l ⊆ T)
    (hQS : Q ⊆ S) (hF : IsClosed F) (hFQ : F ⊆ Q)
    {x : E} (hx : x ∈ F \ T) :
    ∃! k, closure (connectedComponentIn (F \ T) x) ⊆ R k := by
  let U := connectedComponentIn (F \ T) x
  have hUF : U ⊆ F := (connectedComponentIn_subset _ _).trans sdiff_subset
  have hUT : Disjoint U T := disjoint_left.mpr
    (fun y hy hyT => (connectedComponentIn_subset _ _ hy).2 hyT)
  obtain ⟨k,hk,hunique⟩ := exists_unique_disk_owner_away_from_cuts B
    (fun k => (hB k).isCompact.isClosed) hcover hinter
    (isConnected_connectedComponentIn_iff.mpr hx) (hUF.trans (hFQ.trans hQS)) hUT
  have hcB : closure U ⊆ B k := closure_minimal hk (hB k).isCompact.isClosed
  have hcQ : closure U ⊆ Q := (closure_minimal hUF hF).trans hFQ
  refine ⟨k, fun y hy => (hR k).symm.subset ⟨hcB hy, Or.inl (hcQ hy)⟩, ?_⟩
  intro l hl
  exact hunique l (subset_closure.trans (hl.trans (hB l).1))



theorem exists_disk_cut_face_region_incidence
    {E ι γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] {S Q F : Set E}
    (hS : IsFinitePLBallPair V3 S Q) (D q : ι → Set E)
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (q i))
    (hsub : ∀ i, D i ⊆ S) (hrim : ∀ i, D i ∩ Q = q i)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hF : IsClosed F) (hFQ : F ⊆ Q) (d r : γ → Set E)
    (hd : ∀ j, IsFinitePLBallPair ℝ (d j) (r j))
    (hface : F ∩ (⋃ i, D i) = ⋃ j, d j) :
    ∃ κ : Type, Finite κ ∧ ∃ (B R : κ → Set E) (ends : ι → Bool → κ) (owner : γ → ι),
      Nat.card κ = Nat.card ι + 1 ∧
      (∀ k, IsFinitePLBallPair V3 (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (Q ∪ ⋃ i, D i)) ∧
      (⋃ k, B k) = S ∧
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i, D i) ∧
      (∀ i, ends i false ≠ ends i true) ∧
      (∀ i b, D i ⊆ R (ends i b)) ∧
      (∀ j, d j ⊆ q (owner j)) ∧
      (∀ j i, i ≠ owner j → Disjoint (d j) (D i)) ∧
      (∀ x ∈ F \ ⋃ j, d j, ∃! k,
        closure (connectedComponentIn (F \ ⋃ j, d j) x) ⊆ R k ∧
        ∀ j, d j ⊆ closure (connectedComponentIn (F \ ⋃ j, d j) x) →
          k = ends (owner j) false ∨ k = ends (owner j) true) ∧
      (∀ k x, x ∈ B k \ ⋃ i, D i →
        connectedComponentIn (S \ ⋃ i, D i) x = B k \ ⋃ i, D i) ∧
      (∀ k, closure (B k \ ⋃ i, D i) = B k) := by
  obtain ⟨κ,hκ,B,R,ends,hcard,hB,hR,hcover,hinter,hends,hcontact,hboundary,hcaps,hcomp,hclosure⟩ :=
    exists_marked_disk_cut_ball_partition hS D q hD hsub hrim hdis
  let : Finite κ := hκ
  have hdsub (j : γ) : d j ⊆ Q ∩ ⋃ i, D i := by
    intro x hx
    have hh := hface.symm.subset (mem_iUnion.mpr ⟨j,hx⟩)
    exact ⟨hFQ hh.1,hh.2⟩
  obtain ⟨owner,howner,havoid⟩ := exists_face_arc_disk_owners D q d r hD hrim hdis hd hdsub
  have hdiff : F \ ⋃ j, d j = F \ ⋃ i, D i := by
    rw [← hface]
    ext x
    simp only [mem_sdiff,mem_inter_iff]
    tauto
  refine ⟨κ,hκ,B,R,ends,owner,hcard,hB,hR,hcover,hinter,hends,hcaps,
    howner,havoid,?_,hcomp,hclosure⟩
  intro x hx
  obtain ⟨k,hk,hunique⟩ := exists_unique_face_region_boundary_owner B R hB hR hcover hinter
    hS.1 hF hFQ (hdiff.subset hx)
  rw [← hdiff] at hk hunique
  refine ⟨k,⟨hk,?_⟩,fun l hl => hunique l hl.1⟩
  intro j hj
  obtain ⟨z,hz⟩ := (hd j).isConnected.nonempty
  by_contra hnot
  have hmiss := (hcontact (owner j) k).2
    (fun he => hnot (Or.inl he)) (fun he => hnot (Or.inr he))
  exact disjoint_left.mp hmiss ((hB k).1 (hk (hj hz))) ((hD (owner j)).1 (howner j hz))

end PoincareConjecture.M76.PrismBelt
