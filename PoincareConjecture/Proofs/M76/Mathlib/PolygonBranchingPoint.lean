import PoincareConjecture.Proofs.M76.Mathlib.SegmentGermDirections

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]

theorem exists_local_segments_of_family_ne_common
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {S r : Set E} {q p : E} (hr : r ⊆ {q})
    (hcover : S = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (hp : p ∈ S) (hpq : p ≠ q) :
    ∃ a b : E, a ≠ p ∧ b ≠ p ∧
      segment ℝ p a ∩ segment ℝ p b = {p} ∧
      segment ℝ p a ∪ segment ℝ p b ⊆ S ∧
      ∀ᶠ x in 𝓝 p, x ∈ S ↔ x ∈ segment ℝ p a ∪ segment ℝ p b := by
  classical
  have hpr : p ∉ r := fun h => hpq (hr h)
  obtain ⟨i, hpi⟩ := mem_iUnion.mp ((hcover.subset hp).resolve_left hpr)
  have hother (j : ι) : ∀ᶠ x in 𝓝 p,
      x ∈ (P j).boundary ℝ → x ∈ (P i).boundary ℝ := by
    by_cases hji : j = i
    · subst j
      exact Eventually.of_forall fun _ hx => hx
    · have hpj : p ∉ (P j).boundary ℝ := fun hpj => hpq (hpair hji ⟨hpj, hpi⟩)
      filter_upwards [(P j).isClosed_boundary.isOpen_compl.mem_nhds hpj] with x hx
      exact fun hxj => (hx hxj).elim
  have hrclosed : IsClosed r := ((finite_singleton q).subset hr).isClosed
  have hPiS : (P i).boundary ℝ ⊆ S :=
    fun x hx => hcover.symm.subset (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
  have hlocal : ∀ᶠ x in 𝓝 p, x ∈ S ↔ x ∈ (P i).boundary ℝ := by
    filter_upwards [Filter.eventually_all.mpr hother,
      hrclosed.isOpen_compl.mem_nhds hpr] with x hx hxr
    constructor
    · intro hxS
      obtain ⟨j, hxj⟩ := mem_iUnion.mp ((hcover.subset hxS).resolve_left hxr)
      exact hx j hxj
    · exact fun hx => hPiS hx
  obtain ⟨a, b, ha, hb, hab, hsegments, hnear⟩ :=
    (P i).exists_local_segment_pair (hP i).2 (hP i).1 hpi
  refine ⟨a, b, ha, hb, hab, hsegments.trans hPiS, ?_⟩
  filter_upwards [hlocal, hnear] with x hx hy
  exact hx.trans hy

theorem common_point_eq_of_pair_subset_family
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {S r : Set E} {q p : E} (hr : r ⊆ {q})
    (hcover : S = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    {k l : ℕ} (Q : Polygon E (k + 3)) (R : Polygon E (l + 3))
    (hQ : Function.Injective Q ∧ Q.HasSimplicialEdges)
    (hR : Function.Injective R ∧ R.HasSimplicialEdges)
    (hQS : Q.boundary ℝ ⊆ S) (hRS : R.boundary ℝ ⊆ S)
    (hpQ : p ∈ Q.boundary ℝ) (hpR : p ∈ R.boundary ℝ)
    (hQR : Q.boundary ℝ ∩ R.boundary ℝ ⊆ {p}) : p = q := by
  by_contra hpq
  obtain ⟨a, b, _, _, _, _, hlocal⟩ :=
    exists_local_segments_of_family_ne_common n P hP hr hcover hpair (hQS hpQ) hpq
  obtain ⟨u, v, hu, hv, huv, huvQ, _⟩ := Q.exists_local_segment_pair hQ.2 hQ.1 hpQ
  obtain ⟨w, _, hw, _, _, hwR, _⟩ := R.exists_local_segment_pair hR.2 hR.1 hpR
  have huw : segment ℝ p u ∩ segment ℝ p w ⊆ {p} :=
    fun x hx => hQR ⟨huvQ (Or.inl hx.1), hwR (Or.inl hx.2)⟩
  have hvw : segment ℝ p v ∩ segment ℝ p w ⊆ {p} :=
    fun x hx => hQR ⟨huvQ (Or.inr hx.1), hwR (Or.inl hx.2)⟩
  exact NormedSpace.not_three_segments_in_two_segment_germ hu hv hw huv.subset huw hvw
    ((subset_union_left.trans huvQ).trans hQS)
    ((subset_union_right.trans huvQ).trans hQS)
    ((subset_union_left.trans hwR).trans hRS)
    (hlocal.mono (fun _ hx => hx.mp))

theorem common_point_eq_of_branching_family_subset
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {S r : Set E} {q p : E} (hr : r ⊆ {q})
    (hcover : S = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    {κ : Type*} (m : κ → ℕ) (Q : ∀ i, Polygon E (m i + 3))
    (hQ : ∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges)
    (hQS : ∀ i, (Q i).boundary ℝ ⊆ S)
    (hQpair : Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ {p}))
    (hbranch : ¬ Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ))) :
    p = q := by
  classical
  have hmeet := hbranch
  change ¬ ∀ i j, i ≠ j → Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ) at hmeet
  push Not at hmeet
  obtain ⟨i, j, hij, hmeet⟩ := hmeet
  obtain ⟨x, hxi, hxj⟩ := not_disjoint_iff.mp hmeet
  have hxp : x = p := hQpair hij ⟨hxi, hxj⟩
  exact common_point_eq_of_pair_subset_family n P hP hr hcover hpair
    (Q i) (Q j) (hQ i) (hQ j) (hQS i) (hQS j) (hxp ▸ hxi) (hxp ▸ hxj) (hQpair hij)

end Polygon
