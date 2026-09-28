import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.Innermost
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ComponentExclusion



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : V → ℝ) ⁻¹' ({0} : Set ℝ))

theorem exists_returning_disk_avoiding_complete_upper_family
    {ι : Type*} [Finite ι] (W : ι → Set V) (a b : ι → V) {D C : Set V}
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i, b i})
    (hne : ∀ i, a i ≠ b i)
    (hfront : ∀ i, W i ∩ frontier D = {a i, b i}) (hWD : ∀ i, W i ⊆ D)
    (hupper : ∀ x ∈ D, 0 ≤ x.2) (hDaxis : D ∩ Z ⊆ frontier D)
    (hdis : Pairwise fun i j => Disjoint (W i) (W j))
    (seed : ι) (hseedaxis : a seed ∈ Z ∧ b seed ∈ Z)
    (hC : Convex ℝ C) (hseed : W seed ⊆ C) (hCD : C ⊆ D) :
    ∃ (i : ι) (u v : V) (B : Set V), u.1 < v.1 ∧ {u, v} = ({a i, b i} : Set V) ∧
      IsFinitePLBallPair V B (W i ∪ segment ℝ u v) ∧ IsCompact B ∧ B ⊆ C ∧
      B ∩ Z = segment ℝ u v ∧ B ∩ (⋃ j, W j) = W i ∧
      (⋃ j, W j) ∩ segment ℝ u v = {u, v} := by
  classical
  let J := {i : ι // a i ∈ Z ∧ b i ∈ Z}
  have hordered (i : J) : ∃ u v : V, u.1 < v.1 ∧
      ({u, v} : Set V) = {a i.val, b i.val} := by
    have hf : (a i.val).1 ≠ (b i.val).1 := fun h =>
      hne i.val (Prod.ext h (i.property.1.trans i.property.2.symm))
    rcases lt_or_gt_of_ne hf with h | h
    · exact ⟨a i.val, b i.val, h, rfl⟩
    · exact ⟨b i.val, a i.val, h, by rw [pair_comm]⟩
  choose u v huv hpairs using hordered
  have hball (i : J) : IsFinitePLBallPair ℝ (W i.val) {u i, v i} :=
    (hpairs i).symm ▸ hW i.val
  have haxis (i : J) : W i.val ∩ Z = {u i, v i} := by
    rw [hpairs i]
    apply Subset.antisymm
    · exact fun x hx => (hfront i.val).subset ⟨hx.1, hDaxis ⟨hWD i.val hx.1, hx.2⟩⟩
    · intro x hx
      refine ⟨(hW i.val).1 hx, ?_⟩
      rcases hx with hx | hx
      · exact hx.symm ▸ i.property.1
      · exact hx.symm ▸ i.property.2
  have hdisJ : Pairwise fun i j : J => Disjoint (W i.val) (W j.val) :=
    fun i j hij => hdis (fun h => hij (Subtype.ext h))
  obtain ⟨i, B, hB, hcompact, hBC, hBaxis, hBreturn, _, n, P, hP, hi, hPu, hboundary, hBP⟩ :=
    exists_innermost_returning_disk_in_seed_strip (fun i : J => W i.val) u v hball huv
      (fun i x hx => hupper x (hWD i.val hx)) haxis hdisJ ⟨seed, hseedaxis⟩ hC hseed
  have hBD : B ⊆ D := hBC.trans hCD
  have hBfull : B ∩ (⋃ j, W j) = W i.val := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxW⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxW
      by_cases hj : a j ∈ Z ∧ b j ∈ Z
      · exact hBreturn.subset ⟨hxB, mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩⟩
      · have hij : i.val ≠ j := by
          intro h
          exact hj (h ▸ i.property)
        have havoid := P.closed_returning_disk_disjoint_of_nonreturning_component
          hP hi hPu hboundary (hball i) (haxis i) (huv i) (hW j) (hfront j) (hWD j)
          hupper hDaxis (hBP ▸ hBD) (hdis hij) hj
        exact (disjoint_left.mp havoid (hBP ▸ hxB) hxj).elim
    · intro x hx
      exact ⟨hB.1 (Or.inl hx), mem_iUnion.mpr ⟨i.val, hx⟩⟩
  refine ⟨i.val, u i, v i, B, huv i, hpairs i, hB, hcompact, hBC, hBaxis, hBfull, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxW, hxseg⟩
    have hxB := hB.1 (Or.inr hxseg)
    have hxaxis := (hBaxis.symm.subset hxseg).2
    exact (haxis i).subset ⟨hBfull.subset ⟨hxB, hxW⟩, hxaxis⟩
  · intro x hx
    refine ⟨mem_iUnion.mpr ⟨i.val, (hball i).1 hx⟩, ?_⟩
    rcases hx with hx | hx
    · rw [hx]
      exact left_mem_segment ℝ _ _
    · rw [hx]
      exact right_mem_segment ℝ _ _

end PoincareConjecture.M76.Dehn
