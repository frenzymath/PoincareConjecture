import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.SupportedMoveContactSet
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts
import Mathlib.Data.Set.Card.Arithmetic









set_option autoImplicit false
open Set Geometry
open scoped BigOperators

namespace PoincareConjecture.M76

theorem pairwise_disjoint_original_edge_contacts
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    (S : Set X) (hSV : Disjoint S (g '' K.vertices)) :
    Pairwise fun a b : K.FaceOfCard 2 =>
      Disjoint ((g '' convexHull ℝ (a.1 : Set E)) ∩ S)
        ((g '' convexHull ℝ (b.1 : Set E)) ∩ S) := by
  classical
  intro a b hab
  apply disjoint_left.mpr
  rintro y ⟨⟨x, hx, rfl⟩, hxS⟩ ⟨⟨z, hz, hzx⟩, _⟩
  have hzx' : z = x := hgi (K.convexHull_subset_space b.2.1 hz)
    (K.convexHull_subset_space a.2.1 hx) hzx
  have hxinter : x ∈ convexHull ℝ ((a.1 ∩ b.1 : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull a.2.1 b.2.1]
    exact ⟨hx, hzx' ▸ hz⟩
  have hne : (a.1 ∩ b.1).Nonempty := by
    exact convexHull_nonempty_iff.mp ⟨x, hxinter⟩
  have hlt : (a.1 ∩ b.1).card < a.1.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hsub : a.1 ⊆ b.1 := heq ▸ Finset.inter_subset_right
    exact hab (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [a.2.2, b.2.2])))
  have hc : (a.1 ∩ b.1).card = 1 := by
    have := hne.card_pos
    rw [a.2.2] at hlt
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  have hxv : x = v := by
    simpa only [hv, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hxinter
  have hva : v ∈ a.1 := Finset.mem_of_mem_inter_left
    (show v ∈ a.1 ∩ b.1 by rw [hv]; simp)
  exact disjoint_left.mp hSV hxS ⟨v, K.face_subset_vertices a.2.1 hva, congrArg g hxv.symm⟩

theorem ncard_original_skeleton_contacts_eq_sum
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) [Fintype (K.FaceOfCard 2)]
    (g : E → X) (hgi : InjOn g K.space)
    (S : Set X) (hSV : Disjoint S (g '' K.vertices))
    (hfinite : ∀ a : K.FaceOfCard 2, ((g '' convexHull ℝ (a.1 : Set E)) ∩ S).Finite) :
    ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ S).ncard =
      ∑ a : K.FaceOfCard 2, ((g '' convexHull ℝ (a.1 : Set E)) ∩ S).ncard := by
  rw [iUnion_inter]
  simpa only [finsum_eq_sum_of_fintype] using
    ncard_iUnion_of_finite hfinite (pairwise_disjoint_original_edge_contacts K g hgi S hSV)

theorem ncard_original_skeleton_contacts_remove_pair
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgi : InjOn g K.space)
    (S T : Set X) (hSV : Disjoint S (g '' K.vertices))
    (hTV : Disjoint T (g '' K.vertices))
    (hfinite : ∀ a : K.FaceOfCard 2, ((g '' convexHull ℝ (a.1 : Set E)) ∩ S).Finite)
    (a : K.FaceOfCard 2) {x y : X} (hxy : x ≠ y)
    (hx : x ∈ (g '' convexHull ℝ (a.1 : Set E)) ∩ S)
    (hy : y ∈ (g '' convexHull ℝ (a.1 : Set E)) ∩ S)
    (hselected : (g '' convexHull ℝ (a.1 : Set E)) ∩ T =
      ((g '' convexHull ℝ (a.1 : Set E)) ∩ S) \ {x, y})
    (hother : ∀ b : K.FaceOfCard 2, b ≠ a →
      (g '' convexHull ℝ (b.1 : Set E)) ∩ T =
        (g '' convexHull ℝ (b.1 : Set E)) ∩ S) :
    ((⋃ b : K.FaceOfCard 2, g '' convexHull ℝ (b.1 : Set E)) ∩ T).ncard + 2 =
      ((⋃ b : K.FaceOfCard 2, g '' convexHull ℝ (b.1 : Set E)) ∩ S).ncard := by
  classical
  let := K.finite_faceOfCard hK 2
  let := Fintype.ofFinite (K.FaceOfCard 2)
  have hfiniteT (b : K.FaceOfCard 2) : ((g '' convexHull ℝ (b.1 : Set E)) ∩ T).Finite := by
    by_cases hba : b = a
    · subst b
      rw [hselected]
      exact (hfinite a).sdiff
    · rw [hother b hba]
      exact hfinite b
  rw [ncard_original_skeleton_contacts_eq_sum K g hgi T hTV hfiniteT,
    ncard_original_skeleton_contacts_eq_sum K g hgi S hSV hfinite]
  let f := fun b : K.FaceOfCard 2 => ((g '' convexHull ℝ (b.1 : Set E)) ∩ S).ncard
  let f' := fun b : K.FaceOfCard 2 => ((g '' convexHull ℝ (b.1 : Set E)) ∩ T).ncard
  have hp : ({x, y} : Set X) ⊆ (g '' convexHull ℝ (a.1 : Set E)) ∩ S :=
    pair_subset_iff.mpr ⟨hx, hy⟩
  have hcount : 2 ≤ f a := by
    have := ncard_le_ncard hp (hfinite a)
    simpa only [ncard_pair hxy] using this
  have hdrop : f' a = f a - 2 := by
    dsimp [f', f]
    rw [hselected, ncard_sdiff hp, ncard_pair hxy]
  have hrest : (∑ b ∈ Finset.univ.erase a, f' b) = ∑ b ∈ Finset.univ.erase a, f b := by
    apply Finset.sum_congr rfl
    intro b hb
    exact congrArg Set.ncard (hother b (Finset.mem_erase.mp hb).1)
  change (∑ b, f' b) + 2 = ∑ b, f b
  rw [← Finset.sum_erase_add Finset.univ f' (Finset.mem_univ a),
    ← Finset.sum_erase_add Finset.univ f (Finset.mem_univ a), hrest, hdrop]
  omega

end PoincareConjecture.M76
