import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CompactBicollarRestriction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.DisjointUnionBicollar
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc










set_option autoImplicit false
open Set

namespace PoincareConjecture.M76



theorem compact_signed_collar_enlargement
    {E X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X]
    {P : Set X} (hP : IsCompact P) {K : Set E} (hK : IsCompact K)
    (c : E × ℝ → X) {r eps : ℝ} (heps : 0 < eps) (hepsr : eps < r)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier P)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ P ↔ 0 ≤ z.2)
    (hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r))) :
    let D := P ∪ c '' (K ×ˢ Icc (-eps) 0)
    IsCompact D ∧ P ⊆ interior D ∧
      frontier D = c '' (K ×ˢ ({-eps} : Set ℝ)) := by
  intro D
  have hr : 0 < r := heps.trans hepsr
  have hsub : K ×ˢ Icc (-eps) 0 ⊆ K ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2.trans hr.le⟩
  have hD : IsCompact D := hP.union ((hK.prod isCompact_Icc).image_of_continuousOn (hc.mono hsub))
  have hsmall : IsOpen (c '' (K ×ˢ Ioo (-eps) eps)) := by
    let A : Set (E × ℝ) := K ×ˢ Icc (-r) r
    let V : Set A := (fun z => z.1.2) ⁻¹' Ioo (-eps) eps
    let f : A → X := fun z => c z
    have hV : IsOpen V := isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)
    have hVW : f '' V ⊆ c '' (K ×ˢ Ioo (-r) r) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.property.1, by linarith [hz.1], by linarith [hz.2]⟩, rfl⟩
    have hWr : c '' (K ×ˢ Ioo (-r) r) ⊆ range f := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩
    have heq : f '' V = c '' (K ×ˢ Ioo (-eps) eps) := by
      apply subset_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact ⟨z, ⟨z.property.1, hz⟩, rfl⟩
      · rintro _ ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩, hz.2, rfl⟩
    rw [← heq]
    exact hi.isInducing.isOpen_image_of_subset_open hV hopen hVW hWr
  let O := interior P ∪ c '' (K ×ˢ Ioo (-eps) eps)
  have hOo : IsOpen O := isOpen_interior.union hsmall
  have hOD : O ⊆ D := by
    rintro x (hx | ⟨z, hz, rfl⟩)
    · exact Or.inl (interior_subset hx)
    · by_cases ht : 0 ≤ z.2
      · exact Or.inl ((hside z ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩).mpr ht)
      · exact Or.inr ⟨z, ⟨hz.1, hz.2.1.le, (lt_of_not_ge ht).le⟩, rfl⟩
  have hOi : O ⊆ interior D := interior_maximal hOD hOo
  have hPO : P ⊆ O := by
    intro x hx
    by_cases hxint : x ∈ interior P
    · exact Or.inl hxint
    · have hxfront : x ∈ frontier P := ⟨subset_closure hx, hxint⟩
      obtain ⟨z, hz, rfl⟩ := hzero.symm.subset hxfront
      have ht : z.2 = 0 := hz.2
      exact Or.inr ⟨z, ⟨hz.1, by rw [ht]; constructor <;> linarith⟩, rfl⟩
  have hPi : P ⊆ interior D := hPO.trans hOi
  refine ⟨hD, hPi, subset_antisymm ?_ ?_⟩
  · intro x hx
    rcases hD.isClosed.frontier_subset hx with hxP | ⟨z, hz, rfl⟩
    · exact False.elim (hx.2 (hPi hxP))
    · have ht : z.2 = -eps := by
        by_contra ht
        have hlow : -eps < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm ht)
        exact hx.2 (hOi (Or.inr ⟨z, ⟨hz.1, hlow, hz.2.2.trans_lt heps⟩, rfl⟩))
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    have ht : z.2 = -eps := hz.2
    have hzD : c z ∈ D := Or.inr ⟨z, ⟨hz.1, by rw [ht]; exact ⟨le_rfl, neg_nonpos.mpr heps.le⟩⟩, rfl⟩
    refine ⟨subset_closure hzD, ?_⟩
    have hout : MapsTo c (K ×ˢ Ioo (-r) (-eps)) Dᶜ := by
      intro w hw hwD
      rcases hwD with hwP | ⟨v, hv, hvw⟩
      · have hnonneg := (hside w ⟨hw.1, hw.2.1.le, by linarith [hw.2.2]⟩).mp hwP
        linarith [hw.2.2]
      · have hvw' : v = w := congrArg Subtype.val
          (hi.injective (a₁ := ⟨v, hsub hv⟩)
            (a₂ := ⟨w, hw.1, hw.2.1.le, by linarith [hw.2.2]⟩) hvw)
        have heq := congrArg Prod.snd hvw'
        linarith [hv.2.1, hw.2.2]
    have hcl : closure (K ×ˢ Ioo (-r) (-eps)) = K ×ˢ Icc (-r) (-eps) := by
      rw [closure_prod_eq, hK.isClosed.closure_eq, closure_Ioo (by linarith : -r ≠ -eps)]
    have hcont : ContinuousOn c (closure (K ×ˢ Ioo (-r) (-eps))) := by
      rw [hcl]
      exact hc.mono (prod_mono subset_rfl (Icc_subset_Icc le_rfl (by linarith)))
    have hlimit := hout.closure_of_continuousOn hcont
      (hcl.symm.subset (show z ∈ K ×ˢ Icc (-r) (-eps) from
        ⟨hz.1, by rw [ht]; exact ⟨by linarith, le_rfl⟩⟩))
    simpa only [closure_compl, mem_compl_iff] using hlimit



theorem compact_phase_collar_enlargement
    {E X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X] {p : ℝ} [Fact (0 < p)]
    {P : Set X} (hP : IsCompact P) {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (c : E × ℝ → X) {r eps : ℝ} (heps : 0 < eps) (hepsr : eps < r)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier P)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ P ↔ 0 ≤ z.2)
    (hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (q : C(X, AddCircle p)) {theta l u cut : ℝ} (htheta : theta ∈ Icc l u)
    (hphase : ∀ z ∈ K ×ˢ Icc (-eps) 0, q (c z) = ((theta + z.2 : ℝ) : AddCircle p))
    (hrange : P ⊆ q ⁻¹' AddCircle.closedIntervalArc p l u)
    (hcut : cut < min l (theta - eps)) (hu : u < cut + p) :
    let D := P ∪ c '' (K ×ˢ Icc (-eps) 0)
    IsCompact D ∧ P ⊆ interior D ∧
      frontier D = c '' (K ×ˢ ({-eps} : Set ℝ)) ∧
      (∀ x ∈ frontier D, q x = ((theta - eps : ℝ) : AddCircle p)) ∧
      D ⊆ q ⁻¹' AddCircle.closedIntervalArc p (min l (theta - eps)) u ∧
      theta - eps ∈ Icc (min l (theta - eps)) u ∧
      cut < min l (theta - eps) ∧ u < cut + p ∧
      ((q ⁻¹' {(theta : AddCircle p)}) ∩ interior D).Nonempty := by
  intro D
  obtain ⟨hD, hPi, hfront⟩ := compact_signed_collar_enlargement hP hK c heps hepsr
    hc hi hzero hside hopen
  refine ⟨hD, hPi, hfront, ?_, ?_, ⟨min_le_right _ _, by linarith [htheta.2]⟩,
    hcut, hu, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hfront.subset hx
    have ht : z.2 = -eps := hz.2
    rw [hphase z ⟨hz.1, by rw [ht]; exact ⟨le_rfl, neg_nonpos.mpr heps.le⟩⟩,
      ht, ← sub_eq_add_neg]
  · rintro x (hx | ⟨z, hz, rfl⟩)
    · obtain ⟨s, hs, heq⟩ := hrange hx
      exact ⟨s, ⟨(min_le_left _ _).trans hs.1, hs.2⟩, heq⟩
    · change q (c z) ∈ AddCircle.closedIntervalArc p (min l (theta - eps)) u
      rw [hphase z hz]
      exact ⟨theta + z.2, ⟨(min_le_right _ _).trans (by linarith [hz.2.1]),
        by linarith [htheta.2, hz.2.2]⟩, rfl⟩
  · obtain ⟨z, hz⟩ := hne
    have hbase : c (z, 0) ∈ frontier P := hzero.subset ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩
    refine ⟨c (z, 0), ?_, hPi (hP.isClosed.frontier_subset hbase)⟩
    change q (c (z, 0)) = (theta : AddCircle p)
    rw [hphase (z, 0) ⟨hz, neg_nonpos.mpr heps.le, le_rfl⟩, add_zero]



theorem compact_signed_two_collar_enlargement
    {E F X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace F] [T2Space F] [TopologicalSpace X] [T2Space X]
    {P : Set X} (hP : IsCompact P)
    {K0 : Set E} {K1 : Set F} (hK0 : IsCompact K0) (hK1 : IsCompact K1)
    (c0 : E × ℝ → X) (c1 : F × ℝ → X)
    {r eps : ℝ} (heps : 0 < eps) (hepsr : eps < r)
    (hi0 : Topology.IsEmbedding (fun z : (K0 ×ˢ Icc (-r) r : Set (E × ℝ)) => c0 z))
    (hi1 : Topology.IsEmbedding (fun z : (K1 ×ˢ Icc (-r) r : Set (F × ℝ)) => c1 z))
    (hdis : Disjoint (c0 '' (K0 ×ˢ Icc (-r) r)) (c1 '' (K1 ×ˢ Icc (-r) r)))
    (hzero : c0 '' (K0 ×ˢ ({0} : Set ℝ)) ∪ c1 '' (K1 ×ˢ ({0} : Set ℝ)) = frontier P)
    (hside0 : ∀ z ∈ K0 ×ˢ Icc (-r) r, c0 z ∈ P ↔ 0 ≤ z.2)
    (hside1 : ∀ z ∈ K1 ×ˢ Icc (-r) r, c1 z ∈ P ↔ 0 ≤ z.2)
    (hopen0 : IsOpen (c0 '' (K0 ×ˢ Ioo (-r) r)))
    (hopen1 : IsOpen (c1 '' (K1 ×ˢ Ioo (-r) r))) :
    let D := P ∪ (c0 '' (K0 ×ˢ Icc (-eps) 0) ∪ c1 '' (K1 ×ˢ Icc (-eps) 0))
    IsCompact D ∧ P ⊆ interior D ∧
      frontier D = c0 '' (K0 ×ˢ ({-eps} : Set ℝ)) ∪
        c1 '' (K1 ×ˢ ({-eps} : Set ℝ)) := by
  intro D
  let K : Set (E ⊕ F) := Sum.inl '' K0 ∪ Sum.inr '' K1
  let c := Poincare.Topology.sumBicollarMap c0 c1
  have hK : IsCompact K := (hK0.image continuous_inl).union (hK1.image continuous_inr)
  have hi : Topology.IsEmbedding
      (fun z : (K ×ˢ Icc (-r) r : Set ((E ⊕ F) × ℝ)) => c z) :=
    Poincare.Topology.isEmbedding_sumBicollarMap hK0 hK1 isCompact_Icc c0 c1 hi0 hi1 hdis
  have hc : ContinuousOn c (K ×ˢ Icc (-r) r) := continuousOn_iff_continuous_domRestrict.mpr hi.continuous
  have hzero' : c '' (K ×ˢ ({0} : Set ℝ)) = frontier P := by
    rw [Poincare.Topology.image_sumBicollarMap]
    exact hzero
  have hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ P ↔ 0 ≤ z.2 := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact hside0 (x, t) ⟨hx, ht⟩
    · exact hside1 (x, t) ⟨hx, ht⟩
  have hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r)) := by
    rw [Poincare.Topology.image_sumBicollarMap]
    exact hopen0.union hopen1
  have h := compact_signed_collar_enlargement hP hK c heps hepsr hc hi hzero' hside hopen
  simpa only [c, K, Poincare.Topology.image_sumBicollarMap] using h

end PoincareConjecture.M76
