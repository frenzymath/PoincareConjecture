import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Region
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BallPreimage



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private instance : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2



theorem exists_open_region_disk_of_frontier_subset_circle
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q))
    {W : Set S2} (hW : IsOpen W) (hproper : closure W ≠ univ)
    (hfront : frontier W ⊆ range C) (hne : (W \ range C).Nonempty) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = closure W ∧ d '' ball 0 1 = W ∧
      d '' sphere (0 : E2) 1 = range C := by
  obtain ⟨d, hs, hd, hdi, hc, hb⟩ :=
    exists_disk_neighborhood_of_frontier_subset_circle hC hCi hCd
      isClosed_closure hproper (frontier_closure_subset.trans hfront)
      (hne.mono (by
        intro x hx
        exact ⟨hW.subset_interior_iff.mpr subset_closure hx.1, hx.2⟩))
  have hopen : d '' ball (0 : E2) 1 = W := by
    apply Subset.antisymm
    · rintro x ⟨u, hu, rfl⟩
      have hx : d u ∈ closure W := hc ▸ mem_image_of_mem d (ball_subset_closedBall hu)
      by_contra hn
      have hxf : d u ∈ frontier W := ⟨hx, by simpa only [hW.interior_eq] using hn⟩
      obtain ⟨v, hv, hvu⟩ := hb.symm ▸ hfront hxf
      have heq := d.injOn (hs (sphere_subset_closedBall hv))
        (hs (ball_subset_closedBall hu)) hvu
      rw [heq, mem_sphere_zero_iff_norm] at hv
      have hlt := mem_ball_zero_iff.mp hu
      linarith
    · rw [d.image_ball_eq_interior hs hc]
      exact hW.subset_interior_iff.mpr subset_closure
  exact ⟨d, hs, hd, hdi, hc, hopen, hb⟩

private theorem sublevel_component_frontier
    {h : S2 → Real} (hh : Continuous h) (b : Real) (p : S2) :
    frontier (connectedComponentIn (h ⁻¹' Iio b) p) ⊆ {q | h q = b} := by
  intro q hq
  have hf := hh.frontier_preimage_subset _
    (Poincare.Topology.frontier_connectedComponentIn_subset_of_isOpen
      (isOpen_Iio.preimage hh) p hq)
  simpa only [frontier_Iio, mem_preimage, mem_singleton_iff, mem_ofPred_eq] using hf

private theorem sublevel_component_closure
    {h : S2 → Real} (hh : Continuous h) (b : Real) (p : S2) :
    closure (connectedComponentIn (h ⁻¹' Iio b) p) ⊆ h ⁻¹' Iic b :=
  closure_minimal
    ((connectedComponentIn_subset _ _).trans (fun _ hx => le_of_lt (show h _ < b from hx)))
    (isClosed_Iic.preimage hh)



theorem exists_sublevel_component_disk_of_circle_level
    {h : S2 → Real} (hh : Continuous h) {b : Real}
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q))
    (hlevel : {q | h q = b} = range C)
    (habove : ∃ q, b < h q) {p : S2} (hp : h p < b) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = closure (connectedComponentIn (h ⁻¹' Iio b) p) ∧
      d '' ball 0 1 = connectedComponentIn (h ⁻¹' Iio b) p ∧
      d '' sphere (0 : E2) 1 = range C := by
  apply exists_open_region_disk_of_frontier_subset_circle hC hCi hCd
    (isOpen_Iio.preimage hh).connectedComponentIn
  · intro heq
    obtain ⟨q, hq⟩ := habove
    have := sublevel_component_closure hh b p (heq.symm ▸ mem_univ q)
    exact (not_le_of_gt hq) this
  · exact (sublevel_component_frontier hh b p).trans hlevel.subset
  · refine ⟨p, mem_connectedComponentIn hp, ?_⟩
    intro hpC
    have := hlevel.symm ▸ hpC
    exact (ne_of_lt hp) this



theorem exists_sublevel_component_disk_of_separated_circle_pair
    {h : S2 → Real} (hh : Continuous h) {b : Real}
    (C : Fin 2 → S1 → S2) (hC : ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (C i))
    (hCi : ∀ i, Injective (C i))
    (hCd : ∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (C i) q))
    (hlevel : {q | h q = b} = range (C 0) ∪ range (C 1))
    (l : S2 → Real) (hl : Continuous l)
    (hzero : ∀ q, h q ≤ b → l q ≠ 0)
    (hneg : ∀ q, l (C 0 q) < 0) (hpos : ∀ q, 0 < l (C 1 q))
    (habove : ∃ q, b < h q) {p : S2} (hp : h p < b) :
    ∃ i : Fin 2, ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = closure (connectedComponentIn (h ⁻¹' Iio b) p) ∧
      d '' ball 0 1 = connectedComponentIn (h ⁻¹' Iio b) p ∧
      d '' sphere (0 : E2) 1 = range (C i) := by
  let W := connectedComponentIn (h ⁻¹' Iio b) p
  have hW : IsOpen W := (isOpen_Iio.preimage hh).connectedComponentIn
  have hcl : closure W ⊆ h ⁻¹' Iic b := sublevel_component_closure hh b p
  have hproper : closure W ≠ univ := by
    intro heq
    obtain ⟨q, hq⟩ := habove
    exact (not_le_of_gt hq) (hcl (heq.symm ▸ mem_univ q))
  have hf : frontier W ⊆ range (C 0) ∪ range (C 1) :=
    (sublevel_component_frontier hh b p).trans hlevel.subset
  have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_connectedComponentIn : IsPreconnected W)
    {q | l q ≤ 0} {q | 0 ≤ l q}
    (isClosed_le hl continuous_const) (isClosed_le continuous_const hl)
    (fun q _ => le_total (l q) 0) (by
      rw [eq_empty_iff_forall_notMem]
      rintro q ⟨hq, hle, hge⟩
      exact hzero q (hcl (subset_closure hq)) (le_antisymm hle hge))
  have hne (i : Fin 2) : (W \ range (C i)).Nonempty := by
    refine ⟨p, mem_connectedComponentIn hp, ?_⟩
    intro hpi
    have hpl : p ∈ range (C 0) ∪ range (C 1) := by
      fin_cases i
      · exact Or.inl hpi
      · exact Or.inr hpi
    have heq : p ∈ {q | h q = b} := hlevel.symm ▸ hpl
    exact (ne_of_lt hp) heq
  rcases hparts with hn | hp'
  · have hclosed := closure_minimal hn (isClosed_le hl continuous_const)
    refine ⟨0, ?_⟩
    apply exists_open_region_disk_of_frontier_subset_circle (hC 0) (hCi 0) (hCd 0)
      hW hproper ?_ (hne 0)
    intro q hq
    rcases hf hq with hq0 | ⟨z, rfl⟩
    · exact hq0
    · exact (not_le_of_gt (hpos z) (hclosed hq.1)).elim
  · have hclosed := closure_minimal hp' (isClosed_le continuous_const hl)
    refine ⟨1, ?_⟩
    apply exists_open_region_disk_of_frontier_subset_circle (hC 1) (hCi 1) (hCd 1)
      hW hproper ?_ (hne 1)
    intro q hq
    rcases hf hq with ⟨z, rfl⟩ | hq1
    · exact (not_le_of_gt (hneg z) (hclosed hq.1)).elim
    · exact hq1



theorem outside_height_band_component_eq_sublevel
    {X : Type*} [TopologicalSpace X] {h : X → Real} (hh : Continuous h)
    {a b : Real} (hab : a ≤ b) {p : X} (hp : h p < a) :
    connectedComponentIn {q | h q ∉ Icc a b} p =
      connectedComponentIn (h ⁻¹' Iio a) p := by
  have hpO : p ∈ {q | h q ∉ Icc a b} := fun hx => hp.not_ge hx.1
  have hsub : connectedComponentIn {q | h q ∉ Icc a b} p ⊆ h ⁻¹' Iio a := by
    intro x hx
    have hconn : IsPreconnected (connectedComponentIn {q | h q ∉ Icc a b} p) :=
      isPreconnected_connectedComponentIn
    exact hconn.gt_of_ne hh.continuousOn
      (fun y hy he => (connectedComponentIn_subset {q | h q ∉ Icc a b} p hy)
        (he ▸ ⟨le_rfl, hab⟩))
      ⟨p, mem_connectedComponentIn hpO, hp⟩ hx
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hpO) hsub
  · apply connectedComponentIn_mono
    exact fun x hx hi => hx.not_ge hi.1


theorem outside_height_band_component_eq_superlevel
    {X : Type*} [TopologicalSpace X] {h : X → Real} (hh : Continuous h)
    {a b : Real} (hab : a ≤ b) {p : X} (hp : b < h p) :
    connectedComponentIn {q | h q ∉ Icc a b} p =
      connectedComponentIn (h ⁻¹' Ioi b) p := by
  have heq : {q : X | h q ∉ Icc a b} = {q | (-h) q ∉ Icc (-b) (-a)} := by
    ext q
    simp only [Pi.neg_apply, mem_ofPred_eq, mem_Icc, neg_le_neg_iff, and_comm]
  rw [heq]
  simpa only [preimage, Pi.neg_apply, mem_Iio, mem_Ioi, neg_lt_neg_iff] using
    outside_height_band_component_eq_sublevel hh.neg (neg_le_neg hab) (neg_lt_neg hp)



theorem exists_superlevel_component_disk_of_circle_level
    {h : S2 → Real} (hh : Continuous h) {b : Real}
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q))
    (hlevel : {q | h q = b} = range C)
    (hbelow : ∃ q, h q < b) {p : S2} (hp : b < h p) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = closure (connectedComponentIn (h ⁻¹' Ioi b) p) ∧
      d '' ball 0 1 = connectedComponentIn (h ⁻¹' Ioi b) p ∧
      d '' sphere (0 : E2) 1 = range C := by
  have hlevel' : {q | (-h) q = -b} = range C := by
    simpa only [Pi.neg_apply, neg_inj] using hlevel
  obtain ⟨q, hq⟩ := hbelow
  simpa only [preimage, Pi.neg_apply, mem_Iio, mem_Ioi, neg_lt_neg_iff] using
    exists_sublevel_component_disk_of_circle_level hh.neg hC hCi hCd hlevel'
      ⟨q, neg_lt_neg hq⟩ (neg_lt_neg hp)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
