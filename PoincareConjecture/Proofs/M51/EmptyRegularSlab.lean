import PoincareConjecture.Proofs.M51.EmptyFamily
import PoincareConjecture.Proofs.M51.EmptySlabCopy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

noncomputable def regularSlab (p q : ℝ) (hpq : p < q)
    (hJ : Icc p q ⊆ Ici 0) (hfree : Disjoint F.surgery_times (Ioc p q)) :
    SurgeryRegularSlab (slice F a) (metric F a) p q := by
  classical
  by_cases hqa : q ≤ a
  · have hOld : Icc p q ⊆ F.time_domain := fun t ht =>
      F.time_domain_interval.out F.zero_mem ha ⟨hJ ht, ht.2.trans hqa⟩
    exact (F.regular_slabs p q hpq hOld hfree).m51_reindexPast
      (fun t => min t a) (fun t ht => min_eq_left (ht.trans hqa))
  · have hp : 0 ≤ p := hJ ⟨le_rfl, hpq.le⟩
    letI := crossing_empty F a ha hp (lt_of_not_ge hqa) hfree
    refine {
      ordered := hpq
      flow := emptyFlow (slice F a p) (metric F a p) (connection F a p) hpq
      identify := fun t => ?_
      initial_identify := fun x => isEmptyElim x
      metric_pullback := fun _ x => isEmptyElim x }
    letI := empty_forward F a ha hp t.2.1 inferInstance
    exact Diffeomorph.empty

theorem regularSlab_transport_heq (p q : ℝ) (hpq : p < q)
    (hJ : Icc p q ⊆ Ici 0) (hfree : Disjoint F.surgery_times (Ioc p q))
    (hqa : q ≤ a) (hOld : Icc p q ⊆ F.time_domain) (s t : Icc p q)
    {x : (F.slice s.1).carrier} {y : (slice F a s.1).carrier} (hy : HEq y x) :
    HEq ((regularSlab F ha p q hpq hJ hfree).transport s t y)
      ((F.regular_slabs p q hpq hOld hfree).transport s t x) := by
  classical
  simpa only [regularSlab, dif_pos hqa] using
    (F.regular_slabs p q hpq hOld hfree).m51_reindexPast_transport_heq
      (fun t => min t a) (fun t ht => min_eq_left (ht.trans hqa)) s t hy

include ha in

theorem regularSlab_end_le (p q : ℝ) (hpq : p < q)
    (hJ : Icc p q ⊆ Ici 0) (hfree : Disjoint F.surgery_times (Ioc p q))
    {s : ℝ} (hs : s ∈ Icc p q) (x : (slice F a s).carrier) : q ≤ a := by
  by_contra hqa
  have hp : 0 ≤ p := hJ ⟨le_rfl, hpq.le⟩
  let := empty_forward F a ha hp hs.1
    (crossing_empty F a ha hp (lt_of_not_ge hqa) hfree)
  exact isEmptyElim x

theorem regularSlab_coherent (p q r w : ℝ) (hpq : p < q)
    (hJ : Icc p q ⊆ Ici 0) (hfree : Disjoint F.surgery_times (Ioc p q))
    (hrw : r < w) (hK : Icc r w ⊆ Ici 0)
    (hfree' : Disjoint F.surgery_times (Ioc r w))
    (s t : ℝ) (hs : s ∈ Icc p q) (ht : t ∈ Icc p q)
    (hs' : s ∈ Icc r w) (ht' : t ∈ Icc r w) (x : (slice F a s).carrier) :
    (regularSlab F ha p q hpq hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩ x =
      (regularSlab F ha r w hrw hK hfree').transport ⟨s, hs'⟩ ⟨t, ht'⟩ x := by
  have hqa := regularSlab_end_le F ha p q hpq hJ hfree hs x
  have hwa := regularSlab_end_le F ha r w hrw hK hfree' hs' x
  have hJold : Icc p q ⊆ F.time_domain := fun z hz =>
    F.time_domain_interval.out F.zero_mem ha ⟨hJ hz, hz.2.trans hqa⟩
  have hKold : Icc r w ⊆ F.time_domain := fun z hz =>
    F.time_domain_interval.out F.zero_mem ha ⟨hK hz, hz.2.trans hwa⟩
  let c := M51EventCopy.identify F.slice (fun z => min z a) s
    (min_eq_left (hs.2.trans hqa))
  let y := c.symm x
  have hy : HEq x y := (M51EventCopy.identify_symm_apply_heq F.slice
    (fun z => min z a) s (min_eq_left (hs.2.trans hqa)) x).symm
  have hfirst := regularSlab_transport_heq F ha p q hpq hJ hfree hqa hJold
    ⟨s, hs⟩ ⟨t, ht⟩ hy
  have hsecond := regularSlab_transport_heq F ha r w hrw hK hfree' hwa hKold
    ⟨s, hs'⟩ ⟨t, ht'⟩ hy
  have hmiddle := F.slab_transport_coherent p q r w hpq hJold hfree
    hrw hKold hfree' s t hs ht hs' ht' y
  exact eq_of_heq ((hfirst.trans (heq_of_eq hmiddle)).trans hsecond.symm)

end PoincareConjecture.M51Empty
