import PoincareConjecture.Proofs.M35.Thm12_28.NeckExitTime

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.StandardCylinderPatch

theorem exists_first_axial_exit_of_mem {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) {a : ℝ} (hal : a < length)
    (gamma : ℝ → StandardCapSpace) (hgamma : ContinuousOn gamma (Icc 0 1))
    (hstart : gamma 0 ∈ N.coordinate '' (univ ×ˢ Ioo (-a) a))
    (hend : gamma 1 ∉ N.carrier) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      (∀ s ∈ Icc 0 t, gamma s ∈ N.coordinate '' (univ ×ˢ Icc (-a) a)) ∧
      |(N.inverse (gamma t)).2| = a := by
  let U := N.coordinate '' (univ ×ˢ Ioo (-a) a)
  let K := N.coordinate '' (univ ×ˢ Icc (-a) a)
  have hU : IsOpen U := N.open_axial_slab hal.le
  have hK : IsClosed K := (N.compact_axial_slab hal).isClosed
  have hUK : U ⊆ K := image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hKC : K ⊆ N.carrier := N.closed_axial_slab_subset_carrier hal
  have hzero : gamma 0 ∈ U := hstart
  let T := Icc (0 : ℝ) 1 ∩ gamma ⁻¹' Uᶜ
  have hT : IsCompact T := isCompact_Icc.of_isClosed_subset
    (hgamma.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl) inter_subset_left
  have hone : (1 : ℝ) ∈ T := ⟨⟨by norm_num, le_rfl⟩,
    fun h => hend (hKC (hUK h))⟩
  obtain ⟨t, ht, hmin⟩ := hT.exists_isMinOn ⟨1, hone⟩ continuousOn_id
  have htpos : 0 < t := by
    by_contra h
    have heq : t = 0 := le_antisymm (le_of_not_gt h) ht.1.1
    exact ht.2 (heq ▸ hzero)
  have hbefore : ∀ s ∈ Ico 0 t, gamma s ∈ U := by
    intro s hs
    by_contra h
    have hsmall : t ≤ s := hmin ⟨⟨hs.1, hs.2.le.trans ht.1.2⟩, h⟩
    exact (not_lt_of_ge hsmall) hs.2
  have hendK : gamma t ∈ K := by
    have hc : ContinuousWithinAt gamma (Ico 0 t) t :=
      (hgamma t ht.1).mono (fun s hs => ⟨hs.1, hs.2.le.trans ht.1.2⟩)
    have hcl : t ∈ closure (Ico 0 t) := by
      rw [closure_Ico htpos.ne]
      exact ⟨htpos.le, le_rfl⟩
    exact hK.closure_eq ▸ hc.mem_closure hcl (fun s hs => hUK (hbefore s hs))
  refine ⟨t, ⟨htpos, ht.1.2⟩, ?_, N.axial_abs_eq_at_slab_exit hal hendK ht.2⟩
  intro s hs
  rcases hs.2.eq_or_lt with rfl | hst
  · exact hendK
  · exact hUK (hbefore s ⟨hs.1, hst⟩)

end PoincareConjecture.StandardCylinderPatch
