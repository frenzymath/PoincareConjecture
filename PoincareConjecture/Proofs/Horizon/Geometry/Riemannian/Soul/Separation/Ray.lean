import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Ray
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence










set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

theorem IsMinimizingOn.continuousOn {curve : ℝ → M} {I : Set ℝ}
    (hcurve : IsMinimizingOn curve I) : ContinuousOn curve I := by
  apply LipschitzOnWith.continuousOn (K := 1)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  simp only [hcurve hs ht, Real.dist_eq, NNReal.coe_one, one_mul, le_refl]

theorem IsRay.continuousOn {ray : ℝ → M} (hray : IsRay ray) :
    ContinuousOn ray (Ici 0) := by
  apply LipschitzOnWith.continuousOn (K := 1)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  simp only [hray hs ht, Real.dist_eq, NNReal.coe_one, one_mul, le_refl]

theorem IsRay.eventually_not_mem_compact {ray : ℝ → M} (hray : IsRay ray)
    {K : Set M} (hK : IsCompact K) : ∀ᶠ t in atTop, ray t ∉ K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (ray 0)
  filter_upwards [eventually_gt_atTop (max R 0)] with t ht hmem
  have ht0 : 0 ≤ t := (le_max_right R 0).trans ht.le
  have hdist := hR hmem
  rw [mem_closedBall, hray ht0 le_rfl, sub_zero, abs_of_nonneg ht0] at hdist
  exact (not_lt_of_ge hdist) ((le_max_left R 0).trans_lt ht)

private theorem exists_frontier_time {curve : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hcurve : ContinuousOn curve (Icc a b))
    {A : Set M} (hA : IsOpen A) (ha : curve a ∈ A) (hb : curve b ∉ A) :
    ∃ t ∈ Icc a b, curve t ∈ frontier A := by
  by_contra h
  push Not at h
  have hdisj : Disjoint (curve '' Icc a b) (frontier A) := by
    apply disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ hy
    exact h t ht hy
  have hsub := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    (isPreconnected_Icc.image curve hcurve) hdisj
    ⟨curve a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩, hA.interior_eq.symm ▸ ha⟩
  exact hb (interior_subset (hsub ⟨b, ⟨hab, le_rfl⟩, rfl⟩))



theorem IsMinimizingOn.exists_frontier_distance_le_of_mem
    {curve : ℝ → M} {L : ℝ} (hcurve : IsMinimizingOn curve (Icc 0 L))
    {A : Set M} (hA : IsOpen A) (hout : curve L ∉ A)
    {C : ℝ} (hbound : ∀ y ∈ frontier A, dist (curve 0) y ≤ C)
    {t : ℝ} (ht : t ∈ Icc 0 L) (hmem : curve t ∈ A) :
    ∃ y ∈ frontier A, dist (curve t) y ≤ C - t := by
  obtain ⟨u, hu, huf⟩ := exists_frontier_time ht.2
    (hcurve.continuousOn.mono (fun s hs => ⟨ht.1.trans hs.1, hs.2⟩)) hA hmem hout
  have huI : u ∈ Icc 0 L := ⟨ht.1.trans hu.1, hu.2⟩
  have hbound := hbound (curve u) huf
  rw [hcurve ⟨le_rfl, ht.1.trans ht.2⟩ huI, zero_sub, abs_neg,
    abs_of_nonneg huI.1] at hbound
  refine ⟨curve u, huf, ?_⟩
  rw [hcurve ht huI, abs_of_nonpos (by linarith [hu.1])]
  linarith


theorem IsRay.exists_later_frontier_time {ray : ℝ → M} (hray : IsRay ray)
    {A : Set M} (hA : IsOpen A) (hAc : IsCompact (closure A))
    {t : ℝ} (ht : 0 ≤ t) (hmem : ray t ∈ A) :
    ∃ u : ℝ, t < u ∧ ray u ∈ frontier A := by
  obtain ⟨v, hv, hvout⟩ := ((eventually_gt_atTop t).and
    (hray.eventually_not_mem_compact hAc)).exists
  obtain ⟨u, hu, huf⟩ := exists_frontier_time hv.le
    (hray.continuousOn.mono (fun s hs => ht.trans hs.1)) hA hmem
    (fun h => hvout (subset_closure h))
  refine ⟨u, lt_of_le_of_ne hu.1 ?_, huf⟩
  intro heq
  subst u
  exact huf.2 (hA.interior_eq.symm ▸ hmem)



theorem IsRay.time_le_of_mem_compact_side {ray : ℝ → M} (hray : IsRay ray)
    {A : Set M} (hA : IsOpen A) (hAc : IsCompact (closure A))
    {D : ℝ} (hdiam : ∀ x ∈ frontier A, ∀ y ∈ frontier A, dist x y ≤ D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hstart : ray s ∈ frontier A) (hmem : ray t ∈ A) : t - s < D := by
  obtain ⟨u, htu, hu⟩ := hray.exists_later_frontier_time hA hAc (hs.trans hst) hmem
  have hbound := hdiam (ray s) hstart (ray u) hu
  rw [hray hs (hs.trans (hst.trans htu.le)), abs_of_nonpos (by linarith)] at hbound
  linarith



theorem IsRay.exists_frontier_distance_le_of_mem_compact_side
    {ray : ℝ → M} (hray : IsRay ray) {A : Set M}
    (hA : IsOpen A) (hAc : IsCompact (closure A))
    {C s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hbound : ∀ y ∈ frontier A, dist (ray s) y ≤ C)
    (hmem : ray t ∈ A) :
    ∃ y ∈ frontier A, dist (ray t) y ≤ C - (t - s) := by
  obtain ⟨u, htu, hu⟩ := hray.exists_later_frontier_time hA hAc (hs.trans hst) hmem
  have hbound := hbound (ray u) hu
  have hu0 : 0 ≤ u := hs.trans (hst.trans htu.le)
  rw [hray hs hu0, abs_of_nonpos (by linarith)] at hbound
  refine ⟨ray u, hu, ?_⟩
  rw [hray (hs.trans hst) hu0, abs_of_nonpos (by linarith)]
  linarith



theorem IsRay.exists_frontier_distance_le_half_diameter
    {ray : ℝ → M} (hray : IsRay ray) {A : Set M}
    (hA : IsOpen A) (hAc : IsCompact (closure A))
    {D : ℝ} (hdiam : ∀ x ∈ frontier A, ∀ y ∈ frontier A, dist x y ≤ D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hstart : ray s ∉ A) (hmem : ray t ∈ A) :
    ∃ y ∈ frontier A, dist (ray t) y ≤ D / 2 := by
  obtain ⟨u, htu, huf⟩ := hray.exists_later_frontier_time hA hAc (hs.trans hst) hmem
  have hpre : ∃ v ∈ Icc s t, ray v ∈ frontier A := by
    by_contra h
    push Not at h
    have hd : Disjoint (ray '' Icc s t) (frontier A) := by
      apply disjoint_left.mpr
      rintro y ⟨v, hv, rfl⟩ hy
      exact h v hv hy
    have hsub := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      (isPreconnected_Icc.image ray (hray.continuousOn.mono
        (fun v hv => hs.trans hv.1))) hd
      ⟨ray t, ⟨t, ⟨hst, le_rfl⟩, rfl⟩, hA.interior_eq.symm ▸ hmem⟩
    exact hstart (interior_subset (hsub ⟨s, ⟨le_rfl, hst⟩, rfl⟩))
  obtain ⟨v, hv, hvf⟩ := hpre
  have hbound := hdiam (ray v) hvf (ray u) huf
  rw [hray (hs.trans hv.1) (hs.trans (hst.trans htu.le)),
    abs_of_nonpos (by linarith [hv.2])] at hbound
  by_cases hnear : t - v ≤ D / 2
  · refine ⟨ray v, hvf, ?_⟩
    rwa [hray (hs.trans hst) (hs.trans hv.1), abs_of_nonneg (by linarith [hv.2])]
  · refine ⟨ray u, huf, ?_⟩
    rw [hray (hs.trans hst) (hs.trans (hst.trans htu.le)),
      abs_of_nonpos (by linarith)]
    linarith

end Poincare.Riemannian.Soul
