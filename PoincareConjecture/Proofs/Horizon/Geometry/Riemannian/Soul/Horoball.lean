import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CalibratedRay
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false

open Filter Set Metric
open scoped Topology

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

def horoballIntersection (p : M) (r : ℝ) : Set M :=
  {x | ∀ ray : ℝ → M, IsRay ray → ray 0 = p → -r ≤ busemann ray x}

theorem isClosed_horoballIntersection (p : M) (r : ℝ) :
    IsClosed (horoballIntersection p r) := by
  simp only [horoballIntersection, ofPred_forall]
  apply isClosed_iInter
  intro ray
  apply isClosed_iInter
  intro hray
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (lipschitz_busemann hray).continuous

theorem closedBall_subset_horoballIntersection (p : M) (r : ℝ) :
    closedBall p r ⊆ horoballIntersection p r := by
  intro x hx ray hray hray0
  have h := neg_dist_le_busemann hray x
  rw [hray0] at h
  exact (neg_le_neg (mem_closedBall.mp hx)).trans h

theorem horoballIntersection_mono (p : M) : Monotone (horoballIntersection p) := by
  intro r s hrs x hx ray hray hray0
  exact (neg_le_neg hrs).trans (hx ray hray hray0)

theorem horoballIntersection_subset_interior (p : M) {r s : ℝ} (hrs : r < s) :
    horoballIntersection p r ⊆ interior (horoballIntersection p s) := by
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ball_mem_nhds x (sub_pos.mpr hrs))
  intro y hy ray hray hray0
  have hdist := (lipschitz_busemann hray).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hdist
  have hxy : dist x y < s - r := by simpa only [mem_ball, dist_comm] using hy
  have hbound := hx ray hray hray0
  linarith [le_abs_self (busemann ray x - busemann ray y)]

theorem iUnion_horoballIntersection (p : M) :
    ⋃ r : ℝ, horoballIntersection p r = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨dist x p,
    closedBall_subset_horoballIntersection p (dist x p) (by simp)⟩

theorem mapsTo_horoballIntersection_of_concaveOn
    {curve : ℝ → M} {a b r : ℝ} {p : M}
    (hconc : ∀ ray : ℝ → M, IsRay ray → ray 0 = p →
      ConcaveOn ℝ (Icc a b) (busemann ray ∘ curve))
    (ha : curve a ∈ horoballIntersection p r)
    (hb : curve b ∈ horoballIntersection p r) :
    MapsTo curve (Icc a b) (horoballIntersection p r) := by
  intro t ht ray hray hray0
  have hab := ht.1.trans ht.2
  exact (le_min (ha ray hray hray0) (hb ray hray hray0)).trans
    ((hconc ray hray hray0).min_le_of_mem_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ ht)

theorem isCompact_horoballIntersection [ProperSpace M] (p : M) {r : ℝ} (hr : 0 ≤ r)
    (hsegments : ∀ q ∈ horoballIntersection p r, ∃ curve : ℝ → M,
      curve 0 = p ∧ curve (dist p q) = q ∧ IsMinimizingOn curve (Icc 0 (dist p q)) ∧
        MapsTo curve (Icc 0 (dist p q)) (horoballIntersection p r)) :
    IsCompact (horoballIntersection p r) := by
  by_contra hnc
  obtain ⟨ray, hray, hray0, hmem⟩ := exists_ray_in_closed_set
    (isClosed_horoballIntersection p r) hnc hsegments
  have h := hmem (show r + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
    ray hray hray0
  rw [busemann_apply_ray hray (by linarith)] at h
  linarith

theorem infDist_compl_le_busemann [ProperSpace M] (hsegments : HasMinimizingSegments M)
    {p x : M} {c : ℝ} (hx : x ∈ horoballIntersection p c)
    {ray : ℝ → M} (hray : IsRay ray) (hray0 : ray 0 = p) :
    infDist x (horoballIntersection p c)ᶜ ≤ c + busemann ray x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have ht : 0 ≤ c + busemann ray x + ε := by
    have := hx ray hray hray0
    linarith
  obtain ⟨coray, hcoray, hcoray0, hcalibrated⟩ := exists_calibrated_ray hsegments hray x
  have hy : coray (c + busemann ray x + ε) ∈ (horoballIntersection p c)ᶜ := by
    intro hy
    have hbound := hy ray hray hray0
    rw [hcalibrated _ ht] at hbound
    linarith
  have hd : dist x (coray (c + busemann ray x + ε)) = c + busemann ray x + ε := by
    simpa only [hcoray0, zero_sub, abs_neg, abs_of_nonneg ht] using hcoray le_rfl ht
  exact hd ▸ infDist_le_dist_of_mem hy

theorem le_infDist_compl_of_busemann {p x : M} {c r : ℝ}
    (hne : (horoballIntersection p c)ᶜ.Nonempty)
    (hbound : ∀ ray : ℝ → M, IsRay ray → ray 0 = p → r ≤ c + busemann ray x) :
    r ≤ infDist x (horoballIntersection p c)ᶜ := by
  apply (le_infDist hne).2
  intro y hy
  change ¬ (∀ ray : ℝ → M, IsRay ray → ray 0 = p → -c ≤ busemann ray y) at hy
  push Not at hy
  obtain ⟨ray, hray, hray0, hy⟩ := hy
  have hx := hbound ray hray hray0
  have hLip := (lipschitz_busemann hray).le_add_mul x y
  simp only [NNReal.coe_one, one_mul] at hLip
  linarith

theorem innerParallelSet_eq_shift [ProperSpace M] (hsegments : HasMinimizingSegments M)
    (p : M) (c : ℝ) (hne : (horoballIntersection p c)ᶜ.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) :
    {x ∈ horoballIntersection p c | r ≤ infDist x (horoballIntersection p c)ᶜ} =
      horoballIntersection p (c - r) := by
  ext x
  constructor
  · rintro ⟨hx, hd⟩ ray hray hray0
    have := hd.trans (infDist_compl_le_busemann hsegments hx hray hray0)
    linarith
  · intro hx
    have hbound : ∀ ray : ℝ → M, IsRay ray → ray 0 = p → r ≤ c + busemann ray x := by
      intro ray hray hray0
      have := hx ray hray hray0
      linarith
    refine ⟨?_, le_infDist_compl_of_busemann hne hbound⟩
    intro ray hray hray0
    have := hbound ray hray hray0
    linarith

theorem concaveOn_infDist_compl [ProperSpace M] (hsegments : HasMinimizingSegments M)
    {p : M} {c a b : ℝ} (hne : (horoballIntersection p c)ᶜ.Nonempty)
    {curve : ℝ → M} (hmem : MapsTo curve (Icc a b) (horoballIntersection p c))
    (hconc : ∀ ray : ℝ → M, IsRay ray → ray 0 = p →
      ConcaveOn ℝ (Icc a b) (busemann ray ∘ curve)) :
    ConcaveOn ℝ (Icc a b) (fun t => infDist (curve t) (horoballIntersection p c)ᶜ) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro u hu v hv α β hα hβ hsum
  change α * infDist (curve u) (horoballIntersection p c)ᶜ +
    β * infDist (curve v) (horoballIntersection p c)ᶜ ≤ _
  apply le_infDist_compl_of_busemann hne
  intro ray hray hray0
  have hdu := infDist_compl_le_busemann hsegments (hmem hu) hray hray0
  have hdv := infDist_compl_le_busemann hsegments (hmem hv) hray hray0
  have hJ := ((hconc ray hray hray0).add_const c).2 hu hv hα hβ hsum
  simp only [Pi.add_apply, Function.comp_apply, smul_eq_mul] at hJ ⊢
  nlinarith [mul_le_mul_of_nonneg_left hdu hα, mul_le_mul_of_nonneg_left hdv hβ]

end Poincare.Riemannian.Soul
