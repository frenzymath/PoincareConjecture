import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRay
import PoincareConjecture.Proofs.M28.Mathlib.FinitePackingCompactCompletion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedSphereRayCrossing
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedNeckCofinalSequence
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckCompletionRadius
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSpherePacking
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.ChordDefectLimits
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Filter.Finite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}

theorem totallyBounded_selected_end_ray_chord
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (R : M → ℝ) (hR : ContinuousOn R T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        R y ≤ 2 * R z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < R x)
    (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ),
      E ∉ range ((↑) : U → UniformSpace.Completion U) → 0 < alpha →
      (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
        ∀ x : U, c < (A.inverse x).2 →
          dist (x : UniformSpace.Completion U) E < eta) →
      (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
      (∀ p q : U, 0 < f p → 0 < f q →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (mu s) (mu t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
      ∀ m : PseudoMetricSpace (MetricEndRay E alpha),
        letI := m
        (∀ P Q : MetricEndRay E alpha, Tendsto
          (fun p : ℝ × ℝ => chordDefect (fun s t => dist (P.point s) (Q.point t)) p.1 p.2)
          ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 (dist P Q ^ 2))) →
        TotallyBounded (univ : Set (MetricEndRay E alpha)) := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha houtside halpha htail hbarrier hsegments m
  let := m
  intro hlimit
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hheight : ∀ x : U, dist (x : UniformSpace.Completion U) E < alpha →
      (3 / 4 : ℝ) ≤ (A.inverse x).2 :=
    cylinder_height_ge_threeQuarter_of_radius_barrier T A U f hfinite
      E alpha hbarrier hsegments
  obtain ⟨c, index, hc, hcLimit, hactive, hwhole⟩ :=
    exists_cofinal_selected_neck_sequence T A R hR hratio hdiverge
  apply Metric.totallyBounded_univ_of_finite_pair_collision
  intro d0 hd0
  let eta : ℝ := d0 / 8
  have heta : 0 < eta := div_pos hd0 (by norm_num)
  obtain ⟨K, _hKpos, hpacking⟩ := exists_central_sphere_packing_number.{u} heta
  refine ⟨K, ?_⟩
  intro P
  by_contra! hseparated
  have hlarge : ∀ᶠ p : ℝ × ℝ in ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))),
      ∀ i j : Fin (K + 1), i ≠ j →
        3 * d0 ^ 2 / 4 <
          chordDefect (fun s t => dist ((P i).point s) ((P j).point t)) p.1 p.2 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _p hne => (hne hij).elim
    · have hsq : d0 ^ 2 ≤ dist (P i) (P j) ^ 2 :=
        (sq_le_sq₀ hd0.le dist_nonneg).mpr (hseparated i j hij)
      have hmargin : 3 * d0 ^ 2 / 4 < dist (P i) (P j) ^ 2 := by
        nlinarith only [hsq, sq_pos_of_pos hd0]
      exact ((hlimit (P i) (P j)).eventually (lt_mem_nhds hmargin)).mono
        fun _p hp _hne => hp
  obtain ⟨S, hS, V, hV, hSV⟩ := Filter.mem_prod_iff.mp hlarge
  obtain ⟨a, ha, hIa⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hS
  obtain ⟨b, hb, hIb⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hV
  let tau : ℝ := min a b
  have htau : 0 < tau := lt_min ha hb
  have hrectangle (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) tau)
      (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) tau)
      (i j : Fin (K + 1)) (hij : i ≠ j) :
      3 * d0 ^ 2 / 4 <
        chordDefect (fun u v => dist ((P i).point u) ((P j).point v)) s t :=
    hSV (show (s, t) ∈ S ×ˢ V from
      ⟨hIa ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩,
        hIb ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩⟩) i j hij
  obtain ⟨d, _hdhalf, hd1, hdecay⟩ := htail tau htau
  have hdEventually : ∀ᶠ n in atTop, d < c n :=
    hcLimit.eventually (lt_mem_nhds hd1)
  have hstarts : ∀ᶠ n in atTop, ∀ j : Fin (K + 1),
      (A.inverse ((P j).point (P j).length)).2 < c n := by
    apply Filter.eventually_all.mpr
    intro j
    exact hcLimit.eventually (lt_mem_nhds
      (A.inverse_mem ((P j).point (P j).length)
        (hUV ((P j).point (P j).length).property)).2.2)
  obtain ⟨n, hnD, hnStart⟩ := (hdEventually.and hstarts).exists
  let N := T.chain.neck (index n)
  have hNU : N.carrier ⊆ (U : Set M) := by
    intro x hx
    have hh := (A.mem_tail_iff_m28 true
      (lt_trans (by norm_num) (hc n).1) (hc n).2).mp (hwhole n hx)
    rw [hU]
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hh.1, (hc n).1.trans hh.2⟩
  have hcross (j : Fin (K + 1)) :
      ∃ v ∈ Ioo (0 : ℝ) (P j).length,
        ((P j).inward v : M) ∈ N.central_sphere := by
    have hcontinuous : ContinuousOn (P j).inward (Ico (0 : ℝ) (P j).length) :=
      (P j).continuousOn_point.comp (continuous_const.sub continuous_id).continuousOn
        (fun t ht => ⟨sub_pos.mpr ht.2, sub_le_self _ ht.1⟩)
    have hlower (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (P j).length) :
        (3 / 4 : ℝ) ≤ (A.inverse ((P j).inward t)).2 := by
      apply hheight
      rw [(P j).inward_radius t ht]
      have hsmall := (P j).length_lt
      linarith only [hsmall, ht.1, halpha]
    apply exists_inward_ray_crossing_selected_sphere T A U hU hA (index n)
      (hactive n) (hc n).1 (hc n).2 (hwhole n) hfinite E houtside
      (P j).length (P j).length_pos (P j).inward hcontinuous hlower
      (P j).inward_radius
    simpa only [MetricEndRay.inward, sub_zero] using hnStart j
  choose v hv hSphere using hcross
  let x : Fin (K + 1) → U := fun j => (P j).inward (v j)
  let s : Fin (K + 1) → ℝ := fun j => (P j).length - v j
  have hspos (j : Fin (K + 1)) : 0 < s j := sub_pos.mpr (hv j).2
  have hxradius (j : Fin (K + 1)) :
      dist (x j : UniformSpace.Completion U) E = s j :=
    (P j).inward_radius (v j) ⟨(hv j).1.le, (hv j).2⟩
  have hssmall (j : Fin (K + 1)) : s j < tau := by
    rw [← hxradius j]
    apply hdecay
    have hNpoint : (x j : M) ∈ N.carrier := N.central_sphere_subset (hSphere j)
    have hh := (A.mem_tail_iff_m28 true
      (lt_trans (by norm_num) (hc n).1) (hc n).2).mp (hwhole n hNpoint)
    exact hnD.trans hh.2
  have hscaleLower (j : Fin (K + 1)) : N.scale / 4 ≤ s j := by
    have h := (neck_completion_radius_lower N U hNU hfinite E houtside
      (x j) (hSphere j)).2.le
    rwa [hxradius j] at h
  obtain ⟨i, j, hij, hshort⟩ := hpacking M g N U
    (N.central_sphere_subset.trans hNU) x hSphere
  have hed : (intrinsicOpenMetric g U).edist (x i) (x j) =
      ENNReal.ofReal (dist (x i) (x j)) := by
    change edist (x i) (x j) = _
    exact edist_dist _ _
  rw [hed] at hshort
  have hdist : dist (x i) (x j) < eta * N.scale :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos heta N.scale_pos)).mp hshort
  have hsq : dist (x i) (x j) ^ 2 < (eta * N.scale) ^ 2 :=
    (sq_lt_sq₀ dist_nonneg (mul_pos heta N.scale_pos).le).mpr hdist
  have hproduct : N.scale ^ 2 / 16 ≤ s i * s j := by
    have h := mul_le_mul (hscaleLower i) (hscaleLower j)
      (div_nonneg N.scale_pos.le (by norm_num)) (hspos i).le
    nlinarith only [h]
  have hupper : chordDefect (fun u w => dist ((P i).point u) ((P j).point w))
      (s i) (s j) < d0 ^ 2 / 4 := by
    change (dist (x i) (x j) ^ 2 - (s i - s j) ^ 2) / (s i * s j) < d0 ^ 2 / 4
    apply (div_lt_iff₀ (mul_pos (hspos i) (hspos j))).mpr
    have hscaled := mul_le_mul_of_nonneg_left hproduct
      (div_nonneg (sq_nonneg d0) (by norm_num : (0 : ℝ) ≤ 4))
    dsimp only [eta] at hsq
    nlinarith only [hsq, hscaled, sq_nonneg (s i - s j)]
  have hlower := hrectangle (s i) ⟨hspos i, hssmall i⟩
    (s j) ⟨hspos j, hssmall j⟩ i j hij
  nlinarith only [hlower, hupper, sq_pos_of_pos hd0]

end PoincareConjecture.M28
