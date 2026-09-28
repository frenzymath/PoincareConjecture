import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedInteriorWall
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereCrossings
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricSpace
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Isotopy.Composition
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.Order.Compact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {X : Set M}




theorem exists_completion_radius_threshold_for_cylinder_height
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ E : UniformSpace.Completion U,
      E ∉ range ((↑) : U → UniformSpace.Completion U) →
      ∀ c : ℝ, c < 1 → ∃ eta : ℝ, 0 < eta ∧
        ∀ x : U, (3 / 4 : ℝ) ≤ (A.inverse x).2 →
          dist (x : UniformSpace.Completion U) E < eta → c < (A.inverse x).2 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E houtside c hc
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  have hr : Continuous r :=
    (UniformSpace.Completion.continuous_coe U).dist continuous_const
  have hrpos (x : U) : 0 < r x :=
    dist_pos.mpr fun hx => houtside ⟨x, hx⟩
  let d : ℝ := max c (3 / 4 : ℝ)
  have hd1 : d < 1 := max_lt hc (by norm_num)
  have hKU : A.compactSlab (3 / 4) d ⊆ (U : Set M) := by
    intro x hx
    have hh := (A.mem_compactSlab_iff (by norm_num) hd1).mp hx
    rw [hU]
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hh.1, (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans_le hh.2.1⟩
  let K : Set U := (Subtype.val : U → M) ⁻¹' A.compactSlab (3 / 4) d
  have hK : IsCompact K :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (A.isCompact_compactSlab (by norm_num) hd1)
      (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hmem (x : U) (hlo : (3 / 4 : ℝ) ≤ (A.inverse x).2)
      (hhi : (A.inverse x).2 ≤ c) : x ∈ K :=
    (A.mem_compactSlab_iff (by norm_num) hd1).mpr
      ⟨hUV x.property, hlo, hhi.trans (le_max_left _ _)⟩
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hlo _hradius
    apply lt_of_not_ge
    intro hhi
    have hx := hmem x hlo hhi
    simp only [hEmpty, mem_empty_iff_false] at hx
  · obtain ⟨z, _hz, hmin⟩ := hK.exists_isMinOn hNonempty hr.continuousOn
    refine ⟨r z, hrpos z, ?_⟩
    intro x hlo hradius
    apply lt_of_not_ge
    intro hhi
    exact (not_le_of_gt hradius) (hmin (hmem x hlo hhi))




theorem cylinder_height_ge_threeQuarter_of_radius_barrier
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ),
      (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
      (∀ p q : U, 0 < f p → 0 < f q →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (mu s) (mu t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
      ∀ x : U, dist (x : UniformSpace.Completion U) E < alpha →
        (3 / 4 : ℝ) ≤ (A.inverse x).2 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha hbarrier hsegments x hx
  obtain ⟨mu, h0, _h1, _hcontinuous, hlower, _hmetric⟩ :=
    hsegments x x (hbarrier x hx) (hbarrier x hx)
  simpa only [h0] using hlower 0





theorem exists_inward_ray_crossing_selected_sphere
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (i : ℤ) (hi : i ∈ T.chain.shape.active)
    {c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (hN : (T.chain.neck i).carrier ⊆ A.tail true c)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ E : UniformSpace.Completion U,
      E ∉ range ((↑) : U → UniformSpace.Completion U) →
      ∀ (a : ℝ), 0 < a → ∀ gamma : ℝ → U,
        ContinuousOn gamma (Ico (0 : ℝ) a) →
        (∀ t ∈ Ico (0 : ℝ) a, (3 / 4 : ℝ) ≤ (A.inverse (gamma t)).2) →
        (∀ t ∈ Ico (0 : ℝ) a,
          dist (gamma t : UniformSpace.Completion U) E = a - t) →
        (A.inverse (gamma 0)).2 < c →
        ∃ t ∈ Ioo (0 : ℝ) a, (gamma t : M) ∈ (T.chain.neck i).central_sphere := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E houtside a ha gamma hgamma hlower hradius hstart
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  let V : TopologicalSpace.Opens M := ⟨T.carrier, T.carrier_open⟩
  obtain ⟨phi, _a0, b0, _ha0, _ha0half, hb0half, hb01, hzero, hread, hside⟩ :=
    exists_fixed_positive_side_above_cylinder_level (V := V) A (T.chain.neck i)
      hc hc1 hN ((T.central_sphere_isotopy i hi).trans hA.symm)
  let fN : M → ℝ := ambientCylinderSignedHeight phi
  have hnegative : fN (gamma 0) < 0 := by
    apply lt_of_not_ge
    intro hpos
    exact (not_le_of_gt hstart) (hside (gamma 0) (hUV (gamma 0).property) hpos)
  obtain ⟨eta, heta, hhigh⟩ :=
    exists_completion_radius_threshold_for_cylinder_height T A U hU hfinite
      E houtside b0 hb01
  let s : ℝ := min (a / 2) (eta / 2)
  have hs : 0 < s := lt_min (half_pos ha) (half_pos heta)
  have hsa : s < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  have hseta : s < eta := (min_le_right _ _).trans_lt (half_lt_self heta)
  let b : ℝ := a - s
  have hb0 : 0 < b := sub_pos.mpr hsa
  have hba : b < a := sub_lt_self a hs
  have hbmem : b ∈ Ico (0 : ℝ) a := ⟨hb0.le, hba⟩
  have hsmall : dist (gamma b : UniformSpace.Completion U) E < eta := by
    rw [hradius b hbmem]
    dsimp only [b]
    linarith only [hseta]
  have hbheight := hhigh (gamma b) (hlower b hbmem) hsmall
  have hpositive : 0 < fN (gamma b) := by
    rw [show fN (gamma b) = (A.inverse (gamma b)).2 - 1 / 2 from
      hread (gamma b) (hUV (gamma b).property) (Or.inr hbheight)]
    exact sub_pos.mpr (hb0half.trans hbheight)
  have hsub : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) a :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt hba⟩
  obtain ⟨t, ht, hS⟩ := exists_sphere_crossing_of_signed_height
    (continuousOn_ambientCylinderSignedHeight phi) hzero hb0.le
    (continuous_subtype_val.comp_continuousOn (hgamma.mono hsub))
    (fun t (_ : t ∈ Icc (0 : ℝ) b) => hUV (gamma t).property)
    hnegative hpositive
  exact ⟨t, ⟨ht.1, ht.2.trans hba⟩, hS⟩

end PoincareConjecture.M28
