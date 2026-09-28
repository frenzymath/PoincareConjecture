import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.NeckBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.RadiusBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem crossing_frontier {K S : Set M} (hK : IsClosed K)
    (hS : IsPreconnected S) (hin : (S ∩ interior K).Nonempty)
    (hout : (S \ K).Nonempty) : (S ∩ frontier K).Nonempty := by
  by_contra h
  have hdisjoint : Disjoint S (frontier K) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
  have hcover : S ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · left
      by_contra hxi
      exact disjoint_left.mp hdisjoint hx
        (by rw [frontier, hK.closure_eq]; exact ⟨hxK, hxi⟩)
    · exact Or.inr hxK
  rcases hS.subset_or_subset isOpen_interior hK.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hleft | hright
  · obtain ⟨x, hx, hxK⟩ := hout
    exact hxK (interior_subset (hleft hx))
  · obtain ⟨x, hx, hxK⟩ := hin
    exact hright hx (interior_subset hxK)

omit [T2Space M] in

theorem calibrated_radius_lt_two_mul_of_scalar_in_ball (C : CapCertificate g)
    {p z : M} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hball : g.ball p r ⊆ C.carrier)
    (hcal : scalarCurvatureSupOn g C.connection (g.ball p r) = r⁻¹ ^ 2)
    (hz : z ∈ g.ball p r)
    (hscalar : (1 / 2 : ℝ) < s ^ 2 * C.connection.scalarCurvature z) :
    r < 2 * s := by
  have hbdd : BddAbove (range (fun x : g.ball p r => C.connection.scalarCurvature x)) := by
    apply C.scalar_range_bddAbove.mono
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, hball x.property⟩, rfl⟩
  have hle : C.connection.scalarCurvature z ≤ r⁻¹ ^ 2 := by
    rw [← hcal]
    exact le_csSup hbdd ⟨⟨z, hz⟩, rfl⟩
  have hmul := mul_lt_mul_of_pos_right
    (hscalar.trans_le (mul_le_mul_of_nonneg_left hle (sq_nonneg s))) (sq_pos_of_pos hr)
  have hcancel : s ^ 2 * r⁻¹ ^ 2 * r ^ 2 = s ^ 2 := by field_simp
  rw [hcancel] at hmul
  nlinarith

theorem calibrated_ball_truncated_clearance (C : CapCertificate g)
    (hinterior : interior (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) 0)) =
      C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) 0)
    (hfrontier : frontier (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) 0)) =
      range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, 0)))
    (hscalar : ∀ q : UnitTwoSphere,
      (1 / 2 : ℝ) < C.end_neck.scale ^ 2 *
        C.connection.scalarCurvature (C.end_neck.coordinate_map (q, 0)))
    {p y : M} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) 0)
    (hy : y ∉ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) ((2 / 5 : ℝ) * C.epsilon⁻¹))
    (hball : g.ball p r ⊆ C.carrier)
    (hcal : scalarCurvatureSupOn g C.connection (g.ball p r) = r⁻¹ ^ 2) :
    ENNReal.ofReal (r + (0.3 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) ≤ g.edist p y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) 0)
  have hK : IsClosed K := C.closed_core_compact.isClosed.union isClosed_closure
  have he := inv_pos.mpr C.epsilon_pos
  have hs := C.end_neck.scale_pos
  have hinv : 200 ≤ C.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ C.epsilon_pos).mpr (by linarith [C.epsilon_le_threshold])
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - C.end_neck.epsilon) := by
    rw [C.end_neck_epsilon]
    have hh := Real.sq_sqrt (show 0 ≤ 1 - C.epsilon by linarith [C.epsilon_le_threshold])
    nlinarith [Real.sqrt_nonneg (1 - C.epsilon), C.epsilon_le_threshold]
  have hyK : y ∉ K := by
    intro hyK
    rcases hyK with hycore | hyclosure
    · exact hy (Or.inl hycore)
    · by_cases hyN : y ∈ C.end_neck.carrier
      · have hheight := (C.truncated_closed_core_height_iff (by linarith : -C.epsilon⁻¹ < 0)
          hyN).mp (Or.inr hyclosure)
        have hlo := (C.end_neck.coordinate_inverse_mem y hyN).2.1
        rw [C.end_neck_epsilon] at hlo
        exact hy (Or.inr ⟨hyN, hlo, hheight.trans_lt (by positivity)⟩)
      · have hycap : y ∈ C.carrier := by
          have hboundary := hfrontier
          have hyinterior : y ∈ interior K := by
            by_contra hnot
            have hyf : y ∈ frontier K := by
              rw [frontier, hK.closure_eq]
              exact ⟨Or.inr hyclosure, hnot⟩
            rw [hboundary] at hyf
            obtain ⟨q, rfl⟩ := hyf
            exact hyN (C.end_neck.coordinate_map_mem
              ⟨mem_univ _, by rw [C.end_neck_epsilon]; exact ⟨by linarith, he⟩⟩)
          rw [hinterior] at hyinterior
          exact hyinterior.elim (fun h => C.closed_core_subset_carrier h)
            (fun h => C.end_neck_subset h.1)
        exact hy (Or.inl (C.closed_core_eq_complement_end.symm ▸ ⟨hycap, hyN⟩))
  by_contra h
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt
    (show Manifold.riemannianEDist (𝓡 3) p y <
      ENNReal.ofReal (r + (0.3 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) from lt_of_not_ge h)
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := crossing_frontier hK hconn
    ⟨p, ⟨0, by simp, h0⟩, hinterior.symm ▸ hp⟩
    ⟨y, ⟨1, by simp, h1⟩, hyK⟩
  rw [hfrontier] at hz
  obtain ⟨q, hq⟩ := hz
  have hzcollar : γ t ∈ C.end_neck.closedCollar 0 :=
    ⟨(q, 0), ⟨mem_univ _, by simp⟩, hq⟩
  have hycollar : y ∉ C.end_neck.closedCollar ((0.39 : ℝ) * C.epsilon⁻¹) := by
    intro hyc
    have hrad : (0.39 : ℝ) * C.epsilon⁻¹ < C.end_neck.epsilon⁻¹ := by
      rw [C.end_neck_epsilon]; linarith
    have hh := (C.end_neck.mem_coordinate_slab_iff (neg_lt_neg hrad) hrad).mp hyc
    exact hy (Or.inr ⟨hh.1, by linarith [hh.2.1], by linarith [hh.2.2]⟩)
  have hdist := C.end_neck.edist_lower_between_closedCollars (by norm_num : (0 : ℝ) ≤ 0)
    (by positivity : 0 < (0.39 : ℝ) * C.epsilon⁻¹)
    (by rw [C.end_neck_epsilon]; linarith : (0.39 : ℝ) * C.epsilon⁻¹ < C.end_neck.epsilon⁻¹)
    hzcollar hycollar
  have hnumeric : (0.38 : ℝ) * C.end_neck.scale * C.epsilon⁻¹ ≤
      C.end_neck.scale * Real.sqrt (1 - C.end_neck.epsilon) *
        ((0.39 : ℝ) * C.epsilon⁻¹ - 0) := by
    have hm := mul_le_mul_of_nonneg_right hroot (mul_nonneg hs.le he.le)
    nlinarith
  have hright : ENNReal.ofReal ((0.38 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) ≤
      Manifold.pathELength (𝓡 3) γ t 1 :=
    ((ENNReal.ofReal_le_ofReal hnumeric).trans hdist).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2)
  by_cases hzball : γ t ∈ g.ball p r
  · have hsmall := C.calibrated_radius_lt_two_mul_of_scalar_in_ball hr hs hball hcal hzball
      (hq ▸ hscalar q)
    have hnum : r + (0.3 : ℝ) * C.end_neck.scale * C.epsilon⁻¹ ≤
        (0.38 : ℝ) * C.end_neck.scale * C.epsilon⁻¹ := by
      have hm := mul_le_mul_of_nonneg_left hinv hs.le
      nlinarith
    exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal hnum).trans
      (hright.trans (Manifold.pathELength_mono ht.1 le_rfl)))) hlength
  · have hleft : ENNReal.ofReal r ≤ Manifold.pathELength (𝓡 3) γ 0 t :=
      (le_of_not_gt hzball).trans (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_right ht.2)) h0 rfl ht.1)
    have hbuffer : ENNReal.ofReal ((0.3 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) ≤
        Manifold.pathELength (𝓡 3) γ t 1 :=
      (ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hs he])).trans hright
    have htotal := (add_le_add hleft hbuffer).trans_eq (Manifold.pathELength_add ht.1 ht.2)
    rw [← ENNReal.ofReal_add hr.le (by positivity)] at htotal
    exact (not_lt_of_ge htotal) hlength

theorem exists_calibrated_ball_truncated_clearance_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ p ∈ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) 0,
        ∀ r : ℝ, 0 < r → g.ball p r ⊆ C.carrier →
          scalarCurvatureSupOn g C.connection (g.ball p r) = r⁻¹ ^ 2 →
        ∀ y ∉ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) ((2 / 5 : ℝ) * C.epsilon⁻¹),
          ENNReal.ofReal (r + (0.3 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) ≤ g.edist p y := by
  obtain ⟨ε₁, hε₁, hsmall, hdomain⟩ := exists_truncated_core_domain_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hscalar⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε p hp r hr hball hcal y hy
  have he := inv_pos.mpr C.epsilon_pos
  obtain ⟨_, _, hi, hf, _⟩ := hdomain C (hε.trans (min_le_left _ _)) 0
    ⟨by linarith, he⟩
  apply C.calibrated_ball_truncated_clearance hi hf ?_ hr hp hy hball hcal
  intro q
  have hh := (hscalar C.end_neck C.connection
    (C.end_neck_epsilon.trans_le (hε.trans (min_le_right _ _))) q
    (by rw [C.end_neck_epsilon]; exact ⟨by linarith, he⟩)).1
  linarith [(abs_lt.mp hh).1]

noncomputable def truncatedBallClearanceThreshold : ℝ :=
  Classical.choose exists_calibrated_ball_truncated_clearance_threshold.{u}

theorem truncatedBallClearanceThreshold_pos : 0 < truncatedBallClearanceThreshold.{u} :=
  (Classical.choose_spec exists_calibrated_ball_truncated_clearance_threshold.{u}).1

theorem truncatedBallClearanceThreshold_le : truncatedBallClearanceThreshold.{u} ≤ 1 / 1000 :=
  (Classical.choose_spec exists_calibrated_ball_truncated_clearance_threshold.{u}).2.1

theorem calibrated_ball_truncated_clearance_of_small (C : CapCertificate g)
    (hε : C.epsilon ≤ truncatedBallClearanceThreshold.{u})
    {p y : M} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) 0)
    (hy : y ∉ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) ((2 / 5 : ℝ) * C.epsilon⁻¹))
    (hball : g.ball p r ⊆ C.carrier)
    (hcal : scalarCurvatureSupOn g C.connection (g.ball p r) = r⁻¹ ^ 2) :
    ENNReal.ofReal (r + (0.3 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) ≤ g.edist p y :=
  (Classical.choose_spec exists_calibrated_ball_truncated_clearance_threshold.{u}).2.2
    C hε p hp r hr hball hcal y hy

end PoincareConjecture.CapCertificate
