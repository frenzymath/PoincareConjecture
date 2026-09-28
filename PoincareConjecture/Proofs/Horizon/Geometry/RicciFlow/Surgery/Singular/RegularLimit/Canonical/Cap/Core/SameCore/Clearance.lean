import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Clearance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem edist_lower_of_centered_slab (N : EpsilonNeck g)
    {a w : ℝ} (hw : 0 < w) (ha : -N.epsilon⁻¹ < a - w)
    (hb : a + w < N.epsilon⁻¹) {p y : M}
    (hp : p ∈ N.carrier) (hpa : (N.coordinate_inverse p).2 = a)
    (hy : y ∉ N.coordinate_map '' (univ ×ˢ Icc (a - w) (a + w))) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * w) ≤ g.edist p y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_contra h
  obtain ⟨γ, h0, h1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt
      (show Manifold.riemannianEDist (𝓡 3) p y <
        ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * w) from lt_of_not_ge h)
      (by norm_num : (0 : ℝ) < 1)
  have hstart : γ 0 ∈ N.region (a - w) (a + w) := by
    rw [h0]
    exact ⟨hp, by rw [hpa]; constructor <;> linarith⟩
  obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
    (by norm_num : (0 : ℝ) ≤ 1) ha hb hγ.continuous.continuousOn hstart
    (h1.symm ▸ hy)
  have hvalue : |(N.coordinate_inverse (γ t)).2 -
      (N.coordinate_inverse (γ 0)).2| = w := by
    rw [h0, hpa]
    rcases hboundary with hneg | hpos
    · rw [hneg, sub_sub_cancel_left, abs_neg, abs_of_pos hw]
    · rw [hpos, add_sub_cancel_left, abs_of_pos hw]
  have hax := N.axial_displacement_le_pathELength ht.1.le hγ hcarrier
  rw [hvalue] at hax
  exact (not_lt_of_ge (hax.trans (Manifold.pathELength_mono le_rfl ht.2))) hlength

end PoincareConjecture.EpsilonNeck

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

theorem calibrated_ball_same_core_clearance (C : CapCertificate g)
    (hinterior : interior (C.closed_core ∪
      closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ + 20))) =
        C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ + 20))
    (hfrontier : frontier (C.closed_core ∪
      closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ + 20))) =
        range (fun q : UnitTwoSphere =>
          C.end_neck.coordinate_map (q, -C.epsilon⁻¹ + 20)))
    (hscalar : ∀ q : UnitTwoSphere, (1 / 2 : ℝ) < C.end_neck.scale ^ 2 *
      C.connection.scalarCurvature (C.end_neck.coordinate_map (q, -C.epsilon⁻¹ + 20)))
    {p y : M} {r b : ℝ} (hr : 0 < r) (hp : p ∈ C.closed_core)
    (hb : -C.epsilon⁻¹ + 40 ≤ b)
    (hy : y ∉ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b)
    (hball : g.ball p r ⊆ C.carrier)
    (hcal : scalarCurvatureSupOn g C.connection (g.ball p r) = r⁻¹ ^ 2) :
    ENNReal.ofReal (r + C.end_neck.scale) ≤ g.edist p y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let a : ℝ := -C.epsilon⁻¹ + 20
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)
  have hK : IsClosed K := C.closed_core_compact.isClosed.union isClosed_closure
  have hinv : 200 ≤ C.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ C.epsilon_pos).mpr (by linarith [C.epsilon_le_threshold])
  have ha : -C.epsilon⁻¹ < a := by dsimp [a]; linarith
  have haN : a < C.epsilon⁻¹ := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - C.end_neck.epsilon) := by
    rw [C.end_neck_epsilon]
    have hh := Real.sq_sqrt (show 0 ≤ 1 - C.epsilon by linarith [C.epsilon_le_threshold])
    nlinarith [Real.sqrt_nonneg (1 - C.epsilon), C.epsilon_le_threshold]
  have hyK : y ∉ K := by
    rintro (hycore | hyclosure)
    · exact hy (Or.inl hycore)
    · by_cases hyN : y ∈ C.end_neck.carrier
      · have hheight := (C.truncated_closed_core_height_iff ha hyN).mp (Or.inr hyclosure)
        have hlo := (C.end_neck.coordinate_inverse_mem y hyN).2.1
        rw [C.end_neck_epsilon] at hlo
        exact hy (Or.inr ⟨hyN, hlo, hheight.trans_lt hab⟩)
      · have hycap : y ∈ C.carrier := by
          have hyinterior : y ∈ interior K := by
            by_contra hnot
            have hyf : y ∈ frontier K := by
              rw [frontier, hK.closure_eq]
              exact ⟨Or.inr hyclosure, hnot⟩
            rw [hfrontier] at hyf
            obtain ⟨q, rfl⟩ := hyf
            exact hyN (C.end_neck.coordinate_map_mem
              ⟨mem_univ _, by rw [C.end_neck_epsilon]; exact ⟨ha, haN⟩⟩)
          rw [hinterior] at hyinterior
          exact hyinterior.elim (fun h => C.closed_core_subset_carrier h)
            (fun h => C.end_neck_subset h.1)
        exact hy (Or.inl (C.closed_core_eq_complement_end.symm ▸ ⟨hycap, hyN⟩))
  by_contra h
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt
    (show Manifold.riemannianEDist (𝓡 3) p y <
      ENNReal.ofReal (r + C.end_neck.scale) from lt_of_not_ge h)
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := crossing_frontier hK hconn
    ⟨p, ⟨0, by simp, h0⟩, hinterior.symm ▸ Or.inl hp⟩
    ⟨y, ⟨1, by simp, h1⟩, hyK⟩
  rw [hfrontier] at hz
  obtain ⟨q, hq⟩ := hz
  have hzdom : (q, a) ∈ C.end_neck.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    simpa only [C.end_neck_epsilon, mem_Ioo] using And.intro ha haN
  have hzN : γ t ∈ C.end_neck.carrier := hq ▸ C.end_neck.coordinate_map_mem hzdom
  have hzheight : (C.end_neck.coordinate_inverse (γ t)).2 = a := by
    rw [← hq, C.end_neck.coordinate_inverse_coordinate_map hzdom]
  have hleft : -C.end_neck.epsilon⁻¹ < a - 10 := by
    rw [C.end_neck_epsilon]; dsimp [a]; linarith
  have hright : a + 10 < C.end_neck.epsilon⁻¹ := by
    rw [C.end_neck_epsilon]; dsimp [a]; linarith
  have hycollar : y ∉ C.end_neck.coordinate_map '' (univ ×ˢ Icc (a - 10) (a + 10)) := by
    intro hymem
    have hh := (C.end_neck.mem_coordinate_slab_iff hleft hright).mp hymem
    exact hy (Or.inr ⟨hh.1, by dsimp [a] at hh; linarith [hh.2.1],
      by dsimp [a] at hh; linarith [hh.2.2]⟩)
  have hdist := C.end_neck.edist_lower_of_centered_slab (by norm_num : (0 : ℝ) < 10)
    hleft hright hzN hzheight hycollar
  have hnumeric : 9 * C.end_neck.scale ≤
      C.end_neck.scale * Real.sqrt (1 - C.end_neck.epsilon) * 10 := by
    have hm := mul_le_mul_of_nonneg_left hroot C.end_neck.scale_pos.le
    nlinarith [C.end_neck.scale_pos]
  have hsegment : ENNReal.ofReal (9 * C.end_neck.scale) ≤
      Manifold.pathELength (𝓡 3) γ t 1 :=
    ((ENNReal.ofReal_le_ofReal hnumeric).trans hdist).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2)
  by_cases hzball : γ t ∈ g.ball p r
  · have hsmall := C.calibrated_radius_lt_two_mul_of_scalar_in_ball hr
      C.end_neck.scale_pos hball hcal hzball (hq ▸ hscalar q)
    have hnum : r + C.end_neck.scale ≤ 9 * C.end_neck.scale := by
      linarith [C.end_neck.scale_pos]
    exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal hnum).trans
      (hsegment.trans (Manifold.pathELength_mono ht.1 le_rfl)))) hlength
  · have hleft : ENNReal.ofReal r ≤ Manifold.pathELength (𝓡 3) γ 0 t :=
      (le_of_not_gt hzball).trans (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_right ht.2)) h0 rfl ht.1)
    have hbuffer : ENNReal.ofReal C.end_neck.scale ≤
        Manifold.pathELength (𝓡 3) γ t 1 :=
      (ENNReal.ofReal_le_ofReal (by linarith [C.end_neck.scale_pos])).trans hsegment
    have htotal := (add_le_add hleft hbuffer).trans_eq (Manifold.pathELength_add ht.1 ht.2)
    rw [← ENNReal.ofReal_add hr.le C.end_neck.scale_pos.le] at htotal
    exact (not_lt_of_ge htotal) hlength

theorem exists_calibrated_ball_same_core_clearance_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ p ∈ C.closed_core, ∀ r : ℝ, 0 < r → g.ball p r ⊆ C.carrier →
          scalarCurvatureSupOn g C.connection (g.ball p r) = r⁻¹ ^ 2 →
        ∀ b : ℝ, -C.epsilon⁻¹ + 40 ≤ b →
        ∀ y ∉ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b,
          ENNReal.ofReal (r + C.end_neck.scale) ≤ g.edist p y := by
  obtain ⟨ε₁, hε₁, hsmall, hdomain⟩ := exists_truncated_core_domain_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hscalar⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε p hp r hr hball hcal b hb y hy
  have hinv : 200 ≤ C.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ C.epsilon_pos).mpr (by linarith [C.epsilon_le_threshold])
  have ha : -C.epsilon⁻¹ + 20 ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
    constructor <;> linarith
  obtain ⟨_, _, hi, hf, _⟩ := hdomain C (hε.trans (min_le_left _ _)) _ ha
  apply C.calibrated_ball_same_core_clearance hi hf ?_ hr hp hb hy hball hcal
  intro q
  have hh := (hscalar C.end_neck C.connection
    (C.end_neck_epsilon.trans_le (hε.trans (min_le_right _ _))) q
    (by simpa only [C.end_neck_epsilon] using ha)).1
  linarith [(abs_lt.mp hh).1]

noncomputable def sameCoreBallClearanceThreshold : ℝ :=
  Classical.choose exists_calibrated_ball_same_core_clearance_threshold.{u}

theorem sameCoreBallClearanceThreshold_pos : 0 < sameCoreBallClearanceThreshold.{u} :=
  (Classical.choose_spec exists_calibrated_ball_same_core_clearance_threshold.{u}).1

theorem sameCoreBallClearanceThreshold_le : sameCoreBallClearanceThreshold.{u} ≤ 1 / 1000 :=
  (Classical.choose_spec exists_calibrated_ball_same_core_clearance_threshold.{u}).2.1

theorem calibrated_ball_same_core_clearance_of_small (C : CapCertificate g)
    (hε : C.epsilon ≤ sameCoreBallClearanceThreshold.{u})
    {p y : M} {r b : ℝ} (hr : 0 < r) (hp : p ∈ C.closed_core)
    (hb : -C.epsilon⁻¹ + 40 ≤ b)
    (hy : y ∉ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b)
    (hball : g.ball p r ⊆ C.carrier)
    (hcal : scalarCurvatureSupOn g C.connection (g.ball p r) = r⁻¹ ^ 2) :
    ENNReal.ofReal (r + C.end_neck.scale) ≤ g.edist p y :=
  (Classical.choose_spec exists_calibrated_ball_same_core_clearance_threshold.{u}).2.2
    C hε p hp r hr hball hcal b hb y hy

end PoincareConjecture.CapCertificate
