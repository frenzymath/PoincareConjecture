import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPairCoreCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierOrientationPair
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFrontierBuffers

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck

private theorem core_point_of_neck_choice
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {Q W : EpsilonNeck g}
    (hchoice : Q = W ∨ Q = W.reversed) {x : M}
    (hx : x ∈ Q.region (-(3 * Q.epsilon⁻¹ / 4)) (3 * Q.epsilon⁻¹ / 4)) :
    x ∈ W.carrier ∧ |(W.coordinate_inverse x).2| ≤ 3 * W.epsilon⁻¹ / 4 := by
  have h : x ∈ Q.carrier ∧
      |(Q.coordinate_inverse x).2| ≤ 3 * Q.epsilon⁻¹ / 4 :=
    ⟨hx.1, abs_le.mpr ⟨hx.2.1.le, hx.2.2.le⟩⟩
  rcases hchoice with hQ | hQ <;>
    simpa only [hQ, reversed_carrier, reversed_coordinate_inverse, reversed_epsilon,
      abs_neg] using h

theorem exists_source_neck_core_buffer_accuracy (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N ∈ S.cover.necks, ∀ x ∈ N.carrier,
          ∃ W : EpsilonNeck (E.flow.metric E.time), ∃ t ∈ Ioo (0 : ℝ) 1,
            W.epsilon = epsilon ∧ S.path t = W.center ∧
              W.carrier ⊆ S.source_region.carrier ∧
              S.path 0 ∉ W.carrier ∧ S.path 1 ∉ W.carrier ∧
              x ∈ W.carrier ∧
              |(W.coordinate_inverse x).2| ≤ 3 * W.epsilon⁻¹ / 4 := by
  obtain ⟨epsilonB, hBpos, hBsmall, hbuffers⟩ := exists_source_frontier_buffers_accuracy P
  obtain ⟨epsilonO, hOpos, _, horient⟩ :=
    exists_neck_frontier_orientation_pair_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hregion⟩ := exists_source_neck_region_accuracy.{u}
  obtain ⟨epsilonE, hEpos, _, hendpoints⟩ :=
    exists_source_neck_endpoint_exclusion_accuracy.{u}
  let epsilon₀ := min epsilonB (min epsilonO (min epsilonR epsilonE))
  refine ⟨epsilon₀, lt_min hBpos (lt_min hOpos (lt_min hRpos hEpos)),
    (min_le_left _ _).trans hBsmall, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall N hN x hx
  have hεB : epsilon ≤ epsilonB := hsmall.trans (min_le_left _ _)
  have hεO : epsilon ≤ epsilonO :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεR : epsilon ≤ epsilonR :=
    hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεE : epsilon ≤ epsilonE :=
    hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hε : epsilon ≤ 1 / 1000 := hεB.trans hBsmall
  have hNε : N.epsilon = epsilon :=
    (S.cover.neck_epsilon N hN).trans S.cover_epsilon
  have hNU : N.carrier ⊆ S.source_region.carrier :=
    fun y hy => (hregion E S hQ hεR).2.1 ⟨N, hN, hy⟩
  obtain ⟨hzero, hone⟩ := hendpoints E S hQ hεE
  have hNzero : S.path 0 ∉ N.carrier := fun h => hzero ⟨N, hN, h⟩
  have hNone : S.path 1 ∉ N.carrier := fun h => hone ⟨N, hN, h⟩
  have hcenter := S.center_mem_cover N hN
  rw [S.cover_set] at hcenter
  obtain ⟨t, ht, hcenter⟩ := hcenter
  have ht0 : 0 < t := S.lower_pos.trans_le ht.1
  have ht1 : t < 1 := ht.2.trans_lt S.upper_lt_one
  by_cases hcore : |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4
  · exact ⟨N, t, ⟨ht0, ht1⟩, hNε, hcenter, hNU, hNzero, hNone, hx, hcore⟩
  obtain ⟨u, v, hu0, hut, htv, hv1, hufront, hvfront, hleft, hright, hfresh⟩ :=
    hbuffers E S hQ hεB N hN t ht hcenter
  obtain ⟨Jminus, hJminus, hminusU, hminus0, hminus1, _⟩ :=
    hfresh u (Or.inl rfl)
  obtain ⟨Jplus, hJplus, hplusU, hplus0, hplus1, _⟩ :=
    hfresh v (Or.inr rfl)
  let Pminus := strongNeck_top Jminus S.epsilon_lt_half
  let Pplus := strongNeck_top Jplus S.epsilon_lt_half
  have hminusε : Pminus.epsilon = N.epsilon := hNε.symm
  have hplusε : Pplus.epsilon = N.epsilon := hNε.symm
  obtain ⟨Nplus, Qplus, Nminus, Qminus, hplus, hminus, Hplus, Hminus, hopposite⟩ :=
    horient N Pminus Pplus (by rw [hNε]; exact hεO) hminusε hplusε hNU
      hu0.le hut htv hv1.le S.path_smooth S.source_region.path_mem
      S.source_region.finite_length S.source_region.minimizing hcenter
      hJminus.symm hJplus.symm hleft hright
      (by simpa only [Pminus, strongNeck_top, hJminus] using hufront)
      (by simpa only [Pplus, strongNeck_top, hJplus] using hvfront)
  have hplusε' : Nplus.epsilon = epsilon := by
    rcases hplus with h | h <;> simpa only [h, reversed_epsilon] using hNε
  have hminusε' : Nminus.epsilon = epsilon := by
    rcases hminus with h | h <;> simpa only [h, reversed_epsilon] using hNε
  have hxplus : x ∈ Nplus.carrier := by
    rcases hplus with h | h <;> simpa only [h, reversed_carrier] using hx
  have hlarge : 3 * Nplus.epsilon⁻¹ / 4 < |(Nplus.coordinate_inverse x).2| := by
    have h := lt_of_not_ge hcore
    rcases hplus with hp | hp <;>
      simpa only [hp, reversed_epsilon, reversed_coordinate_inverse, abs_neg] using h
  by_cases hpositive : Nplus.epsilon⁻¹ / 2 < (Nplus.coordinate_inverse x).2
  · have hxquarter : x ∈ Nplus.region (Nplus.epsilon⁻¹ / 2) Nplus.epsilon⁻¹ :=
      ⟨hxplus, hpositive, (Nplus.coordinate_inverse_mem x hxplus).2.2⟩
    have hxQ := Hplus.forward_core (by rw [hplusε']; exact hε) hxquarter
    obtain ⟨hxP, hcoreP⟩ := core_point_of_neck_choice Hplus.choice hxQ
    exact ⟨Pplus, v, ⟨ht0.trans htv, hv1⟩, rfl, hJplus.symm,
      hplusU.trans S.source_region.cover_subset, hplus0, hplus1, hxP, hcoreP⟩
  · have hheight : (Nplus.coordinate_inverse x).2 < -Nplus.epsilon⁻¹ / 2 := by
      have hA : 0 < Nplus.epsilon⁻¹ := inv_pos.mpr Nplus.epsilon_pos
      have hle := le_of_not_gt hpositive
      rcases le_total 0 (Nplus.coordinate_inverse x).2 with hnonneg | hnonpos
      · rw [abs_of_nonneg hnonneg] at hlarge
        linarith only [hlarge, hle, hA]
      · rw [abs_of_nonpos hnonpos] at hlarge
        linarith only [hlarge, hA]
    have hxminus : x ∈ Nminus.carrier := by
      simpa only [hopposite, reversed_carrier] using hxplus
    have hxquarter : x ∈ Nminus.region (Nminus.epsilon⁻¹ / 2) Nminus.epsilon⁻¹ := by
      refine ⟨hxminus, ?_, (Nminus.coordinate_inverse_mem x hxminus).2.2⟩
      simp only [hopposite, reversed_epsilon, reversed_coordinate_inverse]
      linarith only [hheight]
    have hxQ := Hminus.forward_core (by rw [hminusε']; exact hε) hxquarter
    obtain ⟨hxP, hcoreP⟩ := core_point_of_neck_choice Hminus.choice hxQ
    exact ⟨Pminus, u, ⟨hu0, hut.trans ht1⟩, rfl, hJminus.symm,
      hminusU.trans S.source_region.cover_subset, hminus0, hminus1, hxP, hcoreP⟩

end PoincareConjecture.M28
