import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.TruncatedDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.EndFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceUpper
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.FrontierScale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

private theorem pathELength_lower_of_cross_between_exterior_points
    (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1))
    (hstart : γ 0 ∉ N.carrier) (hend : γ 1 ∉ N.carrier)
    {t : ℝ} (ht : t ∈ Icc 0 1) (hcross : γ t ∈ N.central_sphere) :
    ENNReal.ofReal ((1.9 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := N.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hi.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hdiam := N.edist_central_sphere_le_two_pi_mul_scale
    N.center_on_central_sphere hcross
  have hleft : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      ENNReal.ofReal ((2 * Real.pi) * N.scale) + g.pathELength γ 0 t := by
    apply (N.balanced_edist_lower_of_not_mem_carrier hε hstart).trans
    calc
      _ ≤ g.edist N.center (γ t) + g.edist (γ t) (γ 0) :=
        Manifold.riemannianEDist_triangle
      _ = g.edist N.center (γ t) + g.edist (γ 0) (γ t) := by
        rw [show g.edist (γ t) (γ 0) = g.edist (γ 0) (γ t) from
          Manifold.riemannianEDist_comm]
      _ ≤ _ := add_le_add hdiam (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_right ht.2)) rfl rfl ht.1)
  have hright : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      ENNReal.ofReal ((2 * Real.pi) * N.scale) + g.pathELength γ t 1 :=
    (N.balanced_edist_lower_of_not_mem_carrier hε hend).trans
      (Manifold.riemannianEDist_triangle.trans (add_le_add hdiam
        (Manifold.riemannianEDist_le_pathELength
          (hγ.mono (Icc_subset_Icc_left ht.1)) rfl rfl ht.2)))
  have hsum := add_le_add hleft hright
  have hadd : g.pathELength γ 0 t + g.pathELength γ t 1 = g.pathELength γ 0 1 :=
    Manifold.pathELength_add ht.1 ht.2
  rw [add_add_add_comm, hadd] at hsum
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hsum
  by_contra hnot
  have hlt := ENNReal.add_lt_add_left
    (ENNReal.ofReal_ne_top (r := (2 * Real.pi) * N.scale + (2 * Real.pi) * N.scale))
    (lt_of_not_ge hnot)
  have hstrict := hsum.trans_lt hlt
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hstrict
  have hnum := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hstrict
  have hpi := mul_le_mul_of_nonneg_right Real.pi_le_four hs.le
  have hlen := mul_le_mul_of_nonneg_left hinv hs.le
  nlinarith

theorem exists_closed_core_end_thickness_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ x ∈ C.closed_core, ∀ y ∉ C.carrier,
          ENNReal.ofReal ((1.9 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) ≤
            g.edist x y := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε x hx y hy
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi := inv_pos.mpr C.epsilon_pos
  obtain ⟨hK, hKsub, -, hfront, -, hcore⟩ :=
    htrunc C hε 0 ⟨neg_neg_of_pos hi, hi⟩
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) 0)
  have hKclosed : IsClosed K := hK.isClosed
  have hfront' : frontier K = C.end_neck.central_sphere := by
    exact hfront.trans C.end_neck.centralSphere_range
  by_contra hnot
  obtain ⟨γ, h0, h1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (lt_of_not_ge hnot)
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  have hcross : (γ '' Icc (0 : ℝ) 1 ∩ frontier K).Nonempty := by
    by_contra hn
    have hdisj : Disjoint (γ '' Icc (0 : ℝ) 1) (frontier K) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    have hcover : γ '' Icc (0 : ℝ) 1 ⊆ interior K ∪ Kᶜ := by
      intro z hz
      by_cases hzK : z ∈ K
      · left
        by_contra hzint
        exact disjoint_left.mp hdisj hz
          (show z ∈ frontier K from ⟨subset_closure hzK, hzint⟩)
      · exact Or.inr hzK
    rcases hconn.subset_or_subset isOpen_interior hKclosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
    · exact hy (hKsub (interior_subset (hin ⟨1, by simp, h1⟩)))
    · exact hout ⟨0, by simp, h0⟩ (interior_subset (hcore hx))
  obtain ⟨z, ⟨t, ht, rfl⟩, htfront⟩ := hcross
  have hlower := pathELength_lower_of_cross_between_exterior_points C.end_neck
    (C.end_neck_epsilon.trans_le (hε.trans hsmall)) hγ
    (h0 ▸ (fun h => disjoint_left.mp C.disjoint_closed_core_end hx h))
    (h1 ▸ (fun h => hy (C.end_neck_subset h))) ht (hfront' ▸ htfront)
  rw [C.end_neck_epsilon] at hlower
  exact not_lt_of_ge hlower hlength

theorem exists_exterior_center_neck_disjoint_closed_core_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g) (P : EpsilonNeck g), C.epsilon ≤ ε₀ →
          P.epsilon = C.epsilon → P.center ∉ C.carrier →
          Disjoint C.closed_core P.carrier := by
  obtain ⟨ε₁, hε₁, hsmall, hthick⟩ := exists_closed_core_end_thickness_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hscale⟩ := EpsilonNeck.exists_scale_comparison_at_common_closure.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C P hε heq hcenter
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [disjoint_left]
  intro x hxcore hxP
  obtain ⟨q, hqP, hqC⟩ := mem_closure_iff.mp
    (C.closure_core_eq_closed_core.symm ▸ hxcore) P.carrier P.carrier_open hxP
  obtain ⟨p, hpP, hpC⟩ := C.boundary_inter_nonempty_of_crossing
    P.isConnected_carrier.isPreconnected ⟨q, hqP, hqC⟩
    ⟨P.center, P.central_sphere_subset P.center_on_central_sphere,
      fun h => hcenter (C.closed_core_subset_carrier h)⟩
  have hpEnd : p ∈ closure C.end_neck.carrier :=
    closure_mono (C.end_neck.region_subset_carrier _ _)
      (C.boundary_subset_negative_end_closure hpC)
  have hPscale := (hscale C.end_neck P
    (C.end_neck_epsilon.trans_le (hε.trans (min_le_right _ _)))
    (heq.trans_le (hε.trans (min_le_right _ _)))
    ⟨p, hpEnd, subset_closure hpP⟩).2
  have hlower := hthick C (hε.trans (min_le_left _ _)) x hxcore P.center
    hcenter
  have hupper := P.edist_center_le_balanced_upper_of_mem_closure
    (heq.trans_le (hε.trans ((min_le_left _ _).trans hsmall))) (subset_closure hxP)
  rw [heq] at hupper
  have hcomm : g.edist x P.center = g.edist P.center x := Manifold.riemannianEDist_comm
  rw [hcomm] at hlower
  have hstrict : ENNReal.ofReal ((1.01 : ℝ) * P.scale * C.epsilon⁻¹) <
      ENNReal.ofReal ((1.9 : ℝ) * C.end_neck.scale * C.epsilon⁻¹) := by
    have hi := inv_pos.mpr C.epsilon_pos
    have hs := C.end_neck.scale_pos
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hPscale hi.le, mul_pos hs hi]
  exact not_lt_of_ge hlower (hupper.trans_lt hstrict)

theorem exists_frontier_neck_disjoint_closed_core_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g) (P : EpsilonNeck g), C.epsilon ≤ ε₀ →
          P.epsilon = C.epsilon → P.center ∈ frontier C.carrier →
          Disjoint C.closed_core P.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, havoid⟩ :=
    exists_exterior_center_neck_disjoint_closed_core_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C P hε heq hcenter
  exact havoid C P hε heq ((C.carrier_open.frontier_eq ▸ hcenter).2)

end PoincareConjecture.CapCertificate
