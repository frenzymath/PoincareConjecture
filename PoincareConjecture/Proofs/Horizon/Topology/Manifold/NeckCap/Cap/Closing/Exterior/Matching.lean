import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Exterior.Filling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.CollarFilling











noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)
  (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)



theorem exists_matching_exterior_ball_in_euclidean_cap
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture)
    (D : CapCertificate g) (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact
      (closure (connectedComponent C.boundary_neck.center \ C.closed_core)))
    (hsub : closure (connectedComponent C.boundary_neck.center \ C.closed_core) ⊆
      D.carrier) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    ∃ (r : ℝ) (b : OpenPartialHomeomorph E3 UnitThreeSphere)
        (v : OpenPartialHomeomorph E3 M),
      0 < r ∧ Metric.closedBall 0 1 ⊆ b.source ∧
      Metric.closedBall 0 1 ⊆ v.source ∧ v.target ⊆ D.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ v v.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ v.symm v.target ∧ b 0 = a ∧
      b '' Metric.closedBall 0 1 = closure A ∧ b '' Metric.ball 0 1 = A ∧
      v '' Metric.closedBall 0 1 =
        closure (connectedComponent C.boundary_neck.center \ C.closed_core) ∧
      v '' Metric.ball 0 1 = connectedComponent C.boundary_neck.center \ C.closed_core ∧
      v '' Metric.sphere 0 1 = C.boundary_sphere ∧
      Disjoint (v '' Metric.ball 0 1) C.closed_core ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
        Real.exp t • (q : E3) ∈ b.source ∧
        Real.exp t • (q : E3) ∈ v.source ∧
        S.cover (b (Real.exp t • (q : E3))) = v (Real.exp t • (q : E3)) := by
  let K := C.projectiveClosedCoreLift S
  let A := connectedComponentIn Kᶜ a
  let B := Neg.neg '' A
  obtain ⟨η, σ, b, hη, hσ, hbs, hb, hbi, hb0, hbclosed, hbopen, _, hbmatch⟩ :=
    C.exists_projective_exterior_matching_ball S a ha
  obtain ⟨v, hvs, hvt, hv, hvi, hvclosed, hvopen, hvsphere⟩ :=
    C.exists_ball_neighborhood_of_exterior_in_euclidean_cap D hD hcompact hsub
  obtain ⟨R, hR⟩ : ∃ R : Diffeomorph CylModel CylModel
      RoundCylinderSpace RoundCylinderSpace ∞,
      ∀ p : RoundCylinderSpace, R p = (p.1, σ * p.2) := by
    rcases hσ with hσ | hσ
    · exact ⟨Diffeomorph.refl _ _ _, fun p => by simp [hσ]⟩
    · refine ⟨{
        toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
        contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
        contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }, ?_⟩
      intro p
      change (p.1, -p.2) = _
      simp [hσ]
  let N := C.boundary_neck
  let c := R.toHomeomorph.toOpenPartialHomeomorph.trans N.coordinatePartialHomeomorph
  have hcq (p : RoundCylinderSpace) : c p = N.coordinate_map (p.1, σ * p.2) := by
    change N.coordinate_map (R p) = _
    rw [hR]
  have hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source :=
    N.coordinate_map_smooth.comp R.contMDiff.contMDiffOn inter_subset_right
  have hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target :=
    R.symm.contMDiff.comp_contMDiffOn (N.coordinate_inverse_smooth.mono inter_subset_left)
  have hcz (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source := by
    refine ⟨mem_univ _, ?_⟩
    change R (q, 0) ∈ N.cylinderDomain
    rw [hR, mul_zero]
    exact ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hczero : c '' (univ ×ˢ ({0} : Set ℝ)) = v '' Metric.sphere 0 1 := by
    rw [hvsphere, C.boundary_eq_neck_sphere, ← N.centralSphere_range]
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨q, by simp [hcq]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, by simp [hcq]⟩
  have hdis : Disjoint (closure A) (closure B) :=
    C.disjoint_closure_projectiveClosedCoreLift_exterior S a ha
  have hclosedcover : closure A ∪ closure B = (interior K)ᶜ := by
    rw [← closure_union, (C.projectiveClosedCoreLift_exterior_components S a ha).2.2.2.1,
      closure_compl]
  let rad : RoundCylinderSpace → E3 := fun p => Real.exp p.2 • (p.1 : E3)
  have hrad : Continuous rad :=
    (Real.continuous_exp.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)
  let V : Opens RoundCylinderSpace :=
    ⟨(c.source ∩ c ⁻¹' v.target) ∩
      (rad ⁻¹' (b.source ∩ b ⁻¹' (closure B)ᶜ)) ∩ (univ ×ˢ Ioo (-η) η),
      ((c.continuousOn.isOpen_inter_preimage c.open_source v.open_target).inter
        ((b.continuousOn.isOpen_inter_preimage b.open_source isClosed_closure.isOpen_compl).preimage
          hrad)).inter (isOpen_univ.prod isOpen_Ioo)⟩
  have hVzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ V := by
    refine ⟨⟨⟨hcz q, ?_⟩, ?_, ?_⟩, mem_univ _, neg_lt_zero.mpr hη, hη⟩
    · have h := hczero.subset (mem_image_of_mem c
        (show (q, (0 : ℝ)) ∈ univ ×ˢ ({0} : Set ℝ) from ⟨mem_univ _, rfl⟩))
      obtain ⟨x, hx, hxeq⟩ := h
      change c (q, 0) ∈ v.target
      exact hxeq ▸ v.map_source (hvs (Metric.sphere_subset_closedBall hx))
    · simpa [rad] using hbs (Metric.sphere_subset_closedBall q.property)
    · change b (rad (q, 0)) ∉ closure B
      apply disjoint_left.mp hdis
      apply hbclosed.subset
      exact mem_image_of_mem b (by simp [rad])
  obtain ⟨δ, hδ, hδV⟩ := CylinderGluing.exists_cylinder_collar V hVzero
  have hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source :=
    fun z hz => (hδV z (abs_lt.mpr hz.2)).1.1.1
  have hct : c '' (univ ×ˢ Ioo (-δ) δ) ⊆ v.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hδV z (abs_lt.mpr hz.2)).1.1.2
  have hpos (q : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
      c (q, t) ∉ v '' Metric.closedBall 0 1 := by
    have hzV := hδV (q, t) (by simpa only [abs_of_pos ht] using htδ)
    have hzη : |t| < η := abs_lt.mpr hzV.2.2
    have hnorm : 1 < ‖rad (q, t)‖ := by
      simpa [rad, norm_smul, Real.norm_eq_abs, Real.abs_exp] using Real.one_lt_exp_iff.mpr ht
    have hbnot : b (rad (q, t)) ∉ closure A := by
      intro h
      obtain ⟨x, hx, hxeq⟩ := hbclosed.symm.subset h
      have heq : x = rad (q, t) := b.injOn (hbs hx) hzV.1.2.1 hxeq
      have hle : ‖rad (q, t)‖ ≤ 1 := by simpa only [heq, mem_closedBall_zero_iff] using hx
      exact (not_le_of_gt hnorm) hle
    have hbcore : b (rad (q, t)) ∈ interior K := by
      by_contra hn
      rcases hclosedcover.symm.subset hn with h | h
      · exact hbnot h
      · exact hzV.1.2.2 h
    have hcore : c (q, t) ∈ C.core := by
      have h := (C.interior_projectiveClosedCoreLift S).subset hbcore
      rw [hcq, ← (hbmatch q t hzη).2.2]
      exact h.2
    rw [hvclosed, C.closure_exterior_eq_component_diff_core]
    exact fun h => h.2 hcore
  obtain ⟨r, w, hr, hrδ, hws, hwt, hw, hwi, hwclosed, hwmatch⟩ :=
    Poincare.exists_ball_neighborhood_matching_collar v hvs hv hvi c hc hci hδ
      hcs hct hczero hpos
  have hwopen : w '' Metric.ball 0 1 =
      connectedComponent C.boundary_neck.center \ C.closed_core := by
    rw [w.image_ball_eq_interior hws (hwclosed.trans hvclosed), C.interior_closure_exterior]
  have hwsphere : w '' Metric.sphere 0 1 = C.boundary_sphere := by
    rw [w.image_sphere_eq_frontier hws (hwclosed.trans hvclosed),
      ← v.image_sphere_eq_frontier hvs hvclosed, hvsphere]
  refine ⟨r, b, w, hr, hbs, hws, hwt ▸ hvt, hb, hbi, hw, hwi, hb0,
    hbclosed, hbopen, hwclosed.trans hvclosed, hwopen, hwsphere, ?_, ?_⟩
  · rw [hwopen]
    exact disjoint_sdiff_left
  · intro q t ht
    have hzV := hδV (q, t) (ht.trans hrδ)
    have hbt := hbmatch q t (abs_lt.mpr hzV.2.2)
    obtain ⟨hws', hwq⟩ := hwmatch (q, t) ht
    exact ⟨hbt.1, hws', hbt.2.2.trans ((hcq (q, t)).symm.trans hwq.symm)⟩

end PoincareConjecture.CapCertificate
