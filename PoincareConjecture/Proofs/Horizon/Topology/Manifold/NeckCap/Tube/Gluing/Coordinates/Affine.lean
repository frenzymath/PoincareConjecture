import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Centered
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.CenteredScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing

theorem exists_cylinder_collar (U : Opens RoundCylinderSpace)
    (hzero : ∀ q : UnitTwoSphere, (q, (0 : ℝ)) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : RoundCylinderSpace, |p.2| < r → p ∈ U := by
  have hz : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero q
  obtain ⟨u, v, _, hv, hu, h0, huv⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) U.isOpen hz
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hv 0 (h0 (by simp))
  refine ⟨r, hr, fun p hp => huv ⟨hu (mem_univ p.1), ?_⟩⟩
  exact hrv (by simpa [Metric.mem_ball, Real.dist_eq] using hp)

end PoincareConjecture.CylinderGluing

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem exists_affine_neck_coordinates
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (r : ℝ) (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        RoundCylinderSpace N.carrierOpen ∞),
      0 < r ∧
      (∀ p, (N.coordinate_inverse (D p)).1 = p.1) ∧
      (∀ p : RoundCylinderSpace, |p.2| < r →
        N.coordinate_inverse (D p) = (p.1, f p.1 + p.2)) ∧
      ∀ p : RoundCylinderSpace,
        (N.coordinate_inverse (D p)).2 ≤ f p.1 ↔ p.2 ≤ 0 := by
  obtain ⟨K, hKfst, hKzero, hKderiv, hKside⟩ := N.exists_centered_neck_coordinates f hf hdom
  let h : RoundCylinderSpace → ℝ := fun p => (N.coordinate_inverse (K p)).2 - f p.1
  have hh : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h :=
    (contMDiff_snd.comp (contMDiff_subtype_val.comp
      (N.coordinateDiffeomorph.symm.contMDiff.comp K.contMDiff))).sub
        (hf.comp contMDiff_fst)
  have hz (q : UnitTwoSphere) : h (q, 0) = 0 := by
    dsimp [h]
    rw [hKzero, N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom q⟩]
    exact sub_self _
  have hp (q : UnitTwoSphere) : 0 < deriv (fun t : ℝ => h (q, t)) 0 := by
    obtain ⟨a, ha, hd⟩ := hKderiv (q, 0)
    have hhd := hd.sub_const (f q)
    change HasDerivAt (fun t : ℝ => h (q, t)) a 0 at hhd
    rwa [hhd.deriv]
  obtain ⟨R, C, hR, hCfst, hCzero, _, hCside, hCagree⟩ :=
    CylinderGluing.exists_centered_scalar_extension h hh hz hp
  have hCinvfst (p : RoundCylinderSpace) : (C.symm p).1 = p.1 := by
    simpa only [C.apply_symm_apply] using (hCfst (C.symm p)).symm
  let U : Opens RoundCylinderSpace :=
    ⟨{p | |(C.symm p).2| < R},
      isOpen_lt ((continuous_snd.comp C.symm.continuous).abs) continuous_const⟩
  have hU0 (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ U := by
    have heq : C.symm (q, 0) = (q, 0) := by
      simpa only [hCzero] using C.symm_apply_apply (q, 0)
    change |(C.symm (q, 0)).2| < R
    simpa only [heq, abs_zero] using hR
  obtain ⟨r, hr, hrc⟩ := CylinderGluing.exists_cylinder_collar U hU0
  let D := C.symm.trans K
  refine ⟨r, D, hr, ?_, ?_, ?_⟩
  · intro p
    change (N.coordinate_inverse (K (C.symm p))).1 = p.1
    rw [hKfst, hCinvfst]
  · intro p hpr
    have heq := hCagree (C.symm p).1 (C.symm p).2 (hrc p hpr)
    have hpair : ((C.symm p).1, (C.symm p).2) = C.symm p := Prod.eta _
    rw [hpair, C.apply_symm_apply] at heq
    have hheight := congrArg Prod.snd heq
    change p.2 = (N.coordinate_inverse (K (C.symm p))).2 - f (C.symm p).1 at hheight
    rw [hCinvfst] at hheight
    apply Prod.ext
    · exact (hKfst (C.symm p)).trans (hCinvfst p)
    · change (N.coordinate_inverse (K (C.symm p))).2 = f p.1 + p.2
      linarith
  · intro p
    have hs := hKside (C.symm p).1 (C.symm p).2
    change (N.coordinate_inverse (K (C.symm p))).2 ≤ f (C.symm p).1 ↔
      (C.symm p).2 ≤ 0 at hs
    have hp := hCside (C.symm p)
    rw [C.apply_symm_apply] at hp
    rw [hCinvfst] at hs
    exact hs.trans hp.symm

end PoincareConjecture.EpsilonNeck
