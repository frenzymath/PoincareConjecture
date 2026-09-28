import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.NormalizedCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.NormalizedCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.CenteredScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem deriv_nonneg_of_right_positive {h : ℝ → ℝ}
    (hd : DifferentiableAt ℝ h 0) (hz : h 0 = 0)
    {r : ℝ} (hr : 0 < r) (hp : ∀ t, 0 < t → t < r → 0 < h t) :
    0 ≤ deriv h 0 := by
  apply ge_of_tendsto hd.hasDerivAt.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with t ht htr
  have ht0 : 0 < t := ht
  have hht : 0 ≤ h t := (hp t ht0 htr).le
  simpa only [zero_add, hz, sub_zero, smul_eq_mul] using
    mul_nonneg (inv_nonneg.mpr ht0.le) hht

theorem centered_transition_extension_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ 1 / 200 → B.epsilon ≤ 1 / 200 →
        ∀ s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹,
        (∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) →
        ∀ f : UnitTwoSphere → ℝ,
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f →
        (∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹) →
        range (fun q => A.coordinate_map (q, f q)) =
          range (fun q => B.coordinate_map (q, s)) →
        (∀ x ∈ A.carrier ∩ B.carrier,
          s < (B.coordinate_inverse x).2 ↔
            f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2) →
        ∃ (r : ℝ) (G : Diffeomorph CylModel CylModel
            RoundCylinderSpace RoundCylinderSpace ∞),
          0 < r ∧
          (∀ p : RoundCylinderSpace, (G p).2 ≤ 0 ↔ p.2 ≤ 0) ∧
          (∀ p : RoundCylinderSpace, (G p).2 = 0 ↔ p.2 = 0) ∧
          ∀ t : ℝ, |t| < r →
            s + t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ ∧
            (∀ q : UnitTwoSphere, B.coordinate_map (q, s + t) ∈ A.carrier) ∧
            ∀ q : UnitTwoSphere,
              G (q, t) =
                ((A.coordinate_inverse (B.coordinate_map (q, s + t))).1,
                  (A.coordinate_inverse (B.coordinate_map (q, s + t))).2 -
                    f (A.coordinate_inverse (B.coordinate_map (q, s + t))).1) := by
  intro M _ _ _ _ _ _ _ g A B hA hB s hs hc f hf hfd hrange hside
  obtain ⟨R, D, F, hR, hF, hDheight, hFangular, _, hFderiv, hagree⟩ :=
    normalized_collar_of_epsilon_le A B hA hB s hs hc
  let h : RoundCylinderSpace → ℝ := fun p => (F p).2 - f p.1
  have hh : ContMDiff CylModel 𝓘(ℝ, ℝ) ∞ h :=
    (contMDiff_snd.comp hF).sub (hf.comp contMDiff_fst)
  have hz (q : UnitTwoSphere) : h (q, 0) = 0 := by
    have ha := (hagree 0 (by simpa using hR)).2.2 q
    let z := (D.symm (q, 0)).1
    have hx : B.coordinate_map (z, s) ∈ range (fun q => A.coordinate_map (q, f q)) := by
      rw [hrange]
      exact mem_range_self z
    obtain ⟨v, hv⟩ := hx
    have hi := congrArg A.coordinate_inverse hv
    rw [A.coordinate_inverse_coordinate_map ⟨mem_univ _, hfd v⟩] at hi
    have hFq : F (q, 0) = (v, f v) := by
      simp only [add_zero] at ha
      exact ha.trans hi.symm
    have hvq : v = q := by simpa only [hFq] using hFangular (q, 0)
    dsimp [h]
    rw [hFq, hvq]
    exact sub_self _
  have hp (q : UnitTwoSphere) : 0 < deriv (fun t : ℝ => h (q, t)) 0 := by
    have hdiff := (((hh.comp ((contMDiff_const (c := q)).prodMk contMDiff_id)).contDiff).differentiable
      (by simp)) 0
    have hpos (t : ℝ) (ht0 : 0 < t) (htR : t < R) : 0 < h (q, t) := by
      obtain ⟨ht, hct, ha⟩ := hagree t (by rwa [abs_of_pos ht0])
      let z := (D.symm (q, t)).1
      let x := B.coordinate_map (z, s + t)
      have hxA : x ∈ A.carrier := hct z
      have hxB : x ∈ B.carrier := B.coordinate_map_mem ⟨mem_univ _, ht⟩
      have hi : B.coordinate_inverse x = (z, s + t) :=
        B.coordinate_inverse_coordinate_map ⟨mem_univ _, ht⟩
      have hlt := (hside x ⟨hxA, hxB⟩).mp (by rw [hi]; dsimp; linarith)
      have ha' : F (q, t) = A.coordinate_inverse x := ha q
      rw [← ha', hFangular] at hlt
      exact sub_pos.mpr hlt
    have hn := deriv_nonneg_of_right_positive hdiff (hz q) hR hpos
    have hdf := (((contMDiff_snd.comp hF).comp
      ((contMDiff_const (c := q)).prodMk contMDiff_id)).contDiff.differentiable (by simp)) 0
    have hd := (hdf.hasDerivAt.sub_const (f q)).deriv
    change deriv (fun t : ℝ => h (q, t)) 0 = deriv (fun t : ℝ => (F (q, t)).2) 0 at hd
    have hne : deriv (fun t : ℝ => h (q, t)) 0 ≠ 0 := hd ▸ hFderiv q
    exact lt_of_le_of_ne hn hne.symm
  obtain ⟨r, K, hr, hKfst, hKzero, hKmono, hKside, hKagree⟩ :=
    CylinderGluing.exists_centered_scalar_extension h hh hz hp
  refine ⟨min R r, D.trans K, lt_min hR hr, ?_, ?_, ?_⟩
  · intro p
    change (K (D p)).2 ≤ 0 ↔ p.2 ≤ 0
    rw [hKside, hDheight]
  · intro p
    have hzK := congrArg Prod.snd (hKzero (D p).1)
    have hziff := (hKmono (D p).1).injective.eq_iff
      (a := (D p).2) (b := 0)
    change (K (D p)).2 = (K ((D p).1, 0)).2 ↔ (D p).2 = 0 at hziff
    rw [hzK, hDheight] at hziff
    exact hziff
  · intro t ht
    obtain ⟨hts, hct, ha⟩ := hagree t (ht.trans_le (min_le_left _ _))
    refine ⟨hts, hct, ?_⟩
    intro q
    have hDp : D (q, t) = ((D (q, t)).1, t) := by
      apply Prod.ext
      · rfl
      · exact hDheight (q, t)
    have hFa := ha (D (q, t)).1
    rw [← hDp, D.symm_apply_apply] at hFa
    change K (D (q, t)) = _
    rw [hDp, hKagree _ _ (ht.trans_le (min_le_right _ _))]
    dsimp only [h]
    have hfirst : (D (q, t)).1 =
        (A.coordinate_inverse (B.coordinate_map (q, s + t))).1 := by
      rw [← hFa, hFangular]
    rw [← hDp, hFa, hfirst]

end PoincareConjecture.EpsilonNeck
