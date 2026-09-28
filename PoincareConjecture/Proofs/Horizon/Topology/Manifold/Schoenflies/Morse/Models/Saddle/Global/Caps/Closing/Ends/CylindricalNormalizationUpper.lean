import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CylindricalNormalization



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap Poincare.Geometry.Euclidean Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1



theorem exists_supported_cylindrical_upper_terminal_end_normalization
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : UpperAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hDb : D.center ≤ b) (haD : a < D.center)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {w : Real} (hw : 0 < w)
    (hconstant : ∀ t ∈ Icc a (a + w),
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (A.chart (q, t)))) =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (A.chart (q, a))))) :
    ∃ d u : Real, D.center < d ∧ 0 < u ∧ u < w ∧ a + u < d - u ∧
      ∃ Q : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v),
      ∃ S : Set E3, IsCompact S ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (D.planeMap.trans Q.symm) '' sphere (0 : Hemisphere.Plane v) 1 =
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (g (A.chart (q, a)))) ∧
        (∀ y ∉ S, R y = y) ∧
        (∀ y, inner Real v y ≤ a + u / 4 → R y = y) ∧
        R '' (g '' A.cappedRegion a) =
          (liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero
            (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) ∪
          (fun x : Real × Hemisphere.Plane v => x.1 • v + (x.2 : E3)) ''
            (Icc a d ×ˢ range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
              (g (A.chart (q, a))))) := by
  let J := heightReflection D.unit_v
  let g' : S2 → E3 := J ∘ g
  have hg' : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g' := by
    apply isSmoothEmbedding_of_injective_mfderiv (J.contMDiff.comp hg.contMDiff)
      (J.injective.comp hg.isEmbedding.injective)
    intro p
    rw [mfderiv_comp p (J.contMDiff.mdifferentiable (by simp) _)
      (hg.contMDiff.mdifferentiable (by simp) _)]
    exact (J.mfderivToContinuousLinearEquiv (by simp) (g p)).injective.comp
      (injective_mfderiv_sphere_embedding hg p)
  have hgerm' : ∀ p ∈ C,
      (fun q => -h q) =ᶠ[𝓝 p] (fun q => inner Real v (g' q)) := by
    intro p hp
    filter_upwards [hgerm p hp] with q hq
    change -h q = inner Real v (heightReflection D.unit_v (g q))
    rw [inner_heightReflection, hq]
  have hc : ∀ t ∈ Icc (-a - w) (-a),
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g' (A.reflected.chart (q, t)))) =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g' (A.reflected.chart (q, -a)))) := by
    intro t ht
    have hh := hconstant (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [g', Function.comp_apply, J, projection_heightReflection,
      A.chart_apply, neg_neg] using hh
  obtain ⟨d, u, hd, hu, huw, hsep, Q, S, hS, R₀, hQ, hfix, hhalf, hend⟩ :=
    exists_supported_cylindrical_lower_terminal_end_normalization A.reflected hg'
      (neg_le_neg hDb) (neg_lt_neg haD) hgerm' hw hc
  change d < -D.center at hd
  let R := (J.trans R₀).trans J
  have hR (y : E3) : R y = J (R₀ (J y)) := rfl
  refine ⟨-d, u, by linarith, hu, huw, by linarith, Q,
    J '' S, hS.image J.contMDiff.continuous, R, ?_, ?_, ?_, ?_⟩
  · simpa only [reflected, g', Function.comp_apply, J,
      A.chart_apply, projection_heightReflection] using hQ
  · intro y hy
    have hnot : J y ∉ S := fun hh => hy
      ⟨J y, hh, heightReflection_heightReflection D.unit_v y⟩
    rw [hR, hfix _ hnot]
    exact heightReflection_heightReflection D.unit_v y
  · intro y hy
    have hj : -a - u / 4 ≤ inner Real v (J y) := by
      change -a - u / 4 ≤ inner Real v (heightReflection D.unit_v y)
      rw [inner_heightReflection]
      linarith
    rw [hR, hhalf _ hj]
    exact heightReflection_heightReflection D.unit_v y
  · have himage : R '' (g '' A.cappedRegion a) =
        J '' (R₀ '' (g' '' A.reflected.cappedRegion (-a))) := by
      rw [← A.cappedRegion_eq_reflected a]
      simp only [R, Diffeomorph.coe_trans, image_comp, g']
    change R₀ '' (g' '' A.reflected.cappedRegion (-a)) = _ at hend
    rw [himage, hend, image_union]
    have hcap : J '' (liftPlaneDiffeomorph D.unit_v d (-D.scale)
        D.reflected.scale_ne_zero (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) =
        liftPlaneDiffeomorph D.unit_v (-d) D.scale D.scale_ne_zero
          (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v := by
      simpa only [neg_neg] using image_heightReflection_liftPlaneDiffeomorph
        D.unit_v d (-D.scale) D.reflected.scale_ne_zero
        (D.planeMap.trans Q.symm) (boundedCylinderNorthernCap v)
    change J '' (liftPlaneDiffeomorph D.unit_v d (-D.scale)
      D.reflected.scale_ne_zero (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) ∪ _ = _
    rw [hcap]
    congr 1
    simp only [projection_heightReflection, ← A.chart_apply]
    rw [image_image]
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      refine ⟨(-t, x), ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hx⟩, ?_⟩
      exact (heightReflection_height_add_plane D.unit_v t x).symm
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      refine ⟨(-t, x), ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hx⟩, ?_⟩
      simp only [J, heightReflection_height_add_plane, neg_neg]

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
