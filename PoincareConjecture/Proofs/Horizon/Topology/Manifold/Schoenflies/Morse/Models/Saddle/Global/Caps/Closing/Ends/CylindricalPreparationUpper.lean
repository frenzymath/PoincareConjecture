import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CylindricalPreparation

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

theorem exists_prepared_cylindrical_upper_terminal_end_normalization
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : UpperAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hDb : D.center ≤ b) (haD : a < D.center)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ r d u : Real, 0 < r ∧ r < (D.center - a) / 2 ∧
      D.center < d ∧ 0 < u ∧ u < r ∧ a + u < d - u ∧
      ∃ G F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∃ Q : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
        (∀ y, inner Real v (G y) = inner Real v y) ∧
        EqOn G id {y | inner Real v y = a} ∧
        EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1) ∧
        (∀ t ∈ Icc (-r) r, ∀ q : S1,
          G (g (A.chart (q, a + t))) = g (A.chart (q, a)) + t • v) ∧
        (∃ K : Set E3, IsCompact K ∧
          K ⊆ {y | |inner Real v y - a| ≤ (D.center - a) / 2} ∧
          ∀ y ∉ K, G y = y) ∧
        (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, F y = y) ∧
        (∀ y, inner Real v y ≤ a + u / 4 → F y = G y) ∧
        (D.planeMap.trans Q.symm) '' sphere (0 : Hemisphere.Plane v) 1 =
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (g (A.chart (q, a)))) ∧
        F '' (g '' A.cappedRegion a) =
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
  obtain ⟨r, d, u, hr, hrR, hd, hu, hur, hsep, G₀, F₀, Q, hGheight,
    hcentral, hcap, hmotion, ⟨K, hK, hKslab, hGfix⟩, ⟨S, hS, hFfix⟩,
    hagree, hQ, hend⟩ :=
    exists_prepared_cylindrical_lower_terminal_end_normalization A.reflected hg'
      (neg_le_neg hDb) (neg_lt_neg haD) hgerm'
  change d < -D.center at hd
  change r < (-a - -D.center) / 2 at hrR
  let G := (J.trans G₀).trans J
  let F := (J.trans F₀).trans J
  have hG (y : E3) : G y = J (G₀ (J y)) := rfl
  have hF (y : E3) : F y = J (F₀ (J y)) := rfl
  have hconjfix (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
      (W : Set E3) (hfix : ∀ y ∉ W, H y = y) (y : E3) (hy : y ∉ J '' W) :
      J (H (J y)) = y := by
    have hnot : J y ∉ W := fun h => hy
      ⟨J y, h, heightReflection_heightReflection D.unit_v y⟩
    rw [hfix _ hnot]
    exact heightReflection_heightReflection D.unit_v y
  have hQ' : (D.planeMap.trans Q.symm) '' sphere (0 : Hemisphere.Plane v) 1 =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (A.chart (q, a)))) := by
    simpa only [reflected, A.chart_apply, projection_heightReflection] using hQ
  refine ⟨r, -d, u, hr, by linarith, by linarith, hu, hur, by linarith,
    G, F, Q, ?_, ?_, ?_, ?_, ⟨J '' K, hK.image J.contMDiff.continuous, ?_, ?_⟩,
    ⟨J '' S, hS.image J.contMDiff.continuous, ?_⟩, ?_, hQ', ?_⟩
  · intro y
    rw [hG]
    change inner Real v (heightReflection D.unit_v (G₀ (J y))) = _
    rw [inner_heightReflection, hGheight]
    simp only [J, inner_heightReflection, neg_neg]
  · intro y hy
    have hcy : inner Real v (J y) = -a := by
      simpa only [J, inner_heightReflection] using congrArg Neg.neg hy
    rw [hG, hcentral hcy]
    exact heightReflection_heightReflection D.unit_v y
  · intro p hp
    change J (G₀ (J (g p))) = g p
    have hc : G₀ (J (g p)) = J (g p) := hcap hp
    rw [hc]
    exact heightReflection_heightReflection D.unit_v (g p)
  · intro t ht q
    have hn : -a + -t = -(a + t) := by ring
    have hm := hmotion (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ q
    have hm' : G₀ (J (g (A.chart (q, a + t)))) =
        J (g (A.chart (q, a))) + (-t) • v := by
      simpa only [A.chart_apply, hn] using hm
    rw [hG, hm']
    apply (heightCoordinates D.unit_v).symm.injective
    apply Prod.ext
    · change inner Real v (heightReflection D.unit_v _) = inner Real v _
      simp only [inner_heightReflection, inner_add_right, inner_smul_right,
        J, real_inner_self_eq_norm_sq, D.unit_v, one_pow, mul_one]
      ring
    · change (Hemisphere.Plane v).orthogonalProjectionOnto (heightReflection D.unit_v _) =
        (Hemisphere.Plane v).orthogonalProjectionOnto _
      simp only [projection_heightReflection, map_add, map_smul, J, Hemisphere.Plane,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
        smul_zero, add_zero]
  · rintro _ ⟨y, hy, rfl⟩
    have hs := hKslab hy
    change |inner Real v y - -a| ≤ (-a - -D.center) / 2 at hs
    change |inner Real v (heightReflection D.unit_v y) - a| ≤ (D.center - a) / 2
    rw [inner_heightReflection]
    have heq : -inner Real v y - a = -(inner Real v y - -a) := by ring
    rw [heq, abs_neg]
    convert hs using 1
    ring
  · intro y hy
    exact hconjfix G₀ K hGfix y hy
  · intro y hy
    exact hconjfix F₀ S hFfix y hy
  · intro y hy
    rw [hF, hG, hagree]
    change -a - u / 4 ≤ inner Real v (heightReflection D.unit_v y)
    rw [inner_heightReflection]
    linarith
  · have hFimage : F '' (g '' A.cappedRegion a) =
        J '' (F₀ '' (g' '' A.reflected.cappedRegion (-a))) := by
      rw [← A.cappedRegion_eq_reflected a]
      simp only [F, Diffeomorph.coe_trans, image_comp, g']
    change F₀ '' (g' '' A.reflected.cappedRegion (-a)) = _ at hend
    rw [hFimage, hend, image_union]
    have hcap' : J '' (liftPlaneDiffeomorph D.unit_v d (-D.scale)
        D.reflected.scale_ne_zero (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) =
        liftPlaneDiffeomorph D.unit_v (-d) D.scale D.scale_ne_zero
          (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v := by
      simpa only [neg_neg] using image_heightReflection_liftPlaneDiffeomorph
        D.unit_v d (-D.scale) D.reflected.scale_ne_zero
        (D.planeMap.trans Q.symm) (boundedCylinderNorthernCap v)
    change J '' (liftPlaneDiffeomorph D.unit_v d (-D.scale)
      D.reflected.scale_ne_zero (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) ∪ _ = _
    rw [hcap']
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
