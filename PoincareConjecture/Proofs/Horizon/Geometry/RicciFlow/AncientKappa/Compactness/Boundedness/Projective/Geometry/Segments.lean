import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CylinderCover

private theorem exists_initial_segment_in_closed_set
    {M : Type*} [TopologicalSpace M] {γ : ℝ → M} {L : ℝ} (hL : 0 ≤ L)
    {U K : Set M} (hU : IsOpen U) (hK : IsClosed K) (hUK : U ⊆ K)
    (hγ : ContinuousOn γ (Icc 0 L)) (hstart : γ 0 ∈ U) (hout : γ L ∉ K) :
    ∃ t ∈ Ioc 0 L, γ t ∈ K ∧ γ t ∉ U ∧ MapsTo γ (Ico 0 t) U := by
  let S : Set ℝ := Icc 0 L ∩ γ ⁻¹' Uᶜ
  have hSclosed : IsClosed S :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl
  have hSne : S.Nonempty := ⟨L, ⟨⟨hL, le_rfl⟩, fun h => hout (hUK h)⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun _ ht => ht.1.1⟩
  let t := sInf S
  have htS : t ∈ S := hSclosed.csInf_mem hSne hSbdd
  have ht : t ∈ Ioc 0 L := ⟨lt_of_le_of_ne htS.1.1 (by
    intro heq
    exact htS.2 (heq ▸ hstart)), htS.1.2⟩
  have hbefore : MapsTo γ (Ico 0 t) U := by
    intro s hs
    by_contra hnot
    have hsS : s ∈ S := ⟨⟨hs.1, hs.2.le.trans ht.2⟩, hnot⟩
    exact (not_le_of_gt hs.2) (csInf_le hSbdd hsS)
  have htK : γ t ∈ K := by
    have hpre : IsClosed (Icc 0 L ∩ γ ⁻¹' K) :=
      hγ.preimage_isClosed_of_isClosed isClosed_Icc hK
    have hsub : Ico 0 t ⊆ Icc 0 L ∩ γ ⁻¹' K :=
      fun s hs => ⟨⟨hs.1, hs.2.le.trans ht.2⟩, hUK (hbefore hs)⟩
    have hmem : t ∈ Icc 0 L ∩ γ ⁻¹' K := by
      apply hpre.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt ht.1)]
      exact ⟨ht.1.le, le_rfl⟩
    exact hmem.2
  exact ⟨t, ht, htK, htS.2, hbefore⟩

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem axial_displacement_le_of_unit_speed
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε r : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hr : 0 < r)
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w))
    {a : M → ℝ}
    (ha : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)))
    (hvalue : ∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, a (f z) = z.2)
    {γ : ℝ → M} {L : ℝ} (hL : 0 ≤ L) (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hcarrier : MapsTo γ (Icc 0 L) (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)))
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) :
    |a (γ L) - a (γ 0)| ≤ (2 / r) * L := by
  let F := a ∘ γ
  let v := fun t => mvfderiv (𝓡 3) a (γ t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt F (v t) t :=
    hasDerivAt_comp_geodesic (isOpen_image_slab hf) ha hγ (fun t ht => hcarrier ht) ht
  have hbound (t : ℝ) (ht : t ∈ Ico 0 L) : ‖v t‖ ≤ 2 / r := by
    have ht' : t ∈ Icc 0 L := ⟨ht.1, ht.2.le⟩
    obtain ⟨z, hz, heq⟩ := hcarrier ht'
    let V : TangentSpace (𝓡 3) (f z) := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1
    obtain ⟨w, hw⟩ := ((hf ⟨z, hz⟩).mfderivToContinuousLinearEquiv
      (by simp)).surjective V
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z w = V at hw
    have hunit : g.tangentNorm (f z) V = 1 := by rw [heq]; exact hspeed t ht'
    have hpull : roundCylinderPullback g f z w w = 1 := by
      have hnonneg : 0 ≤ g.inner (f z) V V := by
        by_cases hV : V = 0
        · simp [hV]
        · exact (g.pos (f z) V hV).le
      have hsq := congrArg (fun x : ℝ => x ^ 2) hunit
      dsimp only [RiemannianMetric.tangentNorm] at hsq
      rw [Real.sq_sqrt hnonneg, one_pow] at hsq
      simpa only [roundCylinderPullback, hw] using hsq
    have hax : v t = w.2 := by
      have hh := cylinderCover_axialCoordinate_mfderiv hf ha hvalue hz w
      rw [hw, heq] at hh
      exact hh
    have hmodel : w.2 ^ 2 ≤ EvolvingRoundCylinderMetric 0 z w w := by
      dsimp only [EvolvingRoundCylinderMetric]
      nlinarith [real_inner_self_nonneg (x := mfderiv (𝓡 2) (𝓡 3)
        (fun q : UnitTwoSphere => q.1) z.1 w.1)]
    have hmodelabs : |w.2| ≤ Real.sqrt (EvolvingRoundCylinderMetric 0 z w w) :=
      (Real.sqrt_sq_eq_abs w.2).symm.trans_le (Real.sqrt_le_sqrt hmodel)
    rw [Real.norm_eq_abs, hax]
    apply (le_div_iff₀ hr).mpr
    have hh := cylinderCover_scaled_model_length_le_two g f hε.le hεhalf hr hclose
      hz.2 w hpull
    nlinarith [mul_le_mul_of_nonneg_left hmodelabs hr.le]
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound L ⟨hL, le_rfl⟩
  simpa only [F, Function.comp_apply, Real.norm_eq_abs, sub_zero] using hh

omit [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M] in
theorem exists_initial_segment_to_half_slab
    {f : RoundCylinderSpace → M} {ε : ℝ} (hε : 0 < ε)
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    {a : M → ℝ} (hvalue : ∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, a (f z) = z.2)
    {γ : ℝ → M} {L : ℝ} (hL : 0 ≤ L)
    (hγ : ContinuousOn γ (Icc 0 L))
    (hstart : γ 0 ∈ f '' (univ ×ˢ Ioo (-ε⁻¹ / 2) (ε⁻¹ / 2)))
    (hout : γ L ∉ f '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2))) :
    ∃ t ∈ Ioc 0 L, MapsTo γ (Icc 0 t) (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) ∧
      |a (γ t)| = ε⁻¹ / 2 := by
  have hi : 0 < ε⁻¹ := inv_pos.mpr hε
  have hsub : univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2) ⊆
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ : Set RoundCylinderSpace) := by
    rintro z ⟨_, hz⟩
    exact ⟨mem_univ _, by linarith [hz.1], by linarith [hz.2]⟩
  have hoopensub : univ ×ˢ Ioo (-ε⁻¹ / 2) (ε⁻¹ / 2) ⊆
      (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2) : Set RoundCylinderSpace) := by
    rintro z ⟨_, hz⟩
    exact ⟨mem_univ _, hz.1.le, hz.2.le⟩
  have hhalfopen : IsOpen (f '' (univ ×ˢ Ioo (-ε⁻¹ / 2) (ε⁻¹ / 2))) := by
    have hh := isOpen_image_slab (s := ε⁻¹ / 2) (f := f) (fun z =>
      hf ⟨z.val, hsub (hoopensub (by simpa only [neg_div] using z.property))⟩)
    simpa only [neg_div] using hh
  have hhalfcompact : IsCompact (f '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2))) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (hf.contMDiffOn.continuousOn.mono hsub)
  obtain ⟨t, ht, htK, htU, hbefore⟩ := exists_initial_segment_in_closed_set
    hL hhalfopen hhalfcompact.isClosed (image_mono hoopensub) hγ hstart hout
  obtain ⟨z, hz, hzγ⟩ := htK
  refine ⟨t, ht, ?_, ?_⟩
  · intro s hs
    rcases hs.2.eq_or_lt with rfl | hst
    · exact ⟨z, hsub hz, hzγ⟩
    · exact image_mono (hoopensub.trans hsub) (hbefore ⟨hs.1, hst⟩)
  · have hboundary : z.2 = -ε⁻¹ / 2 ∨ z.2 = ε⁻¹ / 2 := by
      by_contra hn
      push Not at hn
      exact htU ⟨z, ⟨mem_univ _, lt_of_le_of_ne hz.2.1 hn.1.symm,
        lt_of_le_of_ne hz.2.2 hn.2⟩, hzγ⟩
    rw [← hzγ, hvalue z (hsub hz)]
    rcases hboundary with he | he
    · rw [he, abs_of_neg (by linarith)]
      ring
    · rw [he, abs_of_pos (by positivity)]

end PoincareConjecture.CylinderCover
