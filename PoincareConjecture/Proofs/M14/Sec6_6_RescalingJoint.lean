import PoincareConjecture.Proofs.M14.Sec6_6_RescalingStable

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

noncomputable def rescalingParameterHomeomorph (x : G.Point) :
    G.Horizontal x × ℝ ≃ₜ (rescalingTransport hM12 hM13 G Q hQ a).Horizontal x × ℝ :=
  (rescalingInitialEquiv G.spacetime Q hQ a x).toHomeomorph.prodCongr
    (Homeomorph.mulLeft₀ (Real.sqrt Q) (Real.sqrt_pos.mpr hQ).ne')

theorem rescalingAdmissible_iff (T : ℝ) (x : G.Point) (z : G.Horizontal x × ℝ) :
    z ∈ M14AdmissibleParameter G T x ↔
      rescalingParameterHomeomorph hM12 hM13 G Q hQ a x z ∈
        M14AdmissibleParameter (rescalingTransport hM12 hM13 G Q hQ a)
          (parabolicTime Q a T) x := by
  change (0 ≤ z.2 ∧ T - z.2 ^ 2 ∈ I.domain) ↔
    (0 ≤ Real.sqrt Q * z.2 ∧ parabolicTime Q a T - (Real.sqrt Q * z.2) ^ 2 ∈
      (parabolicInterval Q hQ a I).domain)
  have he : parabolicTime Q a T - (Real.sqrt Q * z.2) ^ 2 =
      parabolicTime Q a (T - z.2 ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hQ.le]
    unfold parabolicTime
    ring
  rw [he, parabolicTime_mem_parabolicInterval_iff]
  exact and_congr (mul_nonneg_iff_of_pos_left (Real.sqrt_pos.mpr hQ)).symm Iff.rfl

noncomputable def rescalingStableSetInverse {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x)
    (H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x E') : M14StableSet G T τ x E := by
  have hτ : 0 < τ := (mul_pos_iff_of_pos_left hQ).mp H'.tau_pos
  let q₀' := H'.endpoint_slice_map 0
  let q₀ : (G.slices (T - τ)).Point := ⟨q₀'.val, by
    have ht := q₀'.property
    change parabolicTime Q a (G.spacetime.timeFunction q₀'.val) =
      parabolicTime Q a T - Q * τ at ht
    apply (mul_left_cancel₀ hQ.ne')
    unfold parabolicTime at ht
    linear_combination ht⟩
  exact stableSetOfSlicePoint E hτ q₀

include hCoordinates in

theorem rescalingStableGraph_iff {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (z : G.Horizontal x × ℝ) :
    z ∈ M14StableGraph G E ↔
      rescalingParameterHomeomorph hM12 hM13 G Q hQ a x z ∈
        M14StableGraph (rescalingTransport hM12 hM13 G Q hQ a) E' := by
  let A := rescalingInitialEquiv G.spacetime Q hQ a x
  change (∃ τ, ∃ H : M14StableSet G T τ x E, 0 < τ ∧ z.1 ∈ H.carrier ∧ z.2 = Real.sqrt τ) ↔
    ∃ τ', ∃ H' : M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) τ' x E',
      0 < τ' ∧ A z.1 ∈ H'.carrier ∧ Real.sqrt Q * z.2 = Real.sqrt τ'
  constructor
  · rintro ⟨τ, H, hτ, hZ, hs⟩
    let H' := rescalingStableSet hM12 hM13 G Q hQ a E E' H
    refine ⟨Q * τ, H', mul_pos hQ hτ,
      (rescalingStable_carrier_iff hCoordinates hM12 hM13 G Q hQ a E E' H H' z.1).mp hZ, ?_⟩
    rw [hs, Real.sqrt_mul hQ.le]
  · rintro ⟨τ', H', hτ', hZ, hs⟩
    have hex : Nonempty (M14StableSet (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * (τ' / Q)) x E') := by
      rw [mul_div_cancel₀ _ hQ.ne']
      exact ⟨H'⟩
    obtain ⟨H''⟩ := hex
    let H := rescalingStableSetInverse hM12 hM13 G Q hQ a E E' H''
    have hZ' : A z.1 ∈ H''.carrier := by
      rw [H''.carrier_exact, mul_div_cancel₀ _ hQ.ne']
      exact (H'.carrier_exact _).mp hZ
    refine ⟨τ' / Q, H, div_pos hτ' hQ,
      (rescalingStable_carrier_iff hCoordinates hM12 hM13 G Q hQ a E E' H H'' z.1).mpr hZ', ?_⟩
    apply (mul_left_cancel₀ (Real.sqrt_pos.mpr hQ).ne')
    rw [← Real.sqrt_mul hQ.le, mul_div_cancel₀ _ hQ.ne']
    exact hs

private theorem relativeInterior_homeomorph_iff {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β)
    (A S : Set α) (A' S' : Set β)
    (hA : ∀ z, z ∈ A ↔ e z ∈ A') (hS : ∀ z, z ∈ S ↔ e z ∈ S') (z : α) :
    z ∈ M14RelativeInterior A S ↔ e z ∈ M14RelativeInterior A' S' := by
  constructor
  · rintro ⟨hz, U, hU, hzu, hUS⟩
    refine ⟨(hS z).mp hz, e.symm ⁻¹' U, hU.preimage e.symm.continuous, ?_, ?_⟩
    · simpa only [mem_preimage, e.symm_apply_apply] using hzu
    · rintro w ⟨hw, hwA⟩
      have hwa : e.symm w ∈ A := (hA _).mpr (by simpa only [e.apply_symm_apply] using hwA)
      simpa only [e.apply_symm_apply] using (hS _).mp (hUS ⟨hw, hwa⟩)
  · rintro ⟨hz, U, hU, hzu, hUS⟩
    refine ⟨(hS z).mpr hz, e ⁻¹' U, hU.preimage e.continuous, hzu, ?_⟩
    rintro w ⟨hw, hwA⟩
    exact (hS w).mpr (hUS ⟨hw, (hA w).mp hwA⟩)

include hCoordinates in

theorem rescalingJointDomain_iff {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x) (s : ℝ) :
    (Z, s) ∈ M14JointDomain G E ↔
      (rescalingInitialEquiv G.spacetime Q hQ a x Z, Real.sqrt Q * s) ∈
        M14JointDomain (rescalingTransport hM12 hM13 G Q hQ a) E' :=
  relativeInterior_homeomorph_iff (rescalingParameterHomeomorph hM12 hM13 G Q hQ a x)
    _ _ _ _ (rescalingAdmissible_iff hM12 hM13 G Q hQ a T x)
    (rescalingStableGraph_iff hCoordinates hM12 hM13 G Q hQ a E E') (Z, s)

end PoincareConjecture.M14
