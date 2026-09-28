import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckExcursionSubarcs
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckShortening
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem small_ball_subset_middle (N : EpsilonNeck g) {p : M}
    (hp : p ∈ N.central_sphere) :
    g.ball p (N.scale * N.epsilon⁻¹ / 8) ⊆
      N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro x hx
  obtain ⟨γ, h0, h1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hx
  by_contra hxout
  obtain ⟨c, hc0, hc1, hprefix, hheight⟩ := N.exists_first_half_neck_subarc
    zero_le_one hγ.continuousOn (by simpa only [h0] using hp)
      (by simpa only [h1] using hxout)
  have hcost := M28.path_axial_displacement_le N hc0.le
    (hγ.mono (Icc_subset_Icc le_rfl hc1)) hprefix
  rw [hheight] at hcost
  have htotal : ENNReal.ofReal ((N.scale / 2) * (N.epsilon⁻¹ / 2)) ≤
      g.pathELength γ 0 1 :=
    hcost.trans (Manifold.pathELength_mono le_rfl hc1)
  have hbudget : ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8) ≤
      ENNReal.ofReal ((N.scale / 2) * (N.epsilon⁻¹ / 2)) := by
    apply ENNReal.ofReal_le_ofReal
    have hprod : 0 ≤ N.scale * N.epsilon⁻¹ :=
      mul_nonneg N.scale_pos.le (inv_nonneg.mpr N.epsilon_pos.le)
    nlinarith
  exact (not_lt_of_ge (hbudget.trans htotal)) hlength



theorem precompact_ball_of_central_sphere (N : EpsilonNeck g) {p : M}
    (hp : p ∈ N.central_sphere) :
    IsCompact (closure (g.ball p (N.scale * N.epsilon⁻¹ / 8))) ∧
      closure (g.ball p (N.scale * N.epsilon⁻¹ / 8)) ⊆ N.carrier := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hlo : -N.epsilon⁻¹ < -(N.epsilon⁻¹ / 2) := by linarith
  have hhi : N.epsilon⁻¹ / 2 < N.epsilon⁻¹ := by linarith
  let K : Set M := N.coordinate_map ''
    (univ ×ˢ Icc (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2))
  have hK : IsCompact K := N.isCompact_coordinate_slab_intrinsic hlo hhi
  have hballK : g.ball p (N.scale * N.epsilon⁻¹ / 8) ⊆ K := by
    intro x hx
    have hmiddle := N.small_ball_subset_middle hp hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hmiddle.2.1.le, hmiddle.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hmiddle.1⟩
  have hclosure : closure (g.ball p (N.scale * N.epsilon⁻¹ / 8)) ⊆ K :=
    closure_minimal hballK hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hclosure,
    hclosure.trans (N.coordinate_slab_subset_carrier_m28 hlo hhi)⟩




theorem exists_central_sphere_minimizing_geodesic (N : EpsilonNeck g)
    (hepsilon : N.epsilon ≤ M28.neckShorteningEpsilon) {p q : M}
    (hp : p ∈ N.central_sphere) (hq : q ∈ N.central_sphere) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-δ) (1 + δ)) ∧ γ 0 = p ∧ γ 1 = q ∧
      MapsTo γ (Icc (0 : ℝ) 1) N.carrier ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hR : 0 < N.scale * N.epsilon⁻¹ / 8 := M28.neck_shortening_saving_pos N
  have hrecip : 32 * M28.standardSpherePathCeiling + 1 ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos hepsilon
    simpa only [M28.neckShorteningEpsilon, one_div_one_div, one_div, inv_inv] using h
  have hbudget : (4 * M28.standardSpherePathCeiling) * N.scale ≤
      N.scale * N.epsilon⁻¹ / 8 := by
    have h := mul_le_mul_of_nonneg_right hrecip N.scale_pos.le
    nlinarith [N.scale_pos]
  obtain ⟨σ, hσ0, hσ1, hσ, _, hσlen, _, _⟩ :=
    M28.exists_central_sphere_shortcut N hp hq
  have hqball : q ∈ g.ball p (N.scale * N.epsilon⁻¹ / 8) :=
    (Manifold.riemannianEDist_le_pathELength hσ.contMDiffOn hσ0 hσ1 zero_le_one).trans_lt
      (hσlen.trans_le (ENNReal.ofReal_le_ofReal hbudget))
  obtain ⟨δ, hδ, γ, hgeod, h0, h1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball p q hR
      (N.precompact_ball_of_central_sphere hp).1 hqball
  refine ⟨δ, hδ, γ, hgeod, h0, h1, ?_, hmin⟩
  intro t ht
  have hdist := hmin 0 (by norm_num) t ht
  rw [h0] at hdist
  have habs : |(0 : ℝ) - t| ≤ 1 := by
    rw [zero_sub, abs_neg, abs_of_nonneg ht.1]
    exact ht.2
  have hfactor : ENNReal.ofReal |(0 : ℝ) - t| ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal habs
  have hsmall : g.edist p (γ t) ≤ g.edist p q := by
    rw [hdist]
    simpa only [one_mul] using mul_le_mul_left hfactor (g.edist p q)
  exact (N.small_ball_subset_middle hp (hsmall.trans_lt hqball)).1

end PoincareConjecture.EpsilonNeck
