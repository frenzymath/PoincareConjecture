import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.CoreTube.InteriorSphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem slice_through_point_subset_slab_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    {p : M} (hpN : p ∈ N.carrier) {a b : ℝ}
    (ha : -P.epsilon⁻¹ < a) (hb : b < P.epsilon⁻¹)
    (hp : p ∈ P.region a b)
    (hda : P.epsilon⁻¹ / 4 ≤ (P.coordinate_inverse p).2 - a)
    (hdb : P.epsilon⁻¹ / 4 ≤ b - (P.coordinate_inverse p).2) :
    ∀ q : UnitTwoSphere,
      N.coordinate_map (q, (N.coordinate_inverse p).2) ∈
        P.coordinate_map '' (univ ×ˢ Icc a b) := by
  have hNs := abs_lt.mp (N.abs_scaled_scalar_sub_one_lt_half_on_carrier N.connection hN hpN)
  have hPs := abs_lt.mp (P.abs_scaled_scalar_sub_one_lt_half_on_carrier N.connection hP hp.1)
  have hscale : N.scale ≤ 2 * P.scale := by
    have h₁ := mul_lt_mul_of_pos_left hNs.2 (sq_pos_of_pos P.scale_pos)
    have h₂ := mul_lt_mul_of_pos_left hPs.1 (sq_pos_of_pos N.scale_pos)
    nlinarith only [h₁, h₂, N.scale_pos, P.scale_pos]
  have hsqrt : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + N.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + N.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [N.epsilon_lt_half]
  have hz := (N.coordinate_inverse_mem p hpN).2
  intro q
  have hdiam : g.edist p (N.coordinate_map (q, (N.coordinate_inverse p).2)) ≤
      ENNReal.ofReal ((4 * Real.pi) * P.scale) := by
    have h := N.edist_coordinate_map_slice_le (N.coordinate_inverse p).1 q hz
    rw [Prod.eta, N.coordinate_map_coordinate_inverse hpN] at h
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt N.scale_pos.le) Real.pi_pos.le
    have hmul' := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith only [hmul, hmul']
  by_contra hout
  have hdist := P.edist_lower_of_not_mem_coordinate_slab ha hb hp hda hdb hout
  have hreal : P.scale * Real.sqrt (1 - P.epsilon) * (P.epsilon⁻¹ / 4) ≤
      (4 * Real.pi) * P.scale :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity [P.scale_pos, Real.pi_pos])).mp (hdist.trans hdiam)
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - P.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - P.epsilon by linarith [P.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - P.epsilon), P.epsilon_lt_half]
  have hinv : (200 : ℝ) ≤ P.epsilon⁻¹ := by
    have hi := one_div_le_one_div_of_le P.epsilon_pos hP
    norm_num at hi
    simpa only [one_div] using hi
  have hroot' := mul_le_mul_of_nonneg_left hroot
    (mul_nonneg P.scale_pos.le (inv_nonneg.mpr P.epsilon_pos.le))
  have hlarge := mul_le_mul_of_nonneg_left hinv P.scale_pos.le
  have hpi := mul_lt_mul_of_pos_right Real.pi_lt_four P.scale_pos
  nlinarith only [hreal, hroot', hlarge, hpi, P.scale_pos]

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem exists_core_point_capturing_neck_spheres (C : CapCertificate g) :
    ∃ p ∈ C.core, ∀ N : EpsilonNeck g, N.epsilon ≤ 1 / 200 → p ∈ N.carrier →
      ∀ q : UnitTwoSphere,
        N.coordinate_map (q, (N.coordinate_inverse p).2) ∈ C.core ∧
        N.coordinate_map (q, (N.coordinate_inverse p).2) ∈ C.boundary_neck.carrier := by
  let B := C.boundary_neck
  have hR : 0 < B.epsilon⁻¹ := inv_pos.mpr B.epsilon_pos
  let q₀ := (B.coordinate_inverse B.center).1
  have hpoint (t : ℝ) (ht : t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹) :
      B.coordinate_map (q₀, t) ∈ B.carrier ∧
      (B.coordinate_inverse (B.coordinate_map (q₀, t))).2 = t :=
    ⟨B.coordinate_map_mem ⟨mem_univ _, ht⟩,
      congrArg Prod.snd (B.coordinate_inverse_coordinate_map ⟨mem_univ _, ht⟩)⟩
  have hB : B.epsilon ≤ 1 / 200 := C.boundary_neck_epsilon.trans_le C.epsilon_le_threshold
  rcases C.boundary_neck_sides with ⟨hnegative, _⟩ | ⟨hpositive, _⟩
  · let p := B.coordinate_map (q₀, -B.epsilon⁻¹ / 2)
    obtain ⟨hpB, hpaxis⟩ := hpoint (-B.epsilon⁻¹ / 2) (by constructor <;> linarith)
    have hpregion : p ∈ B.region (-B.epsilon⁻¹) 0 :=
      ⟨hpB, by rw [hpaxis]; linarith, by rw [hpaxis]; linarith⟩
    refine ⟨p, hnegative hpregion, fun N hN hpN q => ?_⟩
    have hs := N.slice_through_point_subset_slab_of_epsilon_le B hN hB hpN
      (a := -3 * B.epsilon⁻¹ / 4) (b := -B.epsilon⁻¹ / 4)
      (by linarith) (by linarith)
      ⟨hpB, by rw [hpaxis]; linarith, by rw [hpaxis]; linarith⟩
      (by rw [hpaxis]; linarith) (by rw [hpaxis]; linarith) q
    obtain ⟨z, hz, heq⟩ := hs
    have hzdom : z ∈ B.cylinderDomain :=
      ⟨mem_univ _, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hzregion : B.coordinate_map z ∈ B.region (-B.epsilon⁻¹) 0 := by
      refine ⟨B.coordinate_map_mem hzdom, ?_⟩
      rw [B.coordinate_inverse_coordinate_map hzdom]
      exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact heq ▸ ⟨hnegative hzregion, hzregion.1⟩
  · let p := B.coordinate_map (q₀, B.epsilon⁻¹ / 2)
    obtain ⟨hpB, hpaxis⟩ := hpoint (B.epsilon⁻¹ / 2) (by constructor <;> linarith)
    have hpregion : p ∈ B.region 0 B.epsilon⁻¹ :=
      ⟨hpB, by rw [hpaxis]; linarith, by rw [hpaxis]; linarith⟩
    refine ⟨p, hpositive hpregion, fun N hN hpN q => ?_⟩
    have hs := N.slice_through_point_subset_slab_of_epsilon_le B hN hB hpN
      (a := B.epsilon⁻¹ / 4) (b := 3 * B.epsilon⁻¹ / 4)
      (by linarith) (by linarith)
      ⟨hpB, by rw [hpaxis]; linarith, by rw [hpaxis]; linarith⟩
      (by rw [hpaxis]; linarith) (by rw [hpaxis]; linarith) q
    obtain ⟨z, hz, heq⟩ := hs
    have hzdom : z ∈ B.cylinderDomain :=
      ⟨mem_univ _, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hzregion : B.coordinate_map z ∈ B.region 0 B.epsilon⁻¹ := by
      refine ⟨B.coordinate_map_mem hzdom, ?_⟩
      rw [B.coordinate_inverse_coordinate_map hzdom]
      exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact heq ▸ ⟨hpositive hzregion, hzregion.1⟩

end PoincareConjecture.CapCertificate
