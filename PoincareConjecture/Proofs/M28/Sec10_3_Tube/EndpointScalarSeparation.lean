import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

theorem exists_endpoint_scalar_separation_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (C Q : ℝ) (z y : M),
        0 < Q → D.scalarCurvature z = 8 * Q →
        32 * (max C 2) ^ 4 * Q < D.scalarCurvature y →
        (∀ (Nz Ny : EpsilonNeck g),
          Nz.epsilon ≤ epsilon₀ → Ny.epsilon ≤ epsilon₀ →
          z ∈ Nz.carrier → y ∈ Ny.carrier → Disjoint Nz.carrier Ny.carrier) ∧
        (∀ (K : CapCertificate g) (Ny : EpsilonNeck g),
          K.cap_constant ≤ C → Ny.epsilon ≤ epsilon₀ →
          z ∈ K.carrier → y ∈ Ny.carrier → Disjoint K.carrier Ny.carrier) ∧
        (∀ (Nz : EpsilonNeck g) (K : CapCertificate g),
          Nz.epsilon ≤ epsilon₀ → K.cap_constant ≤ C →
          z ∈ Nz.carrier → y ∈ K.carrier → Disjoint Nz.carrier K.carrier) ∧
        (∀ K : CapCertificate g, K.cap_constant ≤ C →
          ¬ (z ∈ K.carrier ∧ y ∈ K.carrier)) ∧
        (∀ (K : CapCertificate g) (Nz Ny : EpsilonNeck g),
          K.cap_constant ≤ max C 2 →
          Nz.epsilon ≤ epsilon₀ → Ny.epsilon ≤ epsilon₀ →
          z ∈ Nz.carrier → y ∈ Ny.carrier →
          Disjoint K.carrier Nz.carrier ∨ Disjoint K.carrier Ny.carrier) := by
  obtain ⟨epsilon₀, hpos, hsmall, hratio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D C Q z y hQ hz hy
  let B := max C 2
  have hB : 2 ≤ B := le_max_right C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBQ : 0 < B * Q := mul_pos hBpos hQ
  have hBpow : B ≤ B ^ 4 := by
    have hsq : B ≤ B ^ 2 := by nlinarith only [sq_nonneg (B - 1), hB]
    nlinarith only [sq_nonneg (B ^ 2 - 1), hsq, hB]
  have hhigh : 32 * B * Q < D.scalarCurvature y := by
    apply lt_of_le_of_lt _ hy
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBpow (by norm_num : (0 : ℝ) ≤ 32)) hQ.le
  have hQle : Q ≤ B * Q := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_trans (by norm_num : (1 : ℝ) ≤ 2) hB) hQ.le
  have low_neck (N : EpsilonNeck g) (hepsilon : N.epsilon ≤ epsilon₀)
      (hzN : z ∈ N.carrier) (x : M) (hx : x ∈ N.carrier) :
      D.scalarCurvature x ≤ 16 * Q := by
    have h := hratio M g D N hepsilon x hx z hzN
    rw [hz] at h
    nlinarith only [h]
  have low_cap (K : CapCertificate g) (hK : K.cap_constant ≤ B)
      (hzK : z ∈ K.carrier) (x : M) (hx : x ∈ K.carrier) :
      D.scalarCurvature x < 8 * B * Q := by
    calc
      D.scalarCurvature x < B * D.scalarCurvature z := K.scalar_lt_mul D hK hzK hx
      _ = 8 * B * Q := by rw [hz]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Nz Ny hNz hNy hzN hyN
    apply Set.disjoint_left.mpr
    intro x hxz hxy
    have hl := low_neck Nz hNz hzN x hxz
    have hh := hratio M g D Ny hNy y hyN x hxy
    nlinarith only [hl, hh, hhigh, hQle]
  · intro K Ny hK hNy hzK hyN
    apply Set.disjoint_left.mpr
    intro x hxK hxy
    have hl := low_cap K (hK.trans (le_max_left C 2)) hzK x hxK
    have hh := hratio M g D Ny hNy y hyN x hxy
    nlinarith only [hl, hh, hhigh, hBQ]
  · intro Nz K hNz hK hzN hyK
    apply Set.disjoint_left.mpr
    intro x hxz hxK
    have hl := low_neck Nz hNz hzN x hxz
    have hh := K.scalar_lt_mul D (C := B) (hK.trans (le_max_left C 2)) hxK hyK
    have hmul := mul_le_mul_of_nonneg_left hl hBpos.le
    nlinarith only [hh, hmul, hhigh, hBQ]
  · intro K hK hboth
    have h := low_cap K (hK.trans (le_max_left C 2)) hboth.1 y hboth.2
    nlinarith only [h, hhigh, hBQ]
  · intro K Nz Ny hK hNz hNy hzN hyN
    classical
    by_cases hdisjoint : Disjoint K.carrier Nz.carrier
    · exact Or.inl hdisjoint
    · obtain ⟨x, hxK, hxz⟩ := Set.not_disjoint_iff_nonempty_inter.mp hdisjoint
      apply Or.inr
      apply Set.disjoint_left.mpr
      intro w hwK hwy
      have hl := low_neck Nz hNz hzN x hxz
      have hh := hratio M g D Ny hNy y hyN w hwy
      have hcap := K.scalar_lt_mul D (C := B) hK hxK hwK
      have hmul := mul_le_mul_of_nonneg_left hl hBpos.le
      nlinarith only [hh, hcap, hmul, hhigh]

theorem exists_cap_disjoint_one_of_endpoint_necks_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (C Q : ℝ) (z y : M) (K : CapCertificate g) (Nz Ny : EpsilonNeck g),
        0 < Q → D.scalarCurvature z = 8 * Q →
        32 * (max C 2) ^ 4 * Q < D.scalarCurvature y →
        K.cap_constant ≤ max C 2 →
        Nz.epsilon ≤ epsilon₀ → Ny.epsilon ≤ epsilon₀ →
        z ∈ Nz.carrier → y ∈ Ny.carrier →
        Disjoint K.carrier Nz.carrier ∨ Disjoint K.carrier Ny.carrier := by
  obtain ⟨epsilon₀, hpos, hsmall, hsep⟩ := exists_endpoint_scalar_separation_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D C Q z y K Nz Ny hQ hz hy hK hNz hNy hzN hyN
  exact (hsep M g D C Q z y hQ hz hy).2.2.2.2 K Nz Ny hK hNz hNy hzN hyN

end PoincareConjecture.M28
