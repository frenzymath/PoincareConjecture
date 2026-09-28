import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialTransversality










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_positive_cross_axis_composition :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (A B D : EpsilonNeck g),
      A.epsilon ≤ epsilon0 → B.epsilon ≤ epsilon0 → D.epsilon ≤ epsilon0 →
      ∀ x : M, x ∈ A.carrier → x ∈ B.carrier → x ∈ D.carrier →
        0 < B.scale * mvfderiv (𝓡 3) (fun y => (B.coordinate_inverse y).2) x
          (A.normalizedAxialVector x) →
        0 < D.scale * mvfderiv (𝓡 3) (fun y => (D.coordinate_inverse y).2) x
          (B.normalizedAxialVector x) →
        0 < D.scale * mvfderiv (𝓡 3) (fun y => (D.coordinate_inverse y).2) x
            (A.normalizedAxialVector x) ∧
          0 < A.scale * mvfderiv (𝓡 3) (fun y => (A.coordinate_inverse y).2) x
            (D.normalizedAxialVector x) := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ :=
    exists_intersecting_axial_control.{u} (α := (1 / 1000 : ℝ)) (by norm_num)
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g A B D hA hB hD x hxA hxB hxD hAB hBD
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let a (E : EpsilonNeck g) : TangentSpace (𝓡 3) x := E.normalizedAxialVector x
  let ell (E : EpsilonNeck g) : TangentSpace (𝓡 3) x →ₗ[ℝ] ℝ :=
    E.scale • (mvfderiv (𝓡 3) (fun y => (E.coordinate_inverse y).2) x).toLinearMap
  have hnorm (v : TangentSpace (𝓡 3) x) : ‖v‖ = g.tangentNorm x v :=
    norm_eq_sqrt_real_inner v
  have hself (E : EpsilonNeck g) (hxE : x ∈ E.carrier) : ell E (a E) = 1 :=
    E.normalizedAxialVector_axial_mvfderiv hxE
  have hbound (E : EpsilonNeck g) (hxE : x ∈ E.carrier)
      (v : TangentSpace (𝓡 3) x) : |ell E v| ≤ 2 * ‖v‖ := by
    have hscaled : Real.sqrt (1 - E.epsilon) * |ell E v| ≤ g.tangentNorm x v := by
      calc
        _ = E.scale * Real.sqrt (1 - E.epsilon) *
            |mvfderiv (𝓡 3) (fun y => (E.coordinate_inverse y).2) x v| := by
          change Real.sqrt (1 - E.epsilon) *
            |E.scale * mvfderiv (𝓡 3) (fun y => (E.coordinate_inverse y).2) x v| = _
          rw [abs_mul, abs_of_pos E.scale_pos]
          ring
        _ ≤ g.tangentNorm x v := E.axial_mvfderiv_bound hxE v
    rw [← hnorm v] at hscaled
    have hhalf : (1 : ℝ) / 2 < Real.sqrt (1 - E.epsilon) :=
      (Real.lt_sqrt (by norm_num)).mpr (by linarith [E.epsilon_lt_half])
    have hmul := mul_le_mul_of_nonneg_right hhalf.le (abs_nonneg (ell E v))
    linarith only [hscaled, hmul]
  have hpositive_close (E F : EpsilonNeck g)
      (he : E.epsilon ≤ epsilon0) (hf : F.epsilon ≤ epsilon0)
      (hxE : x ∈ E.carrier) (hxF : x ∈ F.carrier)
      (hEF : 0 < ell F (a E)) : ‖a F - a E‖ < (1 / 1000 : ℝ) := by
    obtain ⟨tau, htau, hclose⟩ := hcontrol E F he hf x hxE hxF
    have hc : ‖a F - tau • a E‖ < (1 / 1000 : ℝ) := by
      rw [hnorm]
      exact hclose
    rcases htau with rfl | rfl
    · simpa only [one_smul] using hc
    · have hsum : ‖a F + a E‖ < (1 / 1000 : ℝ) := by
        simpa only [neg_one_smul, sub_neg_eq_add] using hc
      have hsmall : |ell F (a F + a E)| < (2 / 1000 : ℝ) :=
        (hbound F hxF (a F + a E)).trans_lt (by linarith only [hsum])
      rw [map_add, hself F hxF] at hsmall
      have hlow : 1 + ell F (a E) ≤ |1 + ell F (a E)| := le_abs_self _
      exfalso
      linarith only [hsmall, hlow, hEF]
  have hab : ‖a B - a A‖ < (1 / 1000 : ℝ) :=
    hpositive_close A B hA hB hxA hxB hAB
  have hbd : ‖a D - a B‖ < (1 / 1000 : ℝ) :=
    hpositive_close B D hB hD hxB hxD hBD
  have had : ‖a D - a A‖ < (2 / 1000 : ℝ) := by
    calc
      _ = ‖(a D - a B) + (a B - a A)‖ := by congr 1; abel
      _ ≤ ‖a D - a B‖ + ‖a B - a A‖ := norm_add_le _ _
      _ < (2 / 1000 : ℝ) := by linarith only [hbd, hab]
  change 0 < ell D (a A) ∧ 0 < ell A (a D)
  constructor
  · have h : |ell D (a D - a A)| < (4 / 1000 : ℝ) :=
      (hbound D hxD (a D - a A)).trans_lt (by linarith only [had])
    rw [map_sub, hself D hxD] at h
    linarith only [(abs_lt.mp h).2]
  · have h : |ell A (a D - a A)| < (4 / 1000 : ℝ) :=
      (hbound A hxA (a D - a A)).trans_lt (by linarith only [had])
    rw [map_sub, hself A hxA] at h
    linarith only [(abs_lt.mp h).1]

end PoincareConjecture.EpsilonNeck
