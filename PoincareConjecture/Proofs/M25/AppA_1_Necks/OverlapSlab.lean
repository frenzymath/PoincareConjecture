import PoincareConjecture.Proofs.M25.AppA_1_Necks.CarrierBuffer
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Overlap_A11
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic












set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal Bundle

universe u

namespace PoincareConjecture




theorem RiemannianMetric.m25_edist_le_intrinsicEDist
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (U : Set M) (x y : M) :
    g.edist x y ≤ intrinsicEDist g U x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_sInf
  rintro L ⟨γ, hγ, h0, h1, _, rfl⟩
  exact Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one

namespace EpsilonNeck




theorem edist_le_axial_add
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) {x y : M}
    (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    g.edist x y ≤ ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) *
      (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
        Real.sqrt 2 * (Real.pi + 1))) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  exact (g.m25_edist_le_intrinsicEDist N.carrier x y).trans
    (N.intrinsicEDist_le_axial_add hx hy)





theorem exists_middle_overlap_slab {L κ : ℝ} (hL : 0 ≤ L) (hκ : κ ∈ Ioc 0 1) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 → N'.center ∈ N.carrier →
      |(N.coordinate_inverse N'.center).2| ≤ (1 - κ) * N.epsilon⁻¹ →
      univ ×ˢ Icc ((N.coordinate_inverse N'.center).2 - L)
          ((N.coordinate_inverse N'.center).2 + L) ⊆
        N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier := by
  obtain ⟨εs, hεs, hcap, hscale⟩ :=
    exists_overlap_scale_control.{u} (α := 1 / 2) (by norm_num)
  let D := neckDepthConstant
  let A := L + Real.sqrt 2 * (Real.pi + 1)
  have hD : 0 < D := neckDepthConstant_pos
  have hA : 0 < A := by dsimp only [A]; positivity
  have hLden : 0 < 2 * (L + 1) := by positivity
  have hden : 0 < 32 * D * A := by positivity
  refine ⟨min εs (min (κ / (2 * (L + 1))) (1 / (32 * D * A))),
    lt_min hεs (lt_min (div_pos hκ.1 hLden) (div_pos zero_lt_one hden)),
    (min_le_left _ _).trans hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hcenter hmiddle z hz
  let s0 := (N.coordinate_inverse N'.center).2
  change |s0| ≤ (1 - κ) * N.epsilon⁻¹ at hmiddle
  have hsmall : N.epsilon ≤ κ / (2 * (L + 1)) :=
    hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmargin : 2 * (L + 1) ≤ κ * N.epsilon⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    simpa only [mul_comm N.epsilon] using (le_div_iff₀ hLden).mp hsmall
  have hheight : |z.2 - s0| ≤ L := by
    have hs : z.2 ∈ Icc (s0 - L) (s0 + L) := hz.2
    exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hzN : z ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, abs_lt.mp ?_⟩
    calc
      |z.2| = |(z.2 - s0) + s0| := by congr 1; ring
      _ ≤ |z.2 - s0| + |s0| := abs_add_le _ _
      _ ≤ L + (1 - κ) * N.epsilon⁻¹ := add_le_add hheight hmiddle
      _ < N.epsilon⁻¹ := by nlinarith
  have hy : N.coordinate_map z ∈ N.carrier := N.coordinate_map_mem hzN
  have hratio := (abs_lt.mp
    (hscale N (hN.trans (min_le_left _ _)) N' hcenter)).1
  have hscale' : N.scale < 2 * N'.scale := by
    have h := (lt_div_iff₀ N.scale_pos).mp
      (show (1 : ℝ) / 2 < N'.scale / N.scale by linarith)
    linarith
  have hsmall' : N'.epsilon ≤ 1 / (32 * D * A) :=
    hN'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hinv : 32 * D * A ≤ N'.epsilon⁻¹ := by
    have h := (le_div_iff₀ hden).mp hsmall'
    have h' : 32 * D * A ≤ 1 / N'.epsilon :=
      (le_div_iff₀ N'.epsilon_pos).mpr (by nlinarith)
    simpa only [one_div] using h'
  have hhalf : (1 : ℝ) / 2 < Real.sqrt (1 - N'.epsilon) :=
    (Real.lt_sqrt (by norm_num)).mpr (by linarith [N'.epsilon_lt_half])
  let R := N'.scale * Real.sqrt (1 - N'.epsilon) * N'.epsilon⁻¹ / (2 * D)
  have hR : 8 * N'.scale * A ≤ R := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hD)).mpr
    calc
      (8 * N'.scale * A) * (2 * D) =
          (N'.scale * (1 / 2)) * (32 * D * A) := by ring
      _ ≤ (N'.scale * (1 / 2)) * N'.epsilon⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg N'.scale_pos.le (by norm_num))
      _ ≤ N'.scale * Real.sqrt (1 - N'.epsilon) * N'.epsilon⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hhalf.le N'.scale_pos.le)
          (inv_nonneg.mpr N'.epsilon_pos.le)
  have hsqrt : Real.sqrt (1 + N.epsilon) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith [N.epsilon_lt_half]⟩
  have hdist := N.edist_le_axial_add hcenter hy
  rw [N.coordinate_inverse_coordinate_map hzN] at hdist
  have hupper : N.scale * Real.sqrt (1 + N.epsilon) *
      (|z.2 - s0| + Real.sqrt 2 * (Real.pi + 1)) ≤ 2 * N.scale * A := by
    calc
      _ ≤ N.scale * Real.sqrt (1 + N.epsilon) * A :=
        mul_le_mul_of_nonneg_left (add_le_add hheight le_rfl)
          (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
      _ ≤ N.scale * 2 * A := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt N.scale_pos.le) hA.le
      _ = _ := by ring
  have hc' := (N'.mem_central_sphere_iff N'.center).mp N'.center_on_central_sphere
  refine ⟨hzN, N'.mem_carrier_of_edist_lt_buffer hc'.1 ?_⟩
  rw [hc'.2, abs_zero, sub_zero]
  change g.edist N'.center (N.coordinate_map z) < ENNReal.ofReal R
  calc
    _ ≤ ENNReal.ofReal (2 * N.scale * A) :=
      hdist.trans (ENNReal.ofReal_le_ofReal hupper)
    _ < ENNReal.ofReal (4 * N'.scale * A) := by
      apply (ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (mul_pos (by norm_num) N'.scale_pos) hA)).mpr
      nlinarith [mul_lt_mul_of_pos_right hscale' hA]
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by
      have hpos : 0 < N'.scale * A := mul_pos N'.scale_pos hA
      linarith)

end EpsilonNeck
end PoincareConjecture
