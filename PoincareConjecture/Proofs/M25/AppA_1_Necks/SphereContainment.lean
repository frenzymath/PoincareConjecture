import PoincareConjecture.Proofs.M25.AppA_1_Necks.CarrierBuffer
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SliceProjectionDifferential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter













set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck





theorem exists_middle_central_sphere_containment {κ : ℝ} (hκ : κ ∈ Ioc 0 1) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.center ∈ N.carrier →
      |(N.coordinate_inverse N'.center).2| ≤ (1 - κ) * N.epsilon⁻¹ →
      N'.central_sphere ⊆ N.carrier := by
  obtain ⟨εs, hεs, hcap, hscale⟩ := exists_overlap_scale_control.{u} (α := 1) (by norm_num)
  let C := 2 * neckDepthConstant
  have hC : 0 < C := mul_pos (by norm_num) neckDepthConstant_pos
  have hden : 0 < 16 * Real.pi * C := by positivity
  refine ⟨min εs (κ / (16 * Real.pi * C)),
    lt_min hεs (div_pos hκ.1 hden), (min_le_left _ _).trans hcap, ?_⟩
  intro M _ _ _ _ _ instT3 g N N' hN hcenter hmiddle y hy
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ instT3)
  have hratio := (abs_lt.mp (hscale N (hN.trans (min_le_left _ _)) N' hcenter)).2
  have hscale' : N'.scale < 2 * N.scale :=
    (div_lt_iff₀ N.scale_pos).mp (by linarith)
  let δ := N.epsilon⁻¹ - |(N.coordinate_inverse N'.center).2|
  have hδ : 0 < δ :=
    sub_pos.mpr (abs_lt.mpr (N.coordinate_inverse_mem N'.center hcenter).2)
  have hmargin : κ / N.epsilon ≤ δ := by
    dsimp only [δ]
    rw [div_eq_mul_inv]
    linarith
  have hsmall : N.epsilon ≤ κ / (16 * Real.pi * C) :=
    hN.trans (min_le_right _ _)
  have hδlarge : 16 * Real.pi * C ≤ δ := by
    apply le_trans _ hmargin
    apply (le_div_iff₀ N.epsilon_pos).mpr
    simpa only [mul_comm N.epsilon] using (le_div_iff₀ hden).mp hsmall
  have hhalf : (1 : ℝ) / 2 < Real.sqrt (1 - N.epsilon) :=
    (Real.lt_sqrt (by norm_num)).mpr (by linarith [N.epsilon_lt_half])
  let R := N.scale * Real.sqrt (1 - N.epsilon) * δ / C
  have hR : 8 * Real.pi * N.scale ≤ R := by
    apply (le_div_iff₀ hC).mpr
    calc
      (8 * Real.pi * N.scale) * C = (N.scale * (1 / 2)) * (16 * Real.pi * C) := by ring
      _ ≤ (N.scale * (1 / 2)) * δ :=
        mul_le_mul_of_nonneg_left hδlarge (mul_nonneg N.scale_pos.le (by norm_num))
      _ ≤ N.scale * Real.sqrt (1 - N.epsilon) * δ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hhalf.le N.scale_pos.le) hδ.le
  apply N.mem_carrier_of_edist_lt_buffer hcenter
  change g.edist N'.center y < ENNReal.ofReal R
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi) * N'.scale) :=
      N'.edist_central_sphere_le_two_pi_mul_scale N'.center_on_central_sphere hy
    _ < ENNReal.ofReal ((4 * Real.pi) * N.scale) := by
      apply (ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) N.scale_pos)).mpr
      nlinarith [mul_lt_mul_of_pos_left hscale' Real.pi_pos]
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by
      have hpos : 0 < Real.pi * N.scale := mul_pos Real.pi_pos N.scale_pos
      linarith)





theorem exists_middle_central_sphere_graph {κ : ℝ} (hκ : κ ∈ Ioc 0 1) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 → N'.center ∈ N.carrier →
      |(N.coordinate_inverse N'.center).2| ≤ (1 - κ) * N.epsilon⁻¹ →
      N'.central_sphere ⊆ N.carrier ∧
      (∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
        range (fun q => N.coordinate_map (q, h q)) = N'.central_sphere) ∧
      SmoothSphereIsotopicIn N.carrier N.central_sphere N'.central_sphere := by
  obtain ⟨εc, hcpos, hccap, hcontains⟩ := exists_middle_central_sphere_containment.{u} hκ
  obtain ⟨εg, hgpos, _, hgraph⟩ := exists_contained_slice_graph.{u}
  refine ⟨min εc εg, lt_min hcpos hgpos, (min_le_left _ _).trans hccap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hcenter hmiddle
  have hsub := hcontains N N' (hN.trans (min_le_left _ _)) hcenter hmiddle
  have hslice (q : UnitTwoSphere) : N'.coordinate_map (q, 0) ∈ N.carrier := by
    apply hsub
    rw [← N'.coordinate_zero_range]
    exact mem_range_self q
  have h := hgraph N N' (hN.trans (min_le_right _ _)) (hN'.trans (min_le_right _ _))
    0 N'.zero_mem_interval hslice
  rw [N'.coordinate_zero_range] at h
  exact ⟨hsub, h⟩

end PoincareConjecture.EpsilonNeck
