import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialOrientation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphHeight











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem contMDiff_transition_height_slice (N N' : EpsilonNeck g)
    {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hsub : ∀ q : UnitTwoSphere, N.coordinate_map (q, s) ∈ N'.carrier) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun q : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (q, s))).2) := by
  intro q
  have hm := N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds (show (q, s) ∈ N.cylinderDomain from ⟨mem_univ q, hs⟩))
  have hi := N'.coordinate_inverse_smooth.contMDiffAt
    (N'.carrier_open.mem_nhds (hsub q))
  have hp : ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : UnitTwoSphere => (p, s)) q := contMDiffAt_id.prodMk contMDiffAt_const
  exact contMDiffAt_snd.comp q (hi.comp q (hm.comp q hp))




theorem transition_height_horizontal_deriv (N N' : EpsilonNeck g)
    {q : UnitTwoSphere} {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hx' : N.coordinate_map (q, s) ∈ N'.carrier) (v : TangentSpace (𝓡 2) q) :
    mvfderiv (𝓡 2)
        (fun p : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (p, s))).2) q v =
      (N.scale / N'.scale) * (N'.scale *
        mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) (N.coordinate_map (q, s))
          (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            N.coordinate_map (q, s) (v, 0))) := by
  let D : RoundCylinderSpace → (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
    fun z => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z
  let L := mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) (N.coordinate_map (q, s))
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds
      (show (q, s) ∈ N.cylinderDomain from ⟨mem_univ q, hs⟩))).mdifferentiableAt (by simp)
  have hi := (N'.coordinate_inverse_smooth.contMDiffAt
    (N'.carrier_open.mem_nhds hx')).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      (fun y => (N'.coordinate_inverse y).2) (N.coordinate_map (q, s)) :=
    mdifferentiableAt_snd.comp (N.coordinate_map (q, s)) hi
  have hp : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : UnitTwoSphere => (p, s)) q := mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hd : mvfderiv (𝓡 2)
      (fun p : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (p, s))).2) q v =
      L (D (q, s) (v, 0)) := by
    have hc := mfderiv_comp_apply q hl (hm.comp q hp) v
    change mvfderiv (𝓡 2)
        (fun p : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (p, s))).2) q v =
      L (mfderiv (𝓡 2) (𝓡 3) (N.coordinate_map ∘ (fun p : UnitTwoSphere => (p, s))) q v) at hc
    rw [mfderiv_comp_apply q hm hp, mfderiv_prod_left] at hc
    exact hc
  change _ = (N.scale / N'.scale) * (N'.scale * L (N.scale⁻¹ • D (q, s) (v, 0)))
  rw [hd, map_smul, smul_eq_mul]
  field_simp [N.scale_pos.ne', N'.scale_pos.ne']




theorem transition_height_axial_error (N N' : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain)
    (hx' : N.coordinate_map z ∈ N'.carrier) {σ τ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : 0 ≤ τ)
    (hratio : |N.scale / N'.scale - 1| ≤ τ) (hr : N.scale / N'.scale ≤ 2)
    (haxis : |1 - σ * (N'.scale *
      mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) (N.coordinate_map z)
        (N.normalizedAxialVector (N.coordinate_map z)))| ≤ τ) :
    |deriv (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).2) z.2 - σ| ≤
      3 * τ := by
  let r := N.scale / N'.scale
  let b := N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
    (N.coordinate_map z) (N.normalizedAxialVector (N.coordinate_map z))
  have hrpos : 0 < r := div_pos N.scale_pos N'.scale_pos
  have habsσ : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  change |1 - σ * b| ≤ τ at haxis
  have hb : |b - σ| ≤ τ := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul, abs_sub_comm] using haxis
    · simpa only [neg_one_mul, sub_neg_eq_add, add_comm] using haxis
  have hd : deriv (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).2) z.2 =
      r * b := by
    have h := N.scaled_cross_axis_eq_real_deriv N' hz hx'
    change b = (N'.scale / N.scale) *
      deriv (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).2) z.2 at h
    rw [h]
    dsimp only [r]
    field_simp [N.scale_pos.ne', N'.scale_pos.ne']
  rw [hd]
  calc
    |r * b - σ| = |r * (b - σ) + (r - 1) * σ| := by congr 1; ring
    _ ≤ |r * (b - σ)| + |(r - 1) * σ| := abs_add_le _ _
    _ = r * |b - σ| + |r - 1| := by
      rw [abs_mul, abs_mul, abs_of_pos hrpos, habsσ, mul_one]
    _ ≤ r * τ + τ := add_le_add (mul_le_mul_of_nonneg_left hb hrpos.le) hratio
    _ ≤ 3 * τ := by nlinarith




theorem exists_intersecting_transition_height_horizontal_bound {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ z ∈ N.cylinderDomain, N.coordinate_map z ∈ N'.carrier →
      ∀ v : TangentSpace (𝓡 2) z.1,
        |mvfderiv (𝓡 2)
          (fun q : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (q, z.2))).2)
          z.1 v| ≤ α * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
            (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) z.1 v) := by
  obtain ⟨εh, hhpos, hhcap, hhorizontal⟩ :=
    exists_intersecting_horizontal_control.{u} (η := α / 4) (by positivity)
  obtain ⟨εs, hspos, _, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1) (by norm_num)
  refine ⟨min εh εs, lt_min hhpos hspos, (min_le_left _ _).trans hhcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' z hz hx' v
  let x := N.coordinate_map z
  let u : TangentSpace (𝓡 3) x := N.scale⁻¹ •
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z (v, 0)
  let w : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) z.1 v
  let r := N.scale / N'.scale
  let c := N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x u
  have hx : x ∈ N.carrier := N.coordinate_map_mem hz
  have hu : mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x u = 0 := by
    have hz' := N.axial_mvfderiv_coordinate_tangent hz (v, 0)
    dsimp only [u]
    rw [map_smul, smul_eq_mul, hz', mul_zero]
  have hc := hhorizontal N N' (hN.trans (min_le_left _ _))
    (hN'.trans (min_le_left _ _)) x hx hx' u hu
  have hnorm := N.normalized_coordinate_horizontal_tangentNorm_le hz.2 v
  have hcbound : |c| ≤ (α / 4) * (2 * ‖w‖) :=
    hc.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hratio := (hscale N' N (hN'.trans (min_le_right _ _))
    (hN.trans (min_le_right _ _)) ⟨x, hx', hx⟩).2
  have hrpos : 0 < r := div_pos N.scale_pos N'.scale_pos
  have hr : r ≤ 2 := by linarith [(abs_lt.mp hratio).2]
  rw [N.transition_height_horizontal_deriv N' hz.2 hx' v]
  change |r * c| ≤ α * ‖w‖
  rw [abs_mul, abs_of_pos hrpos]
  calc
    r * |c| ≤ 2 * ((α / 4) * (2 * ‖w‖)) :=
      mul_le_mul hr hcbound (abs_nonneg c) (by norm_num)
    _ = α * ‖w‖ := by ring

end PoincareConjecture.EpsilonNeck
