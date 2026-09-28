import PoincareConjecture.Proofs.M25.AppA_1_Necks.HorizontalControl
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SphereContainment












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem normalized_coordinate_horizontal_tangentNorm_le
    [MeasurableSpace M] [BorelSpace M] [T3Space M] (N : EpsilonNeck g)
    {q : UnitTwoSphere} {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : TangentSpace (𝓡 2) q) :
    g.tangentNorm (N.coordinate_map (q, s))
      (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (q, s) (v, 0)) ≤
      2 * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
        (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let w : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v
  have h := (abs_le.mp (N.normalized_pullback_quadratic_error
    (z := (q, s)) hs (v, 0))).2
  have hmodel : EvolvingRoundCylinderMetric 0 (q, s) (v, 0) (v, 0) = 2 * ‖w‖ ^ 2 := by
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one, zero_mul, add_zero]
    change 2 * inner ℝ w w = 2 * ‖w‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  rw [hmodel] at h
  have hnorm : g.inner (N.coordinate_map (q, s))
      (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (q, s) (v, 0))
      (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (q, s) (v, 0)) ≤ (2 * ‖w‖) ^ 2 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    change N.scale⁻¹ * (N.scale⁻¹ * roundCylinderPullback g N.coordinate_map
      (q, s) (v, 0) (v, 0)) ≤ _
    have hsmall := mul_le_mul_of_nonneg_right N.epsilon_lt_half.le (sq_nonneg ‖w‖)
    dsimp only [normalized_pullback] at h
    nlinarith
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hnorm⟩




theorem coordinate_graph_axial_identity (N N' : EpsilonNeck g)
    {h : UnitTwoSphere → ℝ} (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hsub : ∀ q, N.coordinate_map (q, h q) ∈ N'.carrier)
    {t : ℝ} (hheight : ∀ q, (N'.coordinate_inverse (N.coordinate_map (q, h q))).2 = t)
    (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
    N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
      (N.coordinate_map (q, h q))
      (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (q, h q) (v, 0)) +
      mvfderiv (𝓡 2) h q v * (N'.scale *
        mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
          (N.coordinate_map (q, h q))
          (N.normalizedAxialVector (N.coordinate_map (q, h q)))) = 0 := by
  let D : RoundCylinderSpace → (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
    fun z => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z
  let L := mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
    (N.coordinate_map (q, h q))
  let d := mvfderiv (𝓡 2) h q v
  have hp : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : UnitTwoSphere => (p, h p)) q :=
    mdifferentiableAt_id.prodMk (hsmooth.mdifferentiable (by simp) q)
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds
      (show (q, h q) ∈ N.cylinderDomain from ⟨mem_univ q, hdom q⟩))).mdifferentiableAt
        (by simp)
  have hi := (N'.coordinate_inverse_smooth.contMDiffAt
    (N'.carrier_open.mem_nhds (hsub q))).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      (fun y => (N'.coordinate_inverse y).2) (N.coordinate_map (q, h q)) :=
    mdifferentiableAt_snd.comp (N.coordinate_map (q, h q)) hi
  have hpair : mfderiv (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : UnitTwoSphere => (p, h p)) q v = (v, d) := by
    have hd := mfderiv_prodMk (I' := 𝓡 2) mdifferentiableAt_id
      (hsmooth.mdifferentiable (by simp) q)
    change mfderiv (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : UnitTwoSphere => (p, h p)) q = _ at hd
    rw [hd, mfderiv_id]
    rfl
  have hzero : L (D (q, h q) (v, d)) = 0 := by
    have hc : (fun p : UnitTwoSphere =>
        (N'.coordinate_inverse (N.coordinate_map (p, h p))).2) = fun _ => t :=
      funext hheight
    have hz : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (p, h p))).2)
        q v = 0 := by rw [hc, mfderiv_const]; rfl
    change (mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      ((fun y => (N'.coordinate_inverse y).2) ∘
        (N.coordinate_map ∘ (fun p : UnitTwoSphere => (p, h p)))) q) v = 0 at hz
    rw [mfderiv_comp q hl (hm.comp q hp), mfderiv_comp q hm hp] at hz
    change L (D (q, h q) (mfderiv (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : UnitTwoSphere => (p, h p)) q v)) = 0 at hz
    rw [hpair] at hz
    exact hz
  have hsplit : L (D (q, h q) (v, 0)) + d * L (D (q, h q) (0, 1)) = 0 := by
    have heq : (v, d) = (v, (0 : ℝ)) + d • (0, (1 : ℝ)) := by simp
    rw [heq, map_add, map_smul, map_add, map_smul, smul_eq_mul] at hzero
    exact hzero
  have ha : (N.normalizedAxialVector (N.coordinate_map (q, h q)) :
      EuclideanSpace ℝ (Fin 3)) = N.scale⁻¹ • D (q, h q) (0, 1) := by
    change N.scale⁻¹ • D (N.coordinate_inverse (N.coordinate_map (q, h q))) (0, 1) = _
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ q, hdom q⟩]
  change N'.scale * L (N.scale⁻¹ • D (q, h q) (v, 0)) +
    d * (N'.scale * L (N.normalizedAxialVector (N.coordinate_map (q, h q)))) = 0
  rw [ha, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  calc
    _ = (N'.scale * N.scale⁻¹) *
        (L (D (q, h q) (v, 0)) + d * L (D (q, h q) (0, 1))) := by ring
    _ = 0 := by rw [hsplit, mul_zero]





theorem exists_coordinate_graph_slope_bound {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h →
      (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) →
      (∀ q, N.coordinate_map (q, h q) ∈ N'.carrier) →
      ∀ t : ℝ, (∀ q, (N'.coordinate_inverse (N.coordinate_map (q, h q))).2 = t) →
      ∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
        |mvfderiv (𝓡 2) h q v| ≤ α * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
          (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v) := by
  obtain ⟨εh, hhpos, hhcap, hhorizontal⟩ :=
    exists_intersecting_horizontal_control.{u} (η := α / 4) (by positivity)
  obtain ⟨εa, hapos, _, haxis⟩ :=
    exists_intersecting_axial_derivative_control.{u} (η := 1 / 2) (by norm_num)
  refine ⟨min εh εa, lt_min hhpos hapos, (min_le_left _ _).trans hhcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' h hsmooth hdom hsub t hheight q v
  let x := N.coordinate_map (q, h q)
  let u : TangentSpace (𝓡 3) x := N.scale⁻¹ •
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, h q) (v, 0)
  let d := mvfderiv (𝓡 2) h q v
  let b := N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x
    (N.normalizedAxialVector x)
  let c := N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x u
  let w : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v
  have hx : x ∈ N.carrier := N.coordinate_map_mem ⟨mem_univ q, hdom q⟩
  have hu : mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x u = 0 := by
    have hz := N.axial_mvfderiv_coordinate_tangent
      (z := (q, h q)) ⟨mem_univ q, hdom q⟩ (v, 0)
    dsimp only [u]
    rw [map_smul, smul_eq_mul, hz, mul_zero]
  have hc := hhorizontal N N' (hN.trans (min_le_left _ _))
    (hN'.trans (min_le_left _ _)) x hx (hsub q) u hu
  have hnorm := N.normalized_coordinate_horizontal_tangentNorm_le (hdom q) v
  have hcbound : |c| ≤ (α / 4) * (2 * ‖w‖) :=
    hc.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  obtain ⟨σ, hσ, hclose⟩ := haxis N N' (hN.trans (min_le_right _ _))
    (hN'.trans (min_le_right _ _)) x hx (hsub q)
  have habsσ : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hclose' : |1 - σ * b| < (1 : ℝ) / 2 := by
    simpa only [b, mul_assoc] using hclose
  have htriangle : 1 ≤ |1 - σ * b| + |b| := by
    calc
      1 = |(1 - σ * b) + σ * b| := by ring_nf; norm_num
      _ ≤ |1 - σ * b| + |σ * b| := abs_add_le _ _
      _ = _ := by rw [abs_mul, habsσ, one_mul]
  have hb : (1 : ℝ) / 2 < |b| := by linarith
  have heq : c + d * b = 0 :=
    N.coordinate_graph_axial_identity N' hsmooth hdom hsub hheight q v
  have habs : |d| * |b| = |c| := by
    rw [← abs_mul, show d * b = -c by linarith, abs_neg]
  have hhalf : |d| * (1 / 2) ≤ |c| := by
    rw [← habs]
    exact mul_le_mul_of_nonneg_left hb.le (abs_nonneg d)
  change |d| ≤ α * ‖w‖
  nlinarith





theorem exists_contained_slice_graph_with_slope {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ t ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹,
      (∀ q : UnitTwoSphere, N'.coordinate_map (q, t) ∈ N.carrier) →
      (∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
        range (fun q => N.coordinate_map (q, h q)) =
          range (fun q => N'.coordinate_map (q, t)) ∧
        ∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
          |mvfderiv (𝓡 2) h q v| ≤ α * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
            (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v)) ∧
      SmoothSphereIsotopicIn N.carrier N.central_sphere
        (range (fun q => N'.coordinate_map (q, t))) := by
  obtain ⟨εg, hgpos, hgcap, hgraph⟩ := exists_contained_slice_graph.{u}
  obtain ⟨εs, hspos, _, hslope⟩ := exists_coordinate_graph_slope_bound.{u} hα
  refine ⟨min εg εs, lt_min hgpos hspos, (min_le_left _ _).trans hgcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' t ht hsub
  obtain ⟨⟨h, hsmooth, hdom, hrange⟩, hisotopy⟩ := hgraph N N'
    (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _)) t ht hsub
  have hpoint (q : UnitTwoSphere) : N.coordinate_map (q, h q) ∈ N'.carrier ∧
      (N'.coordinate_inverse (N.coordinate_map (q, h q))).2 = t := by
    have hmem : N.coordinate_map (q, h q) ∈ range (fun q => N'.coordinate_map (q, t)) :=
      hrange ▸ mem_range_self q
    obtain ⟨p, hp⟩ := hmem
    rw [← hp]
    exact ⟨N'.coordinate_map_mem ⟨mem_univ p, ht⟩,
      congrArg Prod.snd (N'.coordinate_inverse_coordinate_map ⟨mem_univ p, ht⟩)⟩
  exact ⟨⟨h, hsmooth, hdom, hrange, hslope N N'
    (hN.trans (min_le_right _ _)) (hN'.trans (min_le_right _ _)) h hsmooth hdom
    (fun q => (hpoint q).1) t (fun q => (hpoint q).2)⟩, hisotopy⟩





theorem exists_middle_central_sphere_graph_with_slope
    {α κ : ℝ} (hα : 0 < α) (hκ : κ ∈ Ioc 0 1) :
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
        range (fun q => N.coordinate_map (q, h q)) = N'.central_sphere ∧
        ∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
          |mvfderiv (𝓡 2) h q v| ≤ α * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
            (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v)) ∧
      SmoothSphereIsotopicIn N.carrier N.central_sphere N'.central_sphere := by
  obtain ⟨εc, hcpos, hccap, hcontains⟩ := exists_middle_central_sphere_containment.{u} hκ
  obtain ⟨εg, hgpos, _, hgraph⟩ := exists_contained_slice_graph_with_slope.{u} hα
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
