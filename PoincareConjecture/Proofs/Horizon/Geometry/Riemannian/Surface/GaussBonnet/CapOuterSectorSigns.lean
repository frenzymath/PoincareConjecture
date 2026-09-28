import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterSectorAngles
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.ClosedConeDerivatives







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

private theorem sector_linear_coord_sub_base
    (c : AffineBasis (Fin 3) ℝ Plane) (k : Fin 3) (hk : k ≠ 0) (z : Plane) :
    (c.coord k).linear (z - c 0) = c.coord k z := by
  change (c.coord k).linear (z -ᵥ c 0) = _
  rw [(c.coord k).linearMap_vsub, vsub_eq_sub]
  simp only [AffineBasis.coord_apply, if_neg hk, sub_zero]

private theorem reflex_germ_cone_inclusion
    (c : AffineBasis (Fin 3) ℝ Plane) {E : Set Plane}
    (hE : E =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    ∀ᶠ z in 𝓝 (c 0), z ∈ E →
      z - c 0 ∈ {u | (c.coord 1).linear u ≤ 0 ∨ (c.coord 2).linear u ≤ 0} := by
  filter_upwards [hE] with z hz hmem
  have hm : c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0 := Eq.mp hz hmem
  simpa only [mem_ofPred_eq, sector_linear_coord_sub_base c 1 (by decide),
    sector_linear_coord_sub_base c 2 (by decide)] using hm

private theorem convex_germ_cone_inclusion
    (c : AffineBasis (Fin 3) ℝ Plane) {E : Set Plane}
    (hE : E =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    ∀ᶠ z in 𝓝 (c 0), z ∈ E →
      z - c 0 ∈ {u | 0 ≤ (c.coord 1).linear u ∧ 0 ≤ (c.coord 2).linear u} := by
  filter_upwards [hE] with z hz hmem
  have hm : 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z := Eq.mp hz hmem
  simpa only [mem_ofPred_eq, sector_linear_coord_sub_base c 1 (by decide),
    sector_linear_coord_sub_base c 2 (by decide)] using hm

private theorem linear_reflex_cone_closed (c : AffineBasis (Fin 3) ℝ Plane) :
    IsClosed {u | (c.coord 1).linear u ≤ 0 ∨ (c.coord 2).linear u ≤ 0} :=
  (isClosed_le (c.coord 1).linear.continuous_of_finiteDimensional continuous_const).union
    (isClosed_le (c.coord 2).linear.continuous_of_finiteDimensional continuous_const)

private theorem linear_convex_cone_closed (c : AffineBasis (Fin 3) ℝ Plane) :
    IsClosed {u | 0 ≤ (c.coord 1).linear u ∧ 0 ≤ (c.coord 2).linear u} :=
  (isClosed_le continuous_const (c.coord 1).linear.continuous_of_finiteDimensional).inter
    (isClosed_le continuous_const (c.coord 2).linear.continuous_of_finiteDimensional)

private theorem linear_reflex_cone_smul (c : AffineBasis (Fin 3) ℝ Plane)
    (r : ℝ) (hr : 0 < r) (u : Plane)
    (hu : u ∈ {u | (c.coord 1).linear u ≤ 0 ∨ (c.coord 2).linear u ≤ 0}) :
    r • u ∈ {u | (c.coord 1).linear u ≤ 0 ∨ (c.coord 2).linear u ≤ 0} := by
  simp only [mem_ofPred_eq, map_smul, smul_eq_mul] at hu ⊢
  exact hu.imp (mul_nonpos_of_nonneg_of_nonpos hr.le) (mul_nonpos_of_nonneg_of_nonpos hr.le)

private theorem linear_convex_cone_smul (c : AffineBasis (Fin 3) ℝ Plane)
    (r : ℝ) (hr : 0 < r) (u : Plane)
    (hu : u ∈ {u | 0 ≤ (c.coord 1).linear u ∧ 0 ≤ (c.coord 2).linear u}) :
    r • u ∈ {u | 0 ≤ (c.coord 1).linear u ∧ 0 ≤ (c.coord 2).linear u} := by
  simp only [mem_ofPred_eq, map_smul, smul_eq_mul] at hu ⊢
  exact ⟨mul_nonneg hr.le hu.1, mul_nonneg hr.le hu.2⟩

theorem triangle_direction_mem_closed_cone
    (b : AffineBasis (Fin 3) ℝ Plane) (G : Plane → Plane)
    (L : Plane →L[ℝ] Plane) (i : Fin 3) (hG : HasFDerivAt G L (b i))
    {A : Set Plane} (hA : IsClosed A)
    (hsmul : ∀ r : ℝ, 0 < r → ∀ v ∈ A, r • v ∈ A)
    (hnear : ∀ᶠ z in 𝓝 (G (b i)),
      z ∈ G '' convexHull ℝ (range b) → z - G (b i) ∈ A)
    {q : Plane} (hq : q ∈ convexHull ℝ (range b)) : L (q - b i) ∈ A := by
  let γ : ℝ → Plane := fun t => G (AffineMap.lineMap (b i) q t)
  have hd : HasDerivAt (fun t : ℝ => AffineMap.lineMap (b i) q t) (q - b i) 0 := by
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, one_smul, id_eq]
      using ((hasDerivAt_id (0 : ℝ)).smul_const (q - b i)).add_const (b i)
  have hγ : HasDerivAt γ (L (q - b i)) 0 :=
    hG.comp_hasDerivAt_of_eq 0 hd (by simp)
  apply deriv_mem_closed_cone_of_eventually hA hsmul hγ
  have htend : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (G (b i))) := by
    simpa only [γ, AffineMap.lineMap_apply_zero] using
      hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [htend.eventually hnear, self_mem_nhdsWithin,
    (show ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 from
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))] with t ht hpos hone
  have hmem : γ t ∈ G '' convexHull ℝ (range b) :=
    mem_image_of_mem G ((convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self i)) hq ⟨hpos.le, hone.le⟩)
  simpa only [γ, AffineMap.lineMap_apply_zero] using ht hmem

theorem triangle_positive_combination_mem_closed_cone
    (b : AffineBasis (Fin 3) ℝ Plane) (G : Plane → Plane)
    (L : Plane →L[ℝ] Plane) (i j k : Fin 3) (hG : HasFDerivAt G L (b i))
    {A : Set Plane} (hA : IsClosed A)
    (hsmul : ∀ r : ℝ, 0 < r → ∀ v ∈ A, r • v ∈ A)
    (hnear : ∀ᶠ z in 𝓝 (G (b i)),
      z ∈ G '' convexHull ℝ (range b) → z - G (b i) ∈ A)
    {s : ℝ} (hs : 0 ≤ s) : L (b j - b i) + s • L (b k - b i) ∈ A := by
  have hp : 0 < 1 + s := by linarith
  let q := AffineMap.lineMap (b j) (b k) (s / (1 + s))
  have hq : q ∈ convexHull ℝ (range b) :=
    (convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self j))
      (subset_convexHull ℝ _ (mem_range_self k))
      ⟨div_nonneg hs hp.le, (div_le_one hp).mpr (by linarith)⟩
  have h := hsmul (1 + s) hp _
    (triangle_direction_mem_closed_cone b G L i hG hA hsmul hnear hq)
  have he : (1 + s) • (q - b i) = (b j - b i) + s • (b k - b i) := by
    dsimp [q]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_sub, smul_add,
      smul_smul, mul_div_cancel₀ _ hp.ne']
    module
  rw [← map_smul, he, map_add, map_smul] at h
  exact h

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]

theorem hasFDerivAt_chart_coordinates
    (F : OpenPartialHomeomorph Plane S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (v : S) (z : Plane) (hz : z ∈ F.source)
    (hv : F z ∈ (chartAt Plane v).source) :
    HasFDerivAt (fun y => chartAt Plane v (F y))
      ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v) (F z)).comp
        (mfderiv (𝓡 2) (𝓡 2) F z)) z := by
  have hf := (hF.contMDiffAt (F.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have hc := ((mdifferentiable_chart (I := 𝓡 2) v).1 _ hv).mdifferentiableAt
    ((chartAt Plane v).open_source.mem_nhds hv)
  have hG := (hc.comp z hf).differentiableAt.hasFDerivAt
  rw [← mfderiv_eq_fderiv, mfderiv_comp z hc hf] at hG
  exact hG

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem first_outer_tangent_combination_mem_closed_cone
    (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    {A : Set Plane} (hA : IsClosed A)
    (hsmul : ∀ r : ℝ, 0 < r → ∀ u ∈ A, r • u ∈ A)
    (hnear : ∀ᶠ z in 𝓝 (chartAt Plane v (B.firstOuterTip i)),
      (chartAt Plane v).symm z ∈ ⋃ s, (B.face s).carrier →
        z - chartAt Plane v (B.firstOuterTip i) ∈ A)
    (j : Bool) {s : ℝ} (hs : 0 ≤ s) :
    -B.firstOuterChartSpoke i v +
      s • (chartAt Plane v (B.secondOuterTip j) -
        chartAt Plane v (B.firstOuterTip i)) ∈ A := by
  let F := B.coordinates (i, j)
  let C := chartAt Plane v
  let b := rightTriangleBasis B.scale_pos
  let G : Plane → Plane := fun z => C (F z)
  let L : Plane →L[ℝ] Plane := (mfderiv (𝓡 2) (𝓡 2) C (F (b 1))).comp
    (mfderiv (𝓡 2) (𝓡 2) F (b 1))
  have hb : b 1 ∈ F.source :=
    B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 1))
  have htarget {z : Plane} (hz : z ∈ convexHull ℝ (range b)) : F z ∈ C.source := by
    simpa only [hchart, C] using
      B.coordinates_target (i, j) (F.map_source (B.triangle_subset_source _ hz))
  have htip : F (b 1) = B.firstOuterTip i := B.coordinate_first_outer_tip i j
  have hc : B.firstOuterTip i ∈ C.source := htip ▸ htarget
    (subset_convexHull ℝ _ (mem_range_self 1))
  have hG : HasFDerivAt G L (b 1) := hasFDerivAt_chart_coordinates F
    (B.coordinates_smooth _) v (b 1) hb (htarget (subset_convexHull ℝ _ (mem_range_self 1)))
  have hnear' : ∀ᶠ z in 𝓝 (G (b 1)),
      z ∈ G '' convexHull ℝ (range b) → z - G (b 1) ∈ A := by
    change ∀ᶠ z in 𝓝 (C (F (b 1))),
      z ∈ G '' convexHull ℝ (range b) → z - C (F (b 1)) ∈ A
    rw [htip]
    filter_upwards [hnear] with z hz hzmem
    apply hz
    obtain ⟨q, hq, rfl⟩ := hzmem
    change C.symm (C (F q)) ∈ ⋃ s, (B.face s).carrier
    rw [C.left_inv (htarget hq)]
    apply mem_iUnion.mpr
    refine ⟨(i, j), ?_⟩
    rw [B.carrier_eq]
    exact mem_image_of_mem F hq
  have h := triangle_positive_combination_mem_closed_cone b G L 1 0 2
    hG hA hsmul hnear' hs
  let D : S → (Plane →L[ℝ] Plane) := fun q => mfderiv (𝓡 2) (𝓡 2) C q
  have hpoint := congrArg D htip
  have hL0 : L (b 0 - b 1) = -B.firstOuterChartSpoke i v := by
    change D (F (b 1)) ((mfderiv (𝓡 2) (𝓡 2) F (b 1)) (b 0 - b 1)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint, B.first_outer_inward_velocity_eq]
    simp only [firstOuterChartSpoke, firstOuterSpoke, map_neg, neg_neg, C, D]
    rfl
  have hL2 : L (b 2 - b 1) = C (B.secondOuterTip j) - C (B.firstOuterTip i) := by
    change D (F (b 1)) ((mfderiv (𝓡 2) (𝓡 2) F (b 1)) (b 2 - b 1)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint]
    change (mfderiv (𝓡 2) (𝓡 2) C (B.firstOuterTip i)) (B.firstOuterChord i j) = _
    rw [B.firstOuterChord_eq_common_chart_differential i v hchart j]
    have he := congrArg (fun M : Plane →L[ℝ] Plane =>
      M (C (B.secondOuterTip j) - C (B.firstOuterTip i)))
      ((mdifferentiable_chart (I := 𝓡 2) v).comp_symm_deriv (C.map_source hc))
    change D (C.symm (C (B.firstOuterTip i)))
      ((mfderiv (𝓡 2) (𝓡 2) C.symm (C (B.firstOuterTip i)))
        (C (B.secondOuterTip j) - C (B.firstOuterTip i))) = _ at he
    rw [congrArg D (C.left_inv hc)] at he
    exact he
  rw [hL0, hL2] at h
  exact h

theorem second_outer_tangent_combination_mem_closed_cone
    (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    {A : Set Plane} (hA : IsClosed A)
    (hsmul : ∀ r : ℝ, 0 < r → ∀ u ∈ A, r • u ∈ A)
    (hnear : ∀ᶠ z in 𝓝 (chartAt Plane v (B.secondOuterTip i)),
      (chartAt Plane v).symm z ∈ ⋃ s, (B.face s).carrier →
        z - chartAt Plane v (B.secondOuterTip i) ∈ A)
    (j : Bool) {s : ℝ} (hs : 0 ≤ s) :
    -B.secondOuterChartSpoke i v +
      s • (chartAt Plane v (B.firstOuterTip j) -
        chartAt Plane v (B.secondOuterTip i)) ∈ A := by
  let F := B.coordinates (j, i)
  let C := chartAt Plane v
  let b := rightTriangleBasis B.scale_pos
  let G : Plane → Plane := fun z => C (F z)
  let L : Plane →L[ℝ] Plane := (mfderiv (𝓡 2) (𝓡 2) C (F (b 2))).comp
    (mfderiv (𝓡 2) (𝓡 2) F (b 2))
  have hb : b 2 ∈ F.source :=
    B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 2))
  have htarget {z : Plane} (hz : z ∈ convexHull ℝ (range b)) : F z ∈ C.source := by
    simpa only [hchart, C] using
      B.coordinates_target (j, i) (F.map_source (B.triangle_subset_source _ hz))
  have htip : F (b 2) = B.secondOuterTip i := B.coordinate_second_outer_tip i j
  have hc : B.secondOuterTip i ∈ C.source := htip ▸ htarget
    (subset_convexHull ℝ _ (mem_range_self 2))
  have hG : HasFDerivAt G L (b 2) := hasFDerivAt_chart_coordinates F
    (B.coordinates_smooth _) v (b 2) hb (htarget (subset_convexHull ℝ _ (mem_range_self 2)))
  have hnear' : ∀ᶠ z in 𝓝 (G (b 2)),
      z ∈ G '' convexHull ℝ (range b) → z - G (b 2) ∈ A := by
    change ∀ᶠ z in 𝓝 (C (F (b 2))),
      z ∈ G '' convexHull ℝ (range b) → z - C (F (b 2)) ∈ A
    rw [htip]
    filter_upwards [hnear] with z hz hzmem
    apply hz
    obtain ⟨q, hq, rfl⟩ := hzmem
    change C.symm (C (F q)) ∈ ⋃ s, (B.face s).carrier
    rw [C.left_inv (htarget hq)]
    apply mem_iUnion.mpr
    refine ⟨(j, i), ?_⟩
    rw [B.carrier_eq]
    exact mem_image_of_mem F hq
  have h := triangle_positive_combination_mem_closed_cone b G L 2 0 1
    hG hA hsmul hnear' hs
  let D : S → (Plane →L[ℝ] Plane) := fun q => mfderiv (𝓡 2) (𝓡 2) C q
  have hpoint := congrArg D htip
  have hL0 : L (b 0 - b 2) = -B.secondOuterChartSpoke i v := by
    change D (F (b 2)) ((mfderiv (𝓡 2) (𝓡 2) F (b 2)) (b 0 - b 2)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint, B.second_outer_inward_velocity_eq]
    simp only [secondOuterChartSpoke, secondOuterSpoke, map_neg, neg_neg, C, D]
    rfl
  have hL1 : L (b 1 - b 2) = C (B.firstOuterTip j) - C (B.secondOuterTip i) := by
    change D (F (b 2)) ((mfderiv (𝓡 2) (𝓡 2) F (b 2)) (b 1 - b 2)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint]
    change (mfderiv (𝓡 2) (𝓡 2) C (B.secondOuterTip i)) (B.secondOuterChord i j) = _
    rw [B.secondOuterChord_eq_common_chart_differential i v hchart j]
    have he := congrArg (fun M : Plane →L[ℝ] Plane =>
      M (C (B.firstOuterTip j) - C (B.secondOuterTip i)))
      ((mdifferentiable_chart (I := 𝓡 2) v).comp_symm_deriv (C.map_source hc))
    change D (C.symm (C (B.secondOuterTip i)))
      ((mfderiv (𝓡 2) (𝓡 2) C.symm (C (B.secondOuterTip i)))
        (C (B.firstOuterTip j) - C (B.secondOuterTip i))) = _ at he
    rw [congrArg D (C.left_inv hc)] at he
    exact he
  rw [hL0, hL1] at h
  exact h

theorem firstOuterChartSpoke_nonneg_of_reflex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.secondOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.secondOuterTip true))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    0 ≤ (c.coord 1).linear (B.firstOuterChartSpoke i v) ∧
      0 ≤ (c.coord 2).linear (B.firstOuterChartSpoke i v) := by
  have hnear := reflex_germ_cone_inclusion c hcap
  rw [hc0] at hnear
  have ht (j : Bool) (s : ℝ) (hs : 0 ≤ s) :=
    B.first_outer_tangent_combination_mem_closed_cone i v hchart
      (linear_reflex_cone_closed c) (linear_reflex_cone_smul c) hnear j hs
  have he (a b : Fin 3) (ha : a ≠ 0) :
      (c.coord a).linear (c b - c 0) = if a = b then 1 else 0 := by
    rw [sector_linear_coord_sub_base c a ha, AffineBasis.coord_apply]
  have h := nonpos_coordinates_of_ray_translates (c.coord 1).linear (c.coord 2).linear
    (-B.firstOuterChartSpoke i v) (c 1 - c 0) (c 2 - c 0)
    (by simpa using he 1 1 (by decide)) (by simpa using he 2 1 (by decide))
    (by simpa using he 1 2 (by decide)) (by simpa using he 2 2 (by decide))
    (by simpa only [hc0, hc1, mem_ofPred_eq] using ht false)
    (by simpa only [hc0, hc2, mem_ofPred_eq] using ht true)
  simpa only [map_neg, neg_nonpos] using h

theorem secondOuterChartSpoke_nonneg_of_reflex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.firstOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.firstOuterTip true))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    0 ≤ (c.coord 1).linear (B.secondOuterChartSpoke i v) ∧
      0 ≤ (c.coord 2).linear (B.secondOuterChartSpoke i v) := by
  have hnear := reflex_germ_cone_inclusion c hcap
  rw [hc0] at hnear
  have ht (j : Bool) (s : ℝ) (hs : 0 ≤ s) :=
    B.second_outer_tangent_combination_mem_closed_cone i v hchart
      (linear_reflex_cone_closed c) (linear_reflex_cone_smul c) hnear j hs
  have he (a b : Fin 3) (ha : a ≠ 0) :
      (c.coord a).linear (c b - c 0) = if a = b then 1 else 0 := by
    rw [sector_linear_coord_sub_base c a ha, AffineBasis.coord_apply]
  have h := nonpos_coordinates_of_ray_translates (c.coord 1).linear (c.coord 2).linear
    (-B.secondOuterChartSpoke i v) (c 1 - c 0) (c 2 - c 0)
    (by simpa using he 1 1 (by decide)) (by simpa using he 2 1 (by decide))
    (by simpa using he 1 2 (by decide)) (by simpa using he 2 2 (by decide))
    (by simpa only [hc0, hc1, mem_ofPred_eq] using ht false)
    (by simpa only [hc0, hc2, mem_ofPred_eq] using ht true)
  simpa only [map_neg, neg_nonpos] using h

theorem firstOuterChartSpoke_nonpos_of_convex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    (c.coord 1).linear (B.firstOuterChartSpoke i v) ≤ 0 ∧
      (c.coord 2).linear (B.firstOuterChartSpoke i v) ≤ 0 := by
  have hnear := convex_germ_cone_inclusion c hcap
  rw [hc0] at hnear
  have h := B.first_outer_tangent_combination_mem_closed_cone i v hchart
    (linear_convex_cone_closed c) (linear_convex_cone_smul c) hnear false (le_rfl : (0 : ℝ) ≤ 0)
  simpa only [zero_smul, add_zero, mem_ofPred_eq, map_neg, neg_nonneg] using h

theorem secondOuterChartSpoke_nonpos_of_convex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    (c.coord 1).linear (B.secondOuterChartSpoke i v) ≤ 0 ∧
      (c.coord 2).linear (B.secondOuterChartSpoke i v) ≤ 0 := by
  have hnear := convex_germ_cone_inclusion c hcap
  rw [hc0] at hnear
  have h := B.second_outer_tangent_combination_mem_closed_cone i v hchart
    (linear_convex_cone_closed c) (linear_convex_cone_smul c) hnear false (le_rfl : (0 : ℝ) ≤ 0)
  simpa only [zero_smul, add_zero, mem_ofPred_eq, map_neg, neg_nonneg] using h

end ChartCircleArrangementVertexPatch.VertexCapFaces

end PoincareConjecture.Topology.Surface
