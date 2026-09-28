import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Parameters
import Mathlib.Analysis.Calculus.Deriv.Slope









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in


theorem mfderiv_curve_reparam_zero_of_eqOn
    {γ η : ℝ → S} {φ : ℝ → ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ 0)
    (hη : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) η 0)
    (hφ : DifferentiableAt ℝ φ 0) (hzero : φ 0 = 0)
    (heq : EqOn η (γ ∘ φ) (Icc (0 : ℝ) 1)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η 0 1 =
      deriv φ 0 • mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ 0 1 := by
  have hγ' : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ (φ 0) := by simpa only [hzero] using hγ
  have hu := (uniqueDiffOn_Icc zero_lt_one 0 (by simp)).uniqueMDiffWithinAt
  have he := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2)
    heq (by simp : (0 : ℝ) ∈ Icc 0 1)
  rw [mfderivWithin_eq_mfderiv hu hη,
    mfderivWithin_eq_mfderiv hu (hγ'.comp 0 hφ.mdifferentiableAt)] at he
  have hv := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) => L 1) he
  have hc := LeviCivitaData.mfderiv_curve_reparam hγ' hφ.hasDerivAt
  dsimp only [TangentSpace] at hc ⊢
  rw [hzero] at hc
  exact hv.trans hc

omit [IsManifold (𝓡 2) ∞ S] in


theorem coordinateTriangleVelocity_pos_smul_of_image_eq
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hG : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G G.source)
    (hGi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G.symm G.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (hc : convexHull ℝ (range c) ⊆ G.source)
    {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (himage : (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1 =
      (fun t : ℝ => G (AffineMap.lineMap (c k) (c l) t)) '' Icc (0 : ℝ) 1)
    (hpoint : F (b i) = G (c k)) :
    ∃ a : ℝ, 0 < a ∧
      coordinateTriangleVelocity G c k l = a • coordinateTriangleVelocity F b i j := by
  let γ := fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)
  let η := fun t : ℝ => G (AffineMap.lineMap (c k) (c l) t)
  let e := coordinateTriangleChart F b
  let p := standardTriangleVertex i
  let v := standardTriangleVertex j - standardTriangleVertex i
  have hmap (t : ℝ) : e.symm (p + t • v) = γ t := by
    have h := coordinateTriangleChart_side F b i j t
    simpa only [e, p, v, γ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] using h
  have hv : v ≠ 0 := by
    intro hz
    have hvertices := sub_eq_zero.mp hz
    have h := congrArg (triangleParameterEquiv b) hvertices
    rw [triangleParameterEquiv_vertex, triangleParameterEquiv_vertex] at h
    exact hij (b.ind.injective h).symm
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p + t • v ∈ e.target := by
    change p + t • v ∈ ((triangleParameterEquiv b).toHomeomorph.toOpenPartialHomeomorph.trans F).source
    refine ⟨mem_univ _, hb ?_⟩
    change triangleParameterEquiv b (p + t • v) ∈ convexHull ℝ (range b)
    have heq : p + t • v = AffineMap.lineMap (standardTriangleVertex i) (standardTriangleVertex j) t := by
      simp [p, v, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    rw [heq, triangleParameterEquiv_side]
    exact (convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self j)) ht
  have hη (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ η t :=
    (coordinateTriangle_side_velocity G c hG hGi hc k l ht).1
  obtain ⟨φ, hφ, hmaps, heq, huniq⟩ := LeviCivitaData.exists_smooth_chart_edge_parameter
    e (coordinateTriangleChart_smooth F b hFi) p v hv htarget hη
    (show MapsTo η (Icc (0 : ℝ) 1) ((fun t : ℝ => e.symm (p + t • v)) '' Icc (0 : ℝ) 1) from by
      simpa only [hmap] using (show MapsTo η (Icc (0 : ℝ) 1) (γ '' Icc (0 : ℝ) 1) from
        fun t ht => himage.symm ▸ mem_image_of_mem η ht))
  have heq' : EqOn η (γ ∘ φ) (Icc (0 : ℝ) 1) := by
    intro t ht
    simpa only [Function.comp_apply, hmap] using heq t ht
  have hzero : φ 0 = 0 := by
    apply huniq 0 (by simp) 0 (by simp)
    rw [hmap]
    simpa only [η, γ, AffineMap.lineMap_apply_zero] using hpoint.symm
  have hηinj : InjOn η (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply AffineMap.lineMap_injective ℝ (c.ind.injective.ne hkl)
    apply G.injOn
      (hc ((convex_convexHull ℝ (range c)).lineMap_mem
        (subset_convexHull ℝ _ (mem_range_self k)) (subset_convexHull ℝ _ (mem_range_self l)) hs))
      (hc ((convex_convexHull ℝ (range c)).lineMap_mem
        (subset_convexHull ℝ _ (mem_range_self k)) (subset_convexHull ℝ _ (mem_range_self l)) ht)) he
  have hφinj : InjOn φ (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply hηinj hs ht
    rw [heq' hs, heq' ht, Function.comp_apply, Function.comp_apply, he]
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn φ (Icc (0 : ℝ) 1) := by
    rcases hcont.strictMonoOn_of_injOn_Icc' zero_le_one hφinj with hm | hm
    · exact hm
    · have hn := hm (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) zero_lt_one
      have hp := (hmaps (by simp : (1 : ℝ) ∈ Icc 0 1)).1
      rw [hzero] at hn
      exact (not_lt_of_ge hp hn).elim
  have hdiff : DifferentiableAt ℝ φ 0 := (hφ 0 (by simp)).differentiableAt (by simp)
  have hnonneg : 0 ≤ deriv φ 0 := by
    have h := hmono.monotoneOn.derivWithin_nonneg (x := 0)
    rwa [hdiff.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 (by simp))] at h
  have hvelocity : coordinateTriangleVelocity G c k l =
      deriv φ 0 • coordinateTriangleVelocity F b i j :=
    mfderiv_curve_reparam_zero_of_eqOn
      ((coordinateTriangle_side_velocity F b hF hFi hb i j (by simp : (0 : ℝ) ∈ Icc 0 1)).1.mdifferentiableAt (by simp))
      ((hη 0 (by simp)).mdifferentiableAt (by simp)) hdiff hzero heq'
  have hne : deriv φ 0 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hvelocity
    exact coordinateTriangleVelocity_ne_zero G c hG hGi hc hkl hvelocity
  exact ⟨deriv φ 0, lt_of_le_of_ne hnonneg hne.symm, hvelocity⟩

section Metric

variable (g : RiemannianMetric 2 S)
  (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
  (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
  (hG : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G G.source)
  (hGi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G.symm G.target)
  (hb : convexHull ℝ (range b) ⊆ F.source)
  (hc : convexHull ℝ (range c) ⊆ G.source)
  {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
  (himage : (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1 =
    (fun t : ℝ => G (AffineMap.lineMap (c k) (c l) t)) '' Icc (0 : ℝ) 1)
  (hpoint : F (b i) = G (c k))

include hF hFi hG hGi hb hc hij hkl himage hpoint



theorem coordinateTriangleVelocity_normalize_eq_of_image_eq :
    (Real.sqrt (g.inner (G (c k)) (coordinateTriangleVelocity G c k l)
      (coordinateTriangleVelocity G c k l)))⁻¹ • coordinateTriangleVelocity G c k l =
    (Real.sqrt (g.inner (F (b i)) (coordinateTriangleVelocity F b i j)
      (coordinateTriangleVelocity F b i j)))⁻¹ • coordinateTriangleVelocity F b i j := by
  obtain ⟨a, ha, hv⟩ := coordinateTriangleVelocity_pos_smul_of_image_eq
    F G b c hF hFi hG hGi hb hc hij hkl himage hpoint
  dsimp only [TangentSpace] at hv ⊢
  rw [← hpoint, hv]
  exact g.normalize_smul_pos (F (b i)) (coordinateTriangleVelocity F b i j) ha



theorem coordinateTriangleSideUnitField_endpoint_eq_of_image_eq :
    coordinateTriangleSideUnitField g G c k l (G (c k)) =
      coordinateTriangleSideUnitField g F b i j (F (b i)) := by
  have h := coordinateTriangleVelocity_normalize_eq_of_image_eq
    g F G b c hF hFi hG hGi hb hc hij hkl himage hpoint
  rw [coordinateTriangleVelocity_eq_chartField G c hG hGi hc,
    coordinateTriangleVelocity_eq_chartField F b hF hFi hb] at h
  exact h



theorem cornerAngle_coordinateTriangleVelocity_eq_of_image_eq
    (w : TangentSpace (𝓡 2) (F (b i))) :
    g.cornerAngle (G (c k)) (coordinateTriangleVelocity G c k l) w =
      g.cornerAngle (F (b i)) (coordinateTriangleVelocity F b i j) w := by
  obtain ⟨a, ha, hv⟩ := coordinateTriangleVelocity_pos_smul_of_image_eq
    F G b c hF hFi hG hGi hb hc hij hkl himage hpoint
  dsimp only [TangentSpace] at hv w ⊢
  rw [← hpoint, hv]
  exact g.cornerAngle_smul_pos_left _ _ _ ha


theorem cornerAngle_coordinateTriangleVelocity_eq_of_image_eq_right
    (w : TangentSpace (𝓡 2) (F (b i))) :
    g.cornerAngle (G (c k)) w (coordinateTriangleVelocity G c k l) =
      g.cornerAngle (F (b i)) w (coordinateTriangleVelocity F b i j) := by
  rw [g.cornerAngle_comm (G (c k)), g.cornerAngle_comm (F (b i))]
  exact cornerAngle_coordinateTriangleVelocity_eq_of_image_eq
    g F G b c hF hFi hG hGi hb hc hij hkl himage hpoint w

end Metric

end PoincareConjecture.Topology.Surface
