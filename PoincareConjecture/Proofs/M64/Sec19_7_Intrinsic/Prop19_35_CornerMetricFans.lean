import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerTangentPartition

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_coordinate_corner_vertex_angle_sum
    {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hfront : ∀ i j, i ≠ j →
      (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
        frontier (F i '' convexHull ℝ (range (b i))))
    (q : AnnulusCoordinates) (hvertex : ∀ i, F i (b i 0) = q)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap q) (hzero : phi q = 0)
    (positive : Bool)
    (hregion : ∀ᶠ z in 𝓝 q,
      z ∈ ⋃ i, F i '' convexHull ℝ (range (b i)) ↔
        if positive then 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2
        else (phi z).1 ≤ 0 ∨ (phi z).2 ≤ 0) :
    (∑ i, coordinateTriangleAngle g (F i) (b i) 0) =
      if positive then g.cornerAngle q (L.symm (1, 0)) (L.symm (0, 1))
      else 2 * Real.pi - g.cornerAngle q (L.symm (1, 0)) (L.symm (0, 1)) := by
  let x (i : I) : AnnulusCoordinates := coordinateTriangleVelocity (F i) (b i) 0 1
  let y (i : I) : AnnulusCoordinates := coordinateTriangleVelocity (F i) (b i) 0 2
  let u := L.symm (1, 0)
  let v := L.symm (0, 1)
  have hu : u ≠ 0 := by
    intro h
    have hh := congrArg (fun w => (L w).1) h
    norm_num [u] at hh
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg (fun w => (L w).2) h
    norm_num [v] at hh
  have huv : g.cornerAngle q u v ∈ Ioo (0 : ℝ) Real.pi := by
    apply g.cornerAngle_mem_Ioo_of_not_smul
    intro a ha
    have hh := congrArg (fun w => (L w).2) ha
    norm_num [u, v] at hh
  have htarget (w : AnnulusCoordinates) :
      (∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • u + c • v) ↔
        0 < (L w).1 ∧ 0 < (L w).2 := by
    constructor
    · rintro ⟨a, c, ha, hc, rfl⟩
      simpa [u, v] using And.intro ha hc
    · intro hw
      refine ⟨(L w).1, (L w).2, hw.1, hw.2, ?_⟩
      apply L.injective
      simp [u, v]
  have hangle (i : I) : g.cornerAngle q (x i) (y i) =
      coordinateTriangleAngle g (F i) (b i) 0 := by
    change g.cornerAngle q (x i) (y i) = g.cornerAngle (F i (b i 0)) (x i) (y i)
    exact congrArg (fun p : AnnulusCoordinates => g.cornerAngle p (x i) (y i)) (hvertex i).symm
  have hmem (i : I) : q ∈ F i '' convexHull ℝ (range (b i)) :=
    ⟨b i 0, subset_convexHull ℝ _ (mem_range_self 0), hvertex i⟩
  have hcone (i : I) (w : AnnulusCoordinates) :
      (∀ k, (b i).coord k ((F i).symm q) = 0 →
        0 < fderiv ℝ (fun z => (b i).coord k ((F i).symm z)) q w) ↔
      ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • x i + c • y i := by
    have h := m64Intrinsic_coordinate_corner_tangent_cone (F i) (b i) (hF i) (hFi i)
      (hsource i) w
    rw [hvertex] at h
    simpa only [x, y, coordinateTriangleVelocity_eq_differential _ _ (hF i) (hsource i),
      mfderiv_eq_fderiv, TangentSpace] using h
  have hx (i : I) : x i ≠ 0 :=
    coordinateTriangleVelocity_ne_zero (F i) (b i) (hF i) (hFi i) (hsource i)
      (by decide : (0 : Fin 3) ≠ 1)
  have hy (i : I) : y i ≠ 0 :=
    coordinateTriangleVelocity_ne_zero (F i) (b i) (hF i) (hFi i) (hsource i)
      (by decide : (0 : Fin 3) ≠ 2)
  have hangles (i : I) : g.cornerAngle q (x i) (y i) ∈ Ioo (0 : ℝ) Real.pi := by
    rw [hangle]
    exact coordinateTriangleAngle_mem_Ioo g (F i) (b i) (hF i) (hFi i) (hsource i) 0
  have hpartition := m64Intrinsic_corner_tangent_partition_ae F b hF hFi hsource hfront
    L hphi hzero positive hregion
  simp only [hmem, true_and, true_implies, hcone] at hpartition
  simp_rw [← htarget] at hpartition
  cases positive
  · have hsum := m64Intrinsic_metric_reflex_fan_angle_sum g q x y u v
      hx hy hangles hu hv huv (by simpa only [Bool.false_eq_true, if_false] using hpartition)
    simpa only [hangle, Bool.false_eq_true, if_false] using hsum
  · have hsum := m64Intrinsic_metric_sector_fan_angle_sum g q x y u v
      hx hy hangles hu hv huv (by simpa only [if_true] using hpartition)
    simpa only [hangle, if_true] using hsum

end PoincareConjecture
