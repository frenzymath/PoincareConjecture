import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerTangentCones
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteConeFan

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory MeasureTheory.Measure InnerProductGeometry
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem exists_metric_complex_coordinates
    (g : RiemannianMetric 2 AnnulusCoordinates) (q : AnnulusCoordinates) :
    ∃ L : AnnulusCoordinates ≃ₗ[ℝ] ℂ,
      ∀ v w : AnnulusCoordinates, angle (L v) (L w) = g.cornerAngle q v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) q) = 2 :=
    finrank_euclideanSpace_fin
  let b := (g.orthonormalBasis q).reindex (finCongr hd)
  let E := b.repr.trans Complex.orthonormalBasisOneI.repr.symm
  refine ⟨E.toLinearEquiv, ?_⟩
  intro v w
  exact (E.toLinearIsometry.angle_map v w).trans
    (cornerAngle_eq_innerProduct_angle g q v w).symm

theorem m64Intrinsic_metric_fan_angle_sum
    {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates) (q : AnnulusCoordinates)
    (x y : I → AnnulusCoordinates) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hangle : ∀ i, g.cornerAngle q (x i) (y i) ∈ Ioo (0 : ℝ) Real.pi)
    (hpartition : ∀ᵐ w : AnnulusCoordinates, ∃! i, ∃ a c : ℝ,
      0 < a ∧ 0 < c ∧ w = a • x i + c • y i) :
    (∑ i, g.cornerAngle q (x i) (y i)) = 2 * Real.pi := by
  obtain ⟨L, hLangle⟩ := exists_metric_complex_coordinates g q
  let E : AnnulusCoordinates ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let T : ℂ ≃L[ℝ] ℂ := L.symm.toContinuousLinearEquiv.trans E.toContinuousLinearEquiv
  have hT : QuasiMeasurePreserving T volume volume :=
    LinearMap.quasiMeasurePreserving volume T.toLinearEquiv.toLinearMap
      T.toLinearEquiv.isUnit_det'.ne_zero
  have hpreserve : QuasiMeasurePreserving (fun z : ℂ => L.symm z) volume volume := by
    have hE : MeasurePreserving E.symm volume volume :=
      Complex.orthonormalBasisOneI.measurePreserving_repr
    have h := hE.quasiMeasurePreserving.comp hT
    have hfun : E.symm ∘ T = fun z : ℂ => L.symm z := by
      funext z
      exact E.symm_apply_apply (L.symm z)
    rw [hfun] at h
    convert h using 1
  have hcone (z : ℂ) (i : I) :
      (∃ a c : ℝ, 0 < a ∧ 0 < c ∧ L.symm z = a • x i + c • y i) ↔
      ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • L (x i) + c • L (y i) := by
    constructor
    · rintro ⟨a, c, ha, hc, heq⟩
      refine ⟨a, c, ha, hc, ?_⟩
      have h := congrArg L heq
      simpa only [L.apply_symm_apply, map_add, map_smul] using h
    · rintro ⟨a, c, ha, hc, heq⟩
      refine ⟨a, c, ha, hc, ?_⟩
      rw [heq, map_add, map_smul, map_smul, L.symm_apply_apply, L.symm_apply_apply]
  have hcomplex : ∀ᵐ z : ℂ, ∃! i, ∃ a c : ℝ,
      0 < a ∧ 0 < c ∧ z = a • L (x i) + c • L (y i) := by
    filter_upwards [hpreserve.ae hpartition] with z hz
    simpa only [hcone] using hz
  have hsum := m64Intrinsic_complex_fan_angle_sum (fun i => L (x i)) (fun i => L (y i))
    (fun i h => hx i (L.injective (h.trans L.map_zero.symm)))
    (fun i h => hy i (L.injective (h.trans L.map_zero.symm)))
    (fun i => by simpa only [hLangle] using hangle i) hcomplex
  simpa only [hLangle] using hsum

theorem m64Intrinsic_coordinate_interior_vertex_angle_sum
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
    (hq : q ∈ interior (⋃ i, F i '' convexHull ℝ (range (b i)))) :
    (∑ i, coordinateTriangleAngle g (F i) (b i) 0) = 2 * Real.pi := by
  let x (i : I) : AnnulusCoordinates := coordinateTriangleVelocity (F i) (b i) 0 1
  let y (i : I) : AnnulusCoordinates := coordinateTriangleVelocity (F i) (b i) 0 2
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
  have hpartition : ∀ᵐ w : AnnulusCoordinates, ∃! i, ∃ a c : ℝ,
      0 < a ∧ 0 < c ∧ w = a • x i + c • y i := by
    filter_upwards [m64Intrinsic_regional_tangent_partition_ae F b hF hFi hsource hfront hq]
      with w hw
    simpa only [hmem, true_and, hcone] using hw
  have hsum := m64Intrinsic_metric_fan_angle_sum g q x y
    (fun i => coordinateTriangleVelocity_ne_zero (F i) (b i) (hF i) (hFi i) (hsource i)
      (by decide : (0 : Fin 3) ≠ 1))
    (fun i => coordinateTriangleVelocity_ne_zero (F i) (b i) (hF i) (hFi i) (hsource i)
      (by decide : (0 : Fin 3) ≠ 2))
    (fun i => by
      rw [hangle]
      exact coordinateTriangleAngle_mem_Ioo g (F i) (b i) (hF i) (hFi i) (hsource i) 0)
    hpartition
  simpa only [hangle] using hsum

end PoincareConjecture
