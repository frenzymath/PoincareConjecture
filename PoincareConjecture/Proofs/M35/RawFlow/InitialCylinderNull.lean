import PoincareConjecture.Proofs.M35.RawFlow.InitialCylinderCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {g : RiemannianMetric 3 StandardCapSpace} (C : StandardCylindricalEnd g)

include C

theorem initialEnd_ricci_null (D : LeviCivitaData g) (q : UnitTwoSphere)
    {s : ℝ} (hs : 0 < s) :
    ∃ v : StandardCapSpace, v ≠ 0 ∧ D.ricci (C.coordinate (q, s)) v v = 0 := by
  let p : StandardCapSpace := cylinderCoordinateEquiv.symm (0, s)
  let f := C.coordinate ∘ cylinderChart q
  let D0 := cylinderEuclideanConnection 0 (by norm_num)
  let a : StandardCapSpace := EuclideanSpace.basisFun (Fin 3) ℝ 2
  have ha : a ≠ 0 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ne_zero 2
  have hp : 0 < (cylinderCoordinateEquiv p).2 := by
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply] using hs
  have heq : f p = C.coordinate (q, s) := by
    dsimp only [f, Function.comp_def, cylinderChart, p]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    congr 1
    refine Prod.ext ?_ rfl
    change (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 = q
    rw [← sphere_chart_center q]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv (mem_chart_source _ q)
  have hnear : ∀ᶠ z : StandardCapSpace in 𝓝 p, 0 < (cylinderCoordinateEquiv z).2 :=
    (continuous_snd.comp cylinderCoordinateEquiv.continuous).continuousAt.eventually
      (eventually_gt_nhds hp)
  have hinv := hnear.mono (fun z hz => initialEndChart_mfderiv_invertible C q hz)
  have hmetric := hnear.mono (fun z hz => initialEndChart_metric C q hz)
  let v : StandardCapSpace := mfderiv (𝓡 3) (𝓡 3) f p a
  have hv : v ≠ 0 := by
    intro hz
    apply ha
    exact hinv.self_of_nhds.injective (hz.trans (map_zero _).symm)
  refine ⟨v, hv, ?_⟩
  have hricci := D0.ricci_eq_pullback_euclidean D
    (initialEndChart_contMDiffAt C q hp) hinv hmetric a a
  have hzero := cylinder_ricci_center 0 (by norm_num) D0 q s 2 2
  have hz : D0.ricci p a a = 0 := by
    change D0.ricci p a a = inner ℝ (0 : EuclideanSpace ℝ (Fin 2)) 0 at hzero
    simpa only [inner_zero_left] using hzero
  change D0.ricci p a a = D.ricci (f p) v v at hricci
  rw [heq, hz] at hricci
  exact hricci.symm

theorem initial_axis_tail_ricci_null (D : LeviCivitaData g) :
    ∃ R : ℝ, 0 < R ∧ ∀ r, R ≤ r → ∃ v : StandardCapSpace,
      v ≠ 0 ∧ D.ricci (r • EuclideanSpace.single (2 : Fin 3) 1) v v = 0 := by
  have hc : Continuous (fun q : UnitTwoSphere => C.coordinate (q, 0)) :=
    C.coordinate_smooth.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun q => ⟨mem_univ q, neg_lt_zero.mpr C.collar_pos⟩)
  let K := C.closed_core ∪ range (fun q : UnitTwoSphere => C.coordinate (q, 0))
  have hK : IsCompact K := C.core_compact.union (isCompact_range hc)
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let R := max 0 B + 1
  have hR : 0 < R := by dsimp only [R]; linarith [le_max_left (0 : ℝ) B]
  refine ⟨R, hR, ?_⟩
  intro r hr
  have hr0 : 0 < r := hR.trans_le hr
  have hrB : B < r := by dsimp only [R] at hr; linarith [le_max_right (0 : ℝ) B]
  let p : StandardCapSpace := r • EuclideanSpace.single (2 : Fin 3) 1
  have hnorm : ‖p‖ = r := by simp [p, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  have hpK : p ∉ K := by
    intro hp
    have hh := hB (mem_image_of_mem _ hp)
    rw [hnorm] at hh
    exact (not_le_of_gt hrB) hh
  have hpc : p ∈ C.carrier := by
    rw [C.carrier_eq]
    refine ⟨mem_univ _, ?_⟩
    intro hball
    apply hpK
    apply Or.inl
    rw [C.closed_core_eq]
    change g.edist 0 p < ENNReal.ofReal C.radius at hball
    exact le_of_lt hball
  have hs0 := C.inverse_domain p hpc
  have hs : 0 < (C.inverse p).2 := by
    apply lt_of_le_of_ne hs0
    intro hz
    apply hpK
    apply Or.inr
    refine ⟨(C.inverse p).1, ?_⟩
    rw [hz]
    exact C.coordinate_right_inverse hpc
  obtain ⟨v, hv, hnull⟩ := initialEnd_ricci_null C D (C.inverse p).1 hs
  refine ⟨v, hv, ?_⟩
  change D.ricci (C.coordinate (C.inverse p)) v v = 0 at hnull
  rw [C.coordinate_right_inverse hpc] at hnull
  exact hnull

end PoincareConjecture.M35.Uniqueness
