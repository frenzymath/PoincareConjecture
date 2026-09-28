import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialTransversality
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SphereProjection
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem coordinate_map_mfderiv_injective (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) :
    Function.Injective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z) := by
  let Φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace M ∞ := {
    toPartialEquiv := N.coordinatePartialHomeomorph.toPartialEquiv
    open_source := N.cylinderDomain_open
    open_target := N.carrier_open
    contMDiffOn_toFun := N.coordinate_map_smooth
    contMDiffOn_invFun := N.coordinate_inverse_smooth }
  have hΦ := Φ.isLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ hz
  exact (hΦ.mfderivToContinuousLinearEquiv (by simp)).injective



theorem coordinate_product_mfderiv_right_inverse (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) = v := by
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds (N.coordinate_inverse_mem x hx))).mdifferentiableAt
      (by simp)
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have heq : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[𝓝 x] id := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.coordinate_map_coordinate_inverse hy
  have hcomp := mfderiv_comp x hm hi
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (congrArg (fun L => L v) hcomp).symm




theorem slice_projection_isLocalDiffeomorph_of_transverse
    (N N' : EpsilonNeck g) {t : ℝ} (ht : t ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hsub : ∀ q : UnitTwoSphere, N'.coordinate_map (q, t) ∈ N.carrier)
    (htrans : ∀ q : UnitTwoSphere,
      mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
        (N'.coordinate_map (q, t))
        (N.normalizedAxialVector (N'.coordinate_map (q, t))) ≠ 0) :
    IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞
      (fun q : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (q, t))).1) := by
  have hj := (N'.coordinate_slice_isSmoothEmbedding ht).contMDiff
  have hc := N.coordinate_inverse_smooth.comp_contMDiff hj hsub
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv
    (contMDiff_fst.comp hc)
  intro q
  let x := N'.coordinate_map (q, t)
  let B : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (q, t)
  let C : EuclideanSpace ℝ (Fin 3) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x
  let A : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
  let D := mfderiv (𝓡 2) (𝓡 2)
    (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, t))).1) q
  have hinj : Function.Injective D := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hm := (N'.coordinate_map_smooth.contMDiffAt
      (N'.cylinderDomain_open.mem_nhds
        (show (q, t) ∈ N'.cylinderDomain from ⟨mem_univ q, ht⟩))).mdifferentiableAt (by simp)
    have hi := (N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds (hsub q))).mdifferentiableAt (by simp)
    have hpair : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (fun p : UnitTwoSphere => (p, t)) q :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hfirst : (C (B (v, 0))).1 = 0 := by
      have hd : D v = (C (B (v, 0))).1 := by
        change (mfderiv (𝓡 2) (𝓡 2)
          (Prod.fst ∘ (N.coordinate_inverse ∘
            (N'.coordinate_map ∘ (fun p : UnitTwoSphere => (p, t))))) q) v = _
        rw [mfderiv_comp q mdifferentiableAt_fst (hi.comp q (hm.comp q hpair)),
          mfderiv_comp q hi (hm.comp q hpair), mfderiv_comp q hm hpair,
          mfderiv_prod_left, mfderiv_fst]
        rfl
      exact hd.symm.trans hv
    let c : ℝ := (C (B (v, 0))).2
    have hCu : C (B (v, 0)) = (0, c) := Prod.ext hfirst rfl
    have hu : B (v, 0) = (c * N.scale) • N.normalizedAxialVector x := by
      calc
        B (v, 0) = A (C (B (v, 0))) :=
          (N.coordinate_product_mfderiv_right_inverse (hsub q) (B (v, 0))).symm
        _ = A (0, c) := congrArg A hCu
        _ = c • A (0, 1) := by rw [← map_smul]; simp
        _ = (c * N.scale) • N.normalizedAxialVector x := by
          change c • A (0, 1) = (c * N.scale) • (N.scale⁻¹ • A (0, 1))
          rw [smul_smul, mul_assoc, mul_inv_cancel₀ N.scale_pos.ne', mul_one]
    have hz := N'.axial_mvfderiv_coordinate_tangent (z := (q, t)) ⟨mem_univ q, ht⟩ (v, 0)
    change mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x (B (v, 0)) = 0 at hz
    rw [hu, map_smul, smul_eq_mul] at hz
    have hc0 : c = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
      (htrans q))).resolve_right N.scale_pos.ne'
    have hu0 : B (v, 0) = 0 := by rw [hu, hc0, zero_mul, zero_smul]
    have hv0 : (v, (0 : ℝ)) = 0 :=
      N'.coordinate_map_mfderiv_injective ⟨mem_univ q, ht⟩ (hu0.trans B.map_zero.symm)
    exact congrArg Prod.fst hv0
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp hinj⟩




theorem exists_contained_slice_graph :
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
          range (fun q => N'.coordinate_map (q, t))) ∧
      SmoothSphereIsotopicIn N.carrier N.central_sphere
        (range (fun q => N'.coordinate_map (q, t))) := by
  obtain ⟨epsilon0, hpos, hcap, htrans⟩ := exists_intersecting_axial_transversality.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' t ht hsub
  have hlocal := N.slice_projection_isLocalDiffeomorph_of_transverse N' ht hsub
    (fun q => (htrans N N' hN hN' (N'.coordinate_map (q, t)) (hsub q)
      (N'.coordinate_map_mem ⟨mem_univ q, ht⟩)).1)
  exact ⟨N.exists_coordinate_graph_of_slice_projection_localDiffeomorph N' ht hsub hlocal,
    N.slice_isotopic_of_projection_localDiffeomorph N' ht hsub hlocal⟩




theorem exists_contained_sphere_isotopy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      N'.central_sphere ⊆ N.carrier →
      SmoothSphereIsotopicIn N.carrier N.central_sphere N'.central_sphere := by
  obtain ⟨epsilon0, hpos, hcap, hgraph⟩ := exists_contained_slice_graph.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hsub
  have hslice (q : UnitTwoSphere) : N'.coordinate_map (q, 0) ∈ N.carrier := by
    apply hsub
    rw [← N'.coordinate_zero_range]
    exact mem_range_self q
  have hi := (hgraph N N' hN hN' 0 N'.zero_mem_interval hslice).2
  rwa [N'.coordinate_zero_range] at hi

end PoincareConjecture.EpsilonNeck
