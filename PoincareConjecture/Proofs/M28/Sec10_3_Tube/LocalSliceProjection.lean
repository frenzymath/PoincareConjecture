import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalAxialTransition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem coordinate_inverse_mfderiv_map_prod_m28 (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) (v : RoundCylinderTangent z) :
    mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) = v := by
  have hh := mfderiv_comp z
    ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds (N.coordinate_map_mem hz))).mdifferentiableAt (by simp))
    ((N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp))
  have heq : N.coordinate_inverse ∘ N.coordinate_map =ᶠ[𝓝 z] id := by
    filter_upwards [N.cylinderDomain_open.mem_nhds hz] with y hy
    exact N.coordinate_inverse_coordinate_map hy
  rw [heq.mfderiv_eq, mfderiv_id] at hh
  exact (congrArg (fun L => L v) hh).symm

theorem coordinateSlice_contMDiff_m28 (N : EpsilonNeck g) {a : ℝ}
    (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q : UnitTwoSphere => N.coordinate_map (q, a)) := by
  intro q
  exact (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds ⟨mem_univ q, ha⟩)).comp q
    (contMDiffAt_id.prodMk contMDiffAt_const)

private theorem coordinateSlice_projection_mfderiv (N N' : EpsilonNeck g)
    (q : UnitTwoSphere) {a : ℝ} (ha : a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hx : N'.coordinate_map (q, a) ∈ N.carrier) (v : TangentSpace (𝓡 2) q) :
    mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, a))).1) q v =
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse
        (N'.coordinate_map (q, a))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (q, a) (v, 0))).1 := by
  have hmap := (N'.coordinate_map_smooth.contMDiffAt
    (N'.cylinderDomain_open.mem_nhds
      (show (q, a) ∈ N'.cylinderDomain from ⟨mem_univ _, ha⟩))).mdifferentiableAt (by simp)
  have hinv := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hpair := (hasMFDerivAt_id (I := 𝓡 2) q).prodMk
    (hasMFDerivAt_const (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) a q)
  have hcomp := hinv.hasMFDerivAt.comp q (hmap.hasMFDerivAt.comp q hpair)
  have hfst := (hasMFDerivAt_fst (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))
    (N.coordinate_inverse (N'.coordinate_map (q, a)))).comp q hcomp
  exact congrArg (fun L => L v) hfst.mfderiv

theorem exists_contained_coordinate_slice_graph_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
        ∀ {a : ℝ}, a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
        (∀ q : UnitTwoSphere, N'.coordinate_map (q, a) ∈ N.carrier) →
          ∃ h : UnitTwoSphere → ℝ, Continuous h ∧
            (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
            range (fun q : UnitTwoSphere => N'.coordinate_map (q, a)) =
              range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨ε₀, hε₀, hsmall, hbounds⟩ := exists_axial_transition_bounds_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' a ha hmem
  apply N.exists_continuous_graph_of_isLocalHomeomorph
    (fun q : UnitTwoSphere => N'.coordinate_map (q, a))
    (N'.coordinateSlice_contMDiff_m28 ha).continuous hmem
  apply IsLocalDiffeomorph.isLocalHomeomorph (I := 𝓡 2) (J := 𝓡 2) (n := ∞)
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv
  · have hinv : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : UnitTwoSphere => N.coordinate_inverse (N'.coordinate_map (q, a))) := by
      intro q
      exact (N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (hmem q))).comp q (N'.coordinateSlice_contMDiff_m28 ha q)
    exact contMDiff_fst.comp hinv
  · intro q
    let A := mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, a))).1) q
    have hinj : Function.Injective A := by
      apply (injective_iff_map_eq_zero A).mpr
      intro v hv
      let x := N'.coordinate_map (q, a)
      let z := N.coordinate_inverse x
      let w := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (q, a) (v, 0)
      let u := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
      let B := (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N'.coordinate_inverse x).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z)
      have hx : x ∈ N.carrier := hmem q
      have hz' : (q, a) ∈ N'.cylinderDomain := ⟨mem_univ _, ha⟩
      have hu : u.1 = 0 := by
        have h := N.coordinateSlice_projection_mfderiv N' q ha hx v
        exact h.symm.trans hv
      have hback : B u = (v, 0) := by
        change mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N'.coordinate_inverse x
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u) = _
        rw [N.coordinate_map_mfderiv_inverse_prod hx w]
        exact N'.coordinate_inverse_mfderiv_map_prod_m28 hz' (v, 0)
      have hB : (B (0, 1)).2 ≠ 0 := by
        have h := (hbounds N' N hN' hN x ⟨N'.coordinate_map_mem hz', hx⟩).1
        change (0.9 : ℝ) ≤ |(B (0, 1)).2| at h
        intro heq
        rw [heq, abs_zero] at h
        norm_num at h
      have hueq : u = u.2 • (0, 1) := by
        change u = (u.2 • (0 : EuclideanSpace ℝ (Fin 2)), u.2 * (1 : ℝ))
        simp only [smul_zero, mul_one]
        apply Prod.ext
        · exact hu
        · rfl
      have hprod : u.2 * (B (0, 1)).2 = 0 := by
        have h := congrArg Prod.snd hback
        rw [hueq, map_smul] at h
        exact h
      have hu2 : u.2 = 0 := (mul_eq_zero.mp hprod).resolve_right hB
      have huzero : u = 0 := Prod.ext hu hu2
      rw [huzero, map_zero] at hback
      exact (congrArg Prod.fst hback).symm
    let : FiniteDimensional ℝ (TangentSpace (𝓡 2) q) := by
      unfold TangentSpace
      infer_instance
    exact ⟨hinj, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj⟩

end PoincareConjecture.EpsilonNeck
