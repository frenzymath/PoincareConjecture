import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.TruncatedDomain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SliceProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem truncated_closed_core_height_iff (C : CapCertificate g) {a : ℝ}
    (ha : -C.epsilon⁻¹ < a) {x : M} (hx : x ∈ C.end_neck.carrier) :
    x ∈ C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a) ↔
      (C.end_neck.coordinate_inverse x).2 ≤ a := by
  have himage : C.end_neck.coordinatePartialHomeomorph.symm.IsImage
      (C.end_neck.region (-C.epsilon⁻¹) a)
      ((univ : Set UnitTwoSphere) ×ˢ Ioo (-C.epsilon⁻¹) a) := by
    intro y hy
    change (C.end_neck.coordinate_inverse y).1 ∈ univ ∧
      (C.end_neck.coordinate_inverse y).2 ∈ Ioo (-C.epsilon⁻¹) a ↔
        y ∈ C.end_neck.carrier ∧ -C.epsilon⁻¹ < (C.end_neck.coordinate_inverse y).2 ∧
          (C.end_neck.coordinate_inverse y).2 < a
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ C.end_neck.carrier from hy]
  have hh := himage.closure.apply_mem_iff hx
  change C.end_neck.coordinate_inverse x ∈ closure
    ((univ : Set UnitTwoSphere) ×ˢ Ioo (-C.epsilon⁻¹) a) ↔
      x ∈ closure (C.end_neck.region (-C.epsilon⁻¹) a) at hh
  have hlo : -C.epsilon⁻¹ ≤ (C.end_neck.coordinate_inverse x).2 := by
    simpa only [C.end_neck_epsilon] using (C.end_neck.coordinate_inverse_mem x hx).2.1.le
  have hcore : x ∉ C.closed_core := fun hc =>
    disjoint_left.mp C.disjoint_closed_core_end hc hx
  simpa only [mem_union, hcore, false_or, closure_prod_eq, closure_univ,
    closure_Ioo ha.ne, mem_prod, mem_univ, true_and, mem_Icc, hlo] using hh.symm

theorem truncated_core_local_defining_function (C : CapCertificate g) {a b : ℝ}
    (ha : -C.epsilon⁻¹ < a) (hab : a < b) (hb : b < C.epsilon⁻¹)
    {x : M} (hx : x ∈ range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, a))) :
    ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧
        U ⊆ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b ∧
        (∀ y ∈ U, y ∈ C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a) ↔
          f y ≤ 0) ∧ f x = 0 ∧
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
        ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) f x d ≠ 0 := by
  obtain ⟨q, rfl⟩ := hx
  let N := C.end_neck
  let z : RoundCylinderSpace := (q, a)
  let x := N.coordinate_map z
  let f : M → ℝ := fun y => (N.coordinate_inverse y).2 - a
  let U := N.region (-C.epsilon⁻¹) b
  have hz : z ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    simpa only [N, z, C.end_neck_epsilon, mem_Ioo] using And.intro ha (hab.trans hb)
  have hxN : x ∈ N.carrier := N.coordinate_map_mem hz
  have hcoord : N.coordinate_inverse x = z := N.coordinate_inverse_coordinate_map hz
  have hxU : x ∈ U := ⟨hxN, by rw [hcoord]; exact ⟨ha, hab⟩⟩
  have hf : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f N.carrier :=
    (contMDiff_snd.comp_contMDiffOn N.coordinate_inverse_smooth).sub contMDiffOn_const
  refine ⟨U, f, N.isOpen_region _ _, hxU, fun _ hy => Or.inr hy, ?_, ?_,
    hf.mono (fun _ hy => hy.1), ?_⟩
  · intro y hy
    rw [C.truncated_closed_core_height_iff ha hy.1]
    exact (sub_nonpos : (N.coordinate_inverse y).2 - a ≤ 0 ↔ _).symm
  · change (N.coordinate_inverse x).2 - a = 0
    rw [hcoord]
    exact sub_self _
  · let v : RoundCylinderTangent z := (0, 1)
    let d : TangentSpace (𝓡 3) x :=
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v
    have hi := (N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hxN)).mdifferentiableAt (by simp)
    have hheight : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
        (Prod.snd ∘ N.coordinate_inverse) x := mdifferentiableAt_snd.comp x hi
    have hd : mvfderiv (𝓡 3) f x d = 1 := by
      change mvfderiv (𝓡 3) ((Prod.snd ∘ N.coordinate_inverse) - fun _ => a) x d = 1
      rw [mvfderiv_sub hheight mdifferentiableAt_const, mvfderiv_const]
      simp only [sub_zero]
      rw [mvfderiv, mfderiv_comp x mdifferentiableAt_snd hi, mfderiv_snd]
      change (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x d).2 = 1
      exact congrArg Prod.snd (N.coordinate_inverse_mfderiv_map_prod hz v)
    refine ⟨d, ?_, by rw [hd]; norm_num⟩
    intro hd0
    rw [hd0, map_zero] at hd
    norm_num at hd

end PoincareConjecture.CapCertificate
