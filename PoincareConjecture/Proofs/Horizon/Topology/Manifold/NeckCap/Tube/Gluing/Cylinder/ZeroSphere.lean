import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Centered
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem zeroSphere_eq_of_positive_side (c : ℝ)
    (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace N.carrierOpen ∞)
    (hTside : ∀ p : RoundCylinderSpace,
      c < (N.coordinate_inverse (T p)).2 ↔ 0 < p.2) :
    range (fun q : UnitTwoSphere => (T (q, 0) : M)) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, c)) := by
  obtain ⟨K, _, hKzero, _, hKside⟩ :=
    N.exists_centered_neck_coordinates (fun _ => c) contMDiff_const (fun _ => hc)
  let e := (T.trans K.symm).toHomeomorph
  have he (p : RoundCylinderSpace) : K (e p) = T p := K.apply_symm_apply (T p)
  have hside (p : RoundCylinderSpace) : 0 < (e p).2 ↔ 0 < p.2 := by
    have h := not_congr (hKside (e p).1 (e p).2)
    simp only [not_le] at h
    rw [← h, he]
    exact hTside p
  let P : Set RoundCylinderSpace := univ ×ˢ Ioi (0 : ℝ)
  have hpre : e ⁻¹' P = P := by
    ext p
    simpa only [P, mem_preimage, mem_prod, mem_univ, mem_Ioi, true_and] using hside p
  have hfront := e.preimage_frontier P
  rw [hpre] at hfront
  have hzero (p : RoundCylinderSpace) : (e p).2 = 0 ↔ p.2 = 0 := by
    have h := Set.ext_iff.mp hfront p
    simpa only [P, mem_preimage, frontier_univ_prod_eq, frontier_Ioi,
      mem_prod, mem_univ, mem_singleton_iff, true_and] using h
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨(e (q, 0)).1, ?_⟩
    have hz := (hzero (q, 0)).2 rfl
    have hp : ((e (q, 0)).1, 0) = e (q, 0) := by
      exact Prod.ext rfl hz.symm
    change N.coordinate_map ((e (q, 0)).1, c) = (T (q, 0) : M)
    rw [← hKzero, hp, he]
  · rintro ⟨q, rfl⟩
    let p := e.symm (q, 0)
    have hep : e p = (q, 0) := e.apply_symm_apply _
    have hp : p.2 = 0 := (hzero p).1 (congrArg Prod.snd hep)
    refine ⟨p.1, ?_⟩
    have hpair : (p.1, 0) = p := Prod.ext rfl hp.symm
    change (T (p.1, 0) : M) = N.coordinate_map (q, c)
    rw [hpair, ← he, hep, hKzero]

theorem zeroSphere_eq_of_positive_tail [T2Space M] (U : Opens M) (c : ℝ)
    (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace N.carrierOpen ∞)
    (hFtail : ∀ p : RoundCylinderSpace, 0 < p.2 → (F p : M) = T p)
    (hTside : ∀ p : RoundCylinderSpace,
      c < (N.coordinate_inverse (T p)).2 ↔ 0 < p.2) :
    range (fun q : UnitTwoSphere => (F (q, 0) : M)) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, c)) := by
  have heq : EqOn (fun p => (F p : M)) (fun p => (T p : M))
      (univ ×ˢ Ioi (0 : ℝ)) := fun p hp => hFtail p hp.2
  have hzero (q : UnitTwoSphere) : (F (q, 0) : M) = T (q, 0) := by
    apply heq.closure (continuous_subtype_val.comp F.continuous)
      (continuous_subtype_val.comp T.continuous)
    simp only [closure_prod_eq, closure_univ, closure_Ioi, mem_prod, mem_univ,
      mem_Ici, le_refl, and_self]
  rw [show (fun q : UnitTwoSphere => (F (q, 0) : M)) =
    (fun q : UnitTwoSphere => (T (q, 0) : M)) from funext hzero]
  exact N.zeroSphere_eq_of_positive_side c hc T hTside

end PoincareConjecture.EpsilonNeck
