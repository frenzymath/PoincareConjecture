import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.Proper
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.Vertical
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

def overlapCoordinateDomain (N P : EpsilonNeck g) : Set RoundCylinderSpace :=
  N.cylinderDomain ∩ N.coordinate_map ⁻¹' P.carrier

theorem overlapCoordinateDomain_isOpen (N P : EpsilonNeck g) :
    IsOpen (N.overlapCoordinateDomain P) :=
  N.coordinate_map_smooth.continuousOn.isOpen_inter_preimage N.cylinderDomain_open P.carrier_open

def overlapBarrierCoordinate (N Q : EpsilonNeck g) (z : RoundCylinderSpace) : ℝ :=
  (N.epsilon⁻¹ - (N.coordinate_inverse (Q.coordinate_map z)).2)⁻¹ -
    (Q.epsilon⁻¹ + z.2)⁻¹

theorem overlapBarrierCoordinate_contMDiffAt (N Q : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ Q.overlapCoordinateDomain N) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (N.overlapBarrierCoordinate Q) z := by
  have hmap := Q.coordinate_map_smooth.contMDiffAt (Q.cylinderDomain_open.mem_nhds hz.1)
  have htrans := contMDiffAt_snd.comp z
    ((N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hz.2)).comp z hmap)
  have hN : N.epsilon⁻¹ - (N.coordinate_inverse (Q.coordinate_map z)).2 ≠ 0 := by
    have h := (N.coordinate_inverse_mem _ hz.2).2.2
    linarith
  have hQ : Q.epsilon⁻¹ + z.2 ≠ 0 := by linarith [hz.1.2.1]
  exact ((contMDiffAt_const.sub htrans).inv₀ hN).sub
    ((contMDiffAt_const.add contMDiffAt_snd).inv₀ hQ)

theorem overlapBarrierCoordinate_hasDerivAt (N Q : EpsilonNeck g) (q : UnitTwoSphere)
    {t : ℝ} (ht : (q, t) ∈ Q.overlapCoordinateDomain N) :
    HasDerivAt (fun s => N.overlapBarrierCoordinate Q (q, s))
      (deriv (fun s => (N.coordinate_inverse (Q.coordinate_map (q, s))).2) t /
          (N.epsilon⁻¹ - (N.coordinate_inverse (Q.coordinate_map (q, t))).2) ^ 2 +
        1 / (Q.epsilon⁻¹ + t) ^ 2) t := by
  have hd := ((N.transition_axis_contDiffAt Q q ht.1.2 ht.2).differentiableAt
    (by simp)).hasDerivAt
  have hN : N.epsilon⁻¹ - (N.coordinate_inverse (Q.coordinate_map (q, t))).2 ≠ 0 := by
    have h := (N.coordinate_inverse_mem _ ht.2).2.2
    linarith
  have hQ : Q.epsilon⁻¹ + t ≠ 0 := by linarith [ht.1.2.1]
  have hleft := ((hasDerivAt_const t N.epsilon⁻¹).sub hd).inv hN
  have hright := ((hasDerivAt_id t).const_add Q.epsilon⁻¹).inv hQ
  convert hleft.sub hright using 1
  all_goals first | rfl | simp [div_eq_mul_inv]

theorem overlapBarrierCoordinate_deriv_pos (N Q : EpsilonNeck g) (q : UnitTwoSphere)
    {t : ℝ} (ht : (q, t) ∈ Q.overlapCoordinateDomain N)
    (hpositive : 0 < deriv (fun s => (N.coordinate_inverse (Q.coordinate_map (q, s))).2) t) :
    0 < deriv (fun s => N.overlapBarrierCoordinate Q (q, s)) t := by
  rw [(N.overlapBarrierCoordinate_hasDerivAt Q q ht).deriv]
  have hN : N.epsilon⁻¹ - (N.coordinate_inverse (Q.coordinate_map (q, t))).2 ≠ 0 := by
    have h := (N.coordinate_inverse_mem _ ht.2).2.2
    linarith
  have hQ : Q.epsilon⁻¹ + t ≠ 0 := by linarith [ht.1.2.1]
  exact add_pos (div_pos hpositive (sq_pos_of_ne_zero hN))
    (div_pos zero_lt_one (sq_pos_of_ne_zero hQ))

theorem overlapBarrierCoordinate_isLocalDiffeomorphOn (N Q : EpsilonNeck g)
    (hpositive : ∀ z ∈ Q.overlapCoordinateDomain N,
      0 < deriv (fun t => (N.coordinate_inverse (Q.coordinate_map (z.1, t))).2) z.2) :
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun z => (z.1, N.overlapBarrierCoordinate Q z)) (Q.overlapCoordinateDomain N) := by
  apply CylinderGluing.vertical_isLocalDiffeomorphOn _ (Q.overlapCoordinateDomain_isOpen N)
    (fun z hz => (N.overlapBarrierCoordinate_contMDiffAt Q hz).contMDiffWithinAt)
  intro z hz
  have hpos := N.overlapBarrierCoordinate_deriv_pos Q z.1 (by simpa using hz) (hpositive z hz)
  refine ⟨_, hpos.ne', ?_⟩
  exact (N.overlapBarrierCoordinate_hasDerivAt Q z.1 (by simpa using hz)).deriv.symm ▸
    N.overlapBarrierCoordinate_hasDerivAt Q z.1 (by simpa using hz)

theorem overlapBarrier_isLocalDiffeomorphOn (N Q : EpsilonNeck g)
    (hpositive : ∀ z ∈ Q.overlapCoordinateDomain N,
      0 < deriv (fun t => (N.coordinate_inverse (Q.coordinate_map (z.1, t))).2) z.2) :
    IsLocalDiffeomorphOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun x => ((Q.coordinate_inverse x).1, N.overlapBarrier Q x)) (N.carrier ∩ Q.carrier) := by
  let d : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace M ∞ := {
    toPartialEquiv := Q.coordinatePartialHomeomorph.toPartialEquiv
    open_source := Q.cylinderDomain_open
    open_target := Q.carrier_open
    contMDiffOn_toFun := Q.coordinate_map_smooth
    contMDiffOn_invFun := Q.coordinate_inverse_smooth }
  intro x
  have hxdom : Q.coordinate_inverse x ∈ Q.overlapCoordinateDomain N := by
    refine ⟨Q.coordinate_inverse_mem x x.property.2, ?_⟩
    change Q.coordinate_map (Q.coordinate_inverse x) ∈ N.carrier
    rw [Q.coordinate_map_coordinate_inverse x.property.2]
    exact x.property.1
  have hlocal : IsLocalDiffeomorphAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      Q.coordinate_inverse x := ⟨d.symm, x.property.2, fun _ _ => rfl⟩
  have hcomp := hlocal.comp ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace
    (N.overlapBarrierCoordinate_isLocalDiffeomorphOn Q hpositive ⟨Q.coordinate_inverse x, hxdom⟩)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Q.carrier_open.mem_nhds x.property.2] with y hy
  change ((Q.coordinate_inverse y).1, N.overlapBarrier Q y) =
    ((Q.coordinate_inverse y).1, N.overlapBarrierCoordinate Q (Q.coordinate_inverse y))
  simp only [overlapBarrier, overlapBarrierCoordinate, Q.coordinate_map_coordinate_inverse hy]

theorem overlapBarrierMap_isLocalDiffeomorph (N Q : EpsilonNeck g)
    (hpositive : ∀ z ∈ Q.overlapCoordinateDomain N,
      0 < deriv (fun t => (N.coordinate_inverse (Q.coordinate_map (z.1, t))).2) z.2) :
    let U : TopologicalSpace.Opens M :=
      ⟨N.carrier ∩ Q.carrier, N.carrier_open.inter Q.carrier_open⟩
    IsLocalDiffeomorph (M := U) (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (N.overlapBarrierMap Q : U → RoundCylinderSpace) := by
  intro U x
  obtain ⟨d, hxd, heq⟩ := N.overlapBarrier_isLocalDiffeomorphOn Q hpositive x
  let e := d.toOpenPartialHomeomorph.subtypeRestr (s := U) ⟨x⟩
  have hesource : e.source = Subtype.val ⁻¹' d.source :=
    d.toOpenPartialHomeomorph.subtypeRestr_source ⟨x⟩
  have hesub : e.target ⊆ d.target := d.toOpenPartialHomeomorph.subtypeRestr_target_subset ⟨x⟩
  let d' : PartialDiffeomorph (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) U RoundCylinderSpace ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      intro y hy
      rw [hesource] at hy
      have hd := d.contMDiffOn_toFun.contMDiffAt (d.open_source.mem_nhds hy)
      exact (contMDiffAt_subtype_iff.mpr hd).contMDiffWithinAt
    contMDiffOn_invFun := by
      have hs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
          (Subtype.val ∘ e.symm) e.target :=
        (d.contMDiffOn_invFun.mono hesub).congr
          (d.toOpenPartialHomeomorph.subtypeRestr_symm_eqOn ⟨x⟩).symm
      intro y hy
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target y).mp (hs y hy) }
  refine ⟨d', ?_, ?_⟩
  · change x ∈ e.source
    rw [hesource]
    exact hxd
  · intro y hy
    change y ∈ e.source at hy
    rw [hesource] at hy
    exact heq hy

end PoincareConjecture.EpsilonNeck
