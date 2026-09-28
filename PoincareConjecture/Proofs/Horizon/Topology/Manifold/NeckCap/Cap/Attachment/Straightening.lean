import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.EssentialSlice
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.NeckCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.OpenSubset
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Sides
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Diffeomorph












set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapTubeAttachment



theorem exists_collar_straightening_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {X : Set M},
        ∀ {C : CapCertificate g} {T : EpsilonTubeCertificate g X} {side : Bool},
          CapTubeAttachment C T side → C.epsilon ≤ ε₀ →
          let U : Opens M := ⟨C.carrier ∩ T.carrier, C.carrier_open.inter T.carrier_open⟩
          ∃ s ∈ Ioo 0 C.epsilon⁻¹, ∃ δ : ℝ,
            0 < δ ∧ 0 < s - δ ∧ s + δ < C.epsilon⁻¹ ∧
            C.end_neck.region (s - δ) C.epsilon⁻¹ ⊆ U ∧
            ∃ η : ℝ, 0 < η ∧ η < δ ∧
            ∃ F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace U ∞,
              (∀ p : RoundCylinderSpace, |p.2| < η →
                (F p : M) = C.end_neck.coordinate_map (p.1, s + p.2)) ∧
              let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
              IsCompact K ∧ K ⊆ C.carrier ∧ C.closed_core ⊆ interior K ∧
                frontier K = range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, s)) ∧
                (U : Set M) \ K = C.end_neck.region s C.epsilon⁻¹ ∧
                (∀ p : RoundCylinderSpace, (F p : M) ∈ interior K ↔ p.2 < 0) ∧
                (∀ p : RoundCylinderSpace, (F p : M) ∈ K ↔ p.2 ≤ 0) ∧
                ∀ p : RoundCylinderSpace,
                  (F p : M) ∈ C.end_neck.region s C.epsilon⁻¹ ↔ 0 < p.2 := by
  obtain ⟨ε₀, hε₀, hsmall, hslice⟩ := exists_essential_slice_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g X C T side A hC
  let U : Opens M := ⟨C.carrier ∩ T.carrier, C.carrier_open.inter T.carrier_open⟩
  obtain ⟨s, hs, δ, hδ, hlo, hhi, htail, hK, hKC, hint, hfront, hcore,
      hUdiff, hcA, hcB, hcover, _, _, hescape⟩ := hslice A hC
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hlo' : -C.end_neck.epsilon⁻¹ < s - δ := by
    rw [C.end_neck_epsilon]
    exact (neg_lt_zero.mpr hR).trans hlo
  have hhi' : s + δ < C.end_neck.epsilon⁻¹ := by rwa [C.end_neck_epsilon]
  obtain ⟨c, hcs, hct, hc, hci, hcval⟩ := C.end_neck.exists_slice_collar hlo' hhi'
  obtain ⟨E, _⟩ := C.end_neck.exists_unit_to_real_cylinder
  let G := E.symm.trans (A.overlap_model.toDiffeomorph U)
  have hS : range (fun q : UnitTwoSphere => c (q, 0)) =
      range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, s)) := by
    congr 1
    funext q
    simpa only [add_zero] using hcval (q, 0)
  have hctU : c.target ⊆ U := by
    rw [hct]
    intro x hx
    exact htail ⟨hx.1, hx.2.1, hx.2.2.trans hhi⟩
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
  obtain ⟨η, hη, hηδ, F, hF⟩ := Poincare.exists_essential_sphere_collar_extension_in_open
    U G hδ c hcs hctU hc hci ((U : Set M) ∩ interior K) ((U : Set M) \ K)
    (U.isOpen.inter isOpen_interior) (U.isOpen.inter hK.isClosed.isOpen_compl)
    hcA hcB (disjoint_left.mpr fun _ hx hy => hy.2 (interior_subset hx.2))
    (by rw [hS, ← hfront]; exact hcover) hescape
  have hFval (p : RoundCylinderSpace) (hp : |p.2| < η) :
      (F p : M) = C.end_neck.coordinate_map (p.1, s + p.2) :=
    (hF p hp).trans (hcval p)
  have hFzero : range (fun q : UnitTwoSphere => (F (q, 0) : M)) = frontier K := by
    rw [hfront]
    congr 1
    funext q
    simpa only [add_zero] using hFval (q, 0) (by simpa using hη)
  let q := (C.end_neck.coordinate_inverse C.end_neck.center).1
  let p₀ : RoundCylinderSpace := (q, -η / 2)
  have hp₀ : p₀.2 < 0 := by dsimp [p₀]; linarith
  have hpη : |p₀.2| < η := by rw [abs_of_neg hp₀]; dsimp [p₀]; linarith
  have hseed : (F p₀ : M) ∈ (U : Set M) ∩ interior K := by
    refine ⟨(F p₀).property, ?_⟩
    rw [hint]
    apply Or.inr
    rw [hFval p₀ hpη]
    have hdom : (q, s + p₀.2) ∈ C.end_neck.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, C.end_neck_epsilon]
      refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp [p₀] <;> linarith
    refine ⟨C.end_neck.coordinate_map_mem hdom, ?_⟩
    rw [C.end_neck.coordinate_inverse_coordinate_map hdom]
    constructor <;> dsimp [p₀] <;> linarith
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  obtain ⟨hleft, hright⟩ := Poincare.Topology.cylinder_sides_of_negative_witness
    U F.toHomeomorph (U.isOpen.inter isOpen_interior)
    (U.isOpen.inter hK.isClosed.isOpen_compl) hcA.isPreconnected
    (disjoint_left.mpr fun _ hx hy => hy.2 (interior_subset hx.2))
    (hFzero.symm ▸ hcover) hp₀ hseed
  refine ⟨s, hs, δ, hδ, hlo, hhi, htail, η, hη, hηδ, F, hFval,
    hK, hKC, hcore, hfront, hUdiff, ?_, ?_, ?_⟩
  · intro p
    exact (and_iff_right (F p).property).symm.trans (hleft p)
  · intro p
    have h : (F p : M) ∉ K ↔ 0 < p.2 :=
      (and_iff_right (F p).property).symm.trans (hright p)
    simpa only [not_not, not_lt] using not_congr h
  · intro p
    rw [← hUdiff]
    exact hright p

end PoincareConjecture.CapTubeAttachment
