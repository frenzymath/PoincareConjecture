import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.CapComponents
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.NeckCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.OpenSubset
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Sides
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails












set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate




theorem exists_second_cap_collar_straightening_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), D.epsilon ≤ ε₀ →
          ∀ (U : Opens M) (_T : OpenCylinderModel (U : Set M)),
            C.end_neck.carrier ⊆ U →
            Disjoint C.closed_core (U : Set M) → Disjoint D.closed_core C.carrier →
            Disjoint C.closed_core D.carrier →
            IsCompact (C.carrier ∪ (U : Set M) ∪ D.carrier) →
            (frontier (C.carrier ∪ (U : Set M)) ∩ D.core).Nonempty →
            ∃ s ∈ Ioo 0 D.epsilon⁻¹, ∃ δ : ℝ, 0 < δ ∧ 0 < s - δ ∧
              s + δ < D.epsilon⁻¹ ∧ D.end_neck.region (s - δ) (s + δ) ⊆ U ∧
              D.end_neck.region (s - δ) D.epsilon⁻¹ ⊆ U ∧
              ∃ η : ℝ, 0 < η ∧ η < δ ∧
              ∃ F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace U ∞,
                (∀ p : RoundCylinderSpace, |p.2| < η →
                  (F p : M) = D.end_neck.coordinate_map (p.1, s + p.2)) ∧
                let K := D.closed_core ∪ closure (D.end_neck.region (-D.epsilon⁻¹) s)
                IsCompact K ∧ K ⊆ D.carrier ∧
                  frontier K = range (fun q : UnitTwoSphere =>
                    D.end_neck.coordinate_map (q, s)) ∧
                  D.carrier ∩ (U : Set M) = ((U : Set M) ∩ interior K) ∪
                    D.end_neck.region (s - δ) D.epsilon⁻¹ ∧
                  ((U : Set M) ∩ interior K) ∩ D.end_neck.region (s - δ) D.epsilon⁻¹ =
                    D.end_neck.region (s - δ) s ∧
                  IsConnected ((U : Set M) ∩ interior K) ∧
                  IsConnected ((U : Set M) \ K) ∧
                  (∀ p : RoundCylinderSpace, (F p : M) ∈ interior K ↔ p.2 < 0) ∧
                  ∀ p : RoundCylinderSpace, (F p : M) ∈ K ↔ p.2 ≤ 0 := by
  obtain ⟨ε₀, hε₀, hsmall, hslice⟩ := exists_second_cap_essential_components_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε U T hend hfirst hDC hCD hcompact hencounter
  obtain ⟨s, hs, δ, hδ, hlo, hhi, hcollar, htail, hK, hKD, -, hfront,
      hunion, hinter, hcA, hcB, hcover, -, -, hescape⟩ :=
    hslice C D hε U.isOpen T.isConnected_carrier hend hfirst hDC hCD hcompact hencounter
  have hlo' : -D.end_neck.epsilon⁻¹ < s - δ := by
    rw [D.end_neck_epsilon]
    exact (neg_lt_zero.mpr (inv_pos.mpr D.epsilon_pos)).trans hlo
  have hhi' : s + δ < D.end_neck.epsilon⁻¹ := by rwa [D.end_neck_epsilon]
  obtain ⟨c, hcs, hct, hc, hci, hcval⟩ := D.end_neck.exists_slice_collar hlo' hhi'
  obtain ⟨E, -⟩ := D.end_neck.exists_unit_to_real_cylinder
  let T' := E.symm.trans (T.toDiffeomorph U)
  have hS : range (fun q : UnitTwoSphere => c (q, 0)) =
      range (fun q : UnitTwoSphere => D.end_neck.coordinate_map (q, s)) := by
    congr 1
    funext q
    simpa only [add_zero] using hcval (q, 0)
  let K := D.closed_core ∪ closure (D.end_neck.region (-D.epsilon⁻¹) s)
  obtain ⟨η, hη, hηδ, F, hF⟩ := Poincare.exists_essential_sphere_collar_extension_in_open
    U T' hδ c hcs (hct ▸ hcollar) hc hci ((U : Set M) ∩ interior K)
    ((U : Set M) \ K) (U.isOpen.inter isOpen_interior)
    (U.isOpen.inter hK.isClosed.isOpen_compl) hcA hcB
    (disjoint_left.mpr fun _ hx hy => hy.2 (interior_subset hx.2))
    (by rw [hS, ← hfront]; exact hcover) hescape
  have hFval (p : RoundCylinderSpace) (hp : |p.2| < η) :
      (F p : M) = D.end_neck.coordinate_map (p.1, s + p.2) :=
    (hF p hp).trans (hcval p)
  have hFzero : range (fun q : UnitTwoSphere => (F (q, 0) : M)) = frontier K := by
    rw [hfront]
    congr 1
    funext q
    simpa only [add_zero] using hFval (q, 0) (by simpa using hη)
  let q := (D.end_neck.coordinate_inverse D.end_neck.center).1
  let p₀ : RoundCylinderSpace := (q, -η / 2)
  have hp₀ : p₀.2 < 0 := by dsimp [p₀]; linarith
  have hpη : |p₀.2| < η := by rw [abs_of_neg hp₀]; dsimp [p₀]; linarith
  have hseed : (F p₀ : M) ∈ (U : Set M) ∩ interior K := by
    have hdom : (q, s + p₀.2) ∈ D.end_neck.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, D.end_neck_epsilon]
      refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp [p₀] <;> linarith
    have hr : (F p₀ : M) ∈ D.end_neck.region (s - δ) s := by
      rw [hFval p₀ hpη]
      refine ⟨D.end_neck.coordinate_map_mem hdom, ?_⟩
      rw [D.end_neck.coordinate_inverse_coordinate_map hdom]
      constructor <;> dsimp [p₀] <;> linarith
    exact (hinter.ge hr).1
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  obtain ⟨hleft, hright⟩ := Poincare.Topology.cylinder_sides_of_negative_witness
    U F.toHomeomorph (U.isOpen.inter isOpen_interior)
    (U.isOpen.inter hK.isClosed.isOpen_compl) hcA.isPreconnected
    (disjoint_left.mpr fun _ hx hy => hy.2 (interior_subset hx.2))
    (hFzero.symm ▸ hcover) hp₀ hseed
  refine ⟨s, hs, δ, hδ, hlo, hhi, hcollar, htail, η, hη, hηδ, F,
    hFval, hK, hKD, hfront, hunion, hinter, hcA, hcB, ?_, ?_⟩
  · intro p
    exact (and_iff_right (F p).property).symm.trans (hleft p)
  · intro p
    have h : (F p : M) ∉ K ↔ 0 < p.2 :=
      (and_iff_right (F p).property).symm.trans (hright p)
    simpa only [not_not, not_lt] using not_congr h

end PoincareConjecture.CapCertificate
