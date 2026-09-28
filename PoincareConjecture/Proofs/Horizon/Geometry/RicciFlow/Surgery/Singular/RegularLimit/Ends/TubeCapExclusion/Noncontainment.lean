import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeCapExclusion.SliceContainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.NonFilling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Separation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_tube_noncontainment_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {X : Set M},
        ∀ (C : CapCertificate g) (tube : EpsilonTubeCertificate g X),
          C.epsilon ≤ ε₀ → tube.epsilon ≤ ε₀ → ¬ C.carrier ⊆ tube.carrier := by
  obtain ⟨ε₁, hε₁, hsmall, hslice⟩ :=
    EpsilonNeck.exists_slice_through_center_subset_threshold.{u}
  obtain ⟨ε₂, hε₂, _, htransport⟩ :=
    EpsilonNeck.exists_contained_slice_compact_transport.{u}
  obtain ⟨ε₃, hε₃, _, hchain⟩ :=
    BalancedNeckChain.exists_central_sphere_transport_threshold.{u}
  obtain ⟨ε₄, hε₄, _, hfill⟩ :=
    BalancedNeckChain.exists_no_compact_filling_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)), lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g X C tube hC htube hsub
  have hCs : C.epsilon ≤ ε₁ ∧ C.epsilon ≤ ε₂ ∧ C.epsilon ≤ ε₃ ∧ C.epsilon ≤ ε₄ := by
    simpa only [le_min_iff] using hC
  have hTs : tube.epsilon ≤ ε₁ ∧ tube.epsilon ≤ ε₂ ∧
      tube.epsilon ≤ ε₃ ∧ tube.epsilon ≤ ε₄ := by
    simpa only [le_min_iff] using htube
  let B := tube.chain
  have hBU : (B.unionOpen : Set M) = tube.carrier := tube.carrier_eq_chain_union.symm
  have hneck (i : ℤ) (hi : i ∈ B.shape.active) : (B.neck i).carrier ⊆ B.unionOpen :=
    fun _ hx => mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  have hcap : C.carrier ⊆ (B.unionOpen : Set M) := hsub.trans hBU.symm.subset
  have hcenter : C.boundary_neck.center ∈ (B.unionOpen : Set M) :=
    hcap (C.boundary_neck_subset
      (C.boundary_neck.central_sphere_subset C.boundary_neck.center_on_central_sphere))
  obtain ⟨⟨i, hi⟩, hci⟩ := mem_iUnion.mp hcenter
  have hiε := B.epsilon_eq i hi
  let a := ((B.neck i).coordinate_inverse C.boundary_neck.center).2
  have ha : a ∈ Ioo (-(B.neck i).epsilon⁻¹) (B.neck i).epsilon⁻¹ :=
    ((B.neck i).coordinate_inverse_mem C.boundary_neck.center hci).2
  have hcontained : ∀ q : UnitTwoSphere,
      (B.neck i).coordinate_map (q, a) ∈ C.boundary_neck.carrier :=
    hslice (B.neck i) C.boundary_neck (hiε.trans_le hTs.1)
      (C.boundary_neck_epsilon.trans_le (hCs.1.trans hsmall)) hci
  obtain ⟨e, L, _, hLU, hefix, hecomp, heS⟩ :=
    htransport C.boundary_neck (B.neck i)
      (C.boundary_neck_epsilon.trans_le hCs.2.1) (hiε.trans_le hTs.2.1) ha hcontained
  have hLU' : L ⊆ (B.unionOpen : Set M) :=
    hLU.trans (union_subset (C.boundary_neck_subset.trans hcap) (hneck i hi))
  have heU : e '' (B.unionOpen : Set M) = B.unionOpen :=
    DeepHorn.image_eq_self_of_fixed_compl e
      (fun x hx => hefix x (fun h => hx (hLU' h)))
  have hiseparating : (B.neck i).IsSeparating :=
    ((B.neck i).isSeparating_iff_of_homeomorph C.boundary_neck e hecomp heS).mpr
      C.boundary_neck_isSeparating
  have hseparating : ∀ j ∈ B.shape.active, (B.neck j).IsSeparating := by
    intro j hj
    obtain ⟨f, _, _, _, _, _, hfS⟩ := hchain B hTs.2.2.1 i hi j hj
    have hfcomp : f '' connectedComponent (B.neck i).center =
        connectedComponent (B.neck j).center := by
      have himage := f.image_connectedComponentIn (s := univ)
        (x := (B.neck i).center) (mem_univ _)
      simp only [image_univ, f.surjective.range_eq, connectedComponentIn_univ] at himage
      apply himage.trans
      apply Eq.symm
      apply connectedComponent_eq
      apply (B.neck j).carrier_subset_connectedComponent
      apply (B.neck j).central_sphere_subset
      rw [← hfS]
      exact mem_image_of_mem f (B.neck i).center_on_central_sphere
    exact ((B.neck i).isSeparating_iff_of_homeomorph (B.neck j) f hfcomp hfS).mp
      hiseparating
  have hcore : e.symm '' C.closed_core ⊆ (B.unionOpen : Set M) := by
    have hinverse : e.symm '' (B.unionOpen : Set M) = B.unionOpen := by
      exact (congrArg (fun S => e.symm '' S) heU).symm.trans (e.symm_image_image _)
    rw [← hinverse]
    exact image_mono (C.closed_core_subset_carrier.trans hcap)
  have hfront : frontier (e.symm '' C.closed_core) = (B.neck i).central_sphere := by
    rw [← e.symm.image_frontier, C.core_frontier_eq_boundary,
      C.boundary_eq_neck_sphere, ← heS]
    exact e.symm_image_image _
  have hint : (interior (e.symm '' C.closed_core)).Nonempty := by
    rw [← e.symm.image_interior, ← C.core_eq_interior_closed_core]
    exact C.core_nonempty.image e.symm
  exact hfill B hTs.2.2.2 hseparating i hi _ hcore hfront hint
    (C.closed_core_compact.image e.symm.continuous)

end PoincareConjecture.CapCertificate
