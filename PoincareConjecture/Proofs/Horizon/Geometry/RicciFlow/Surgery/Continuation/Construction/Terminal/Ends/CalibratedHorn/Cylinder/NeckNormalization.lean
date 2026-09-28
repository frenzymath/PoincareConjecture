import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Balanced
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.ChainTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.SmoothChainTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeCapExclusion.SliceContainment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Balanced
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem cylinder_at_neck_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)
        (N : EpsilonNeck g), ε ≤ 1 / 200 → N.epsilon ≤ 1 / 200 →
        N.carrier ⊆ C.unionOpen → N.IsSeparating →
        ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞,
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) = N.central_sphere := by
  intro M _ _ _ _ _ _ _ g ε C N hε hN hNU hsepN
  have hcenterU := hNU (N.central_sphere_subset N.center_on_central_sphere)
  obtain ⟨⟨i, hi⟩, hcenter⟩ := mem_iUnion.mp hcenterU
  have hsub (j : ℤ) (hj : j ∈ C.shape.active) : (C.neck j).carrier ⊆ C.unionOpen :=
    fun _ hx => mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩
  let a := ((C.neck i).coordinate_inverse N.center).2
  have ha : a ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ :=
    ((C.neck i).coordinate_inverse_mem N.center hcenter).2
  have hcontained := (C.neck i).slice_through_center_subset_of_epsilon_le N
    ((C.epsilon_eq i hi).symm ▸ hε) hN hcenter
  obtain ⟨F, L, hL, hLU, hFfix, hFsphere⟩ := N.contained_slice_smooth_transport_of_epsilon_le (C.neck i) hN
    ((C.epsilon_eq i hi).symm ▸ hε) ha hcontained
  have hLU' : L ⊆ C.unionOpen := hLU.trans (union_subset hNU (hsub i hi))
  have htransport (j : ℤ) (hj : j ∈ C.shape.active) :
      ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
        IsCompact K ∧ K ⊆ C.unionOpen ∧ (∀ x, x ∉ K → D x = x) ∧
        D '' (C.neck j).central_sphere = N.central_sphere := by
    obtain ⟨D, K, hK, hKU, hDfix, _, hDsphere⟩ := C.central_sphere_smooth_transport_of_epsilon_le hε j hj i hi
    refine ⟨D.trans F, K ∪ L, hK.union hL, union_subset hKU hLU', ?_, ?_⟩
    · intro x hx
      change F (D x) = x
      rw [hDfix x (fun h => hx (Or.inl h)), hFfix x (fun h => hx (Or.inr h))]
    · change (F ∘ D) '' (C.neck j).central_sphere = N.central_sphere
      rw [image_comp, hDsphere, hFsphere]
  have hsep (j : ℤ) (hj : j ∈ C.shape.active) : (C.neck j).IsSeparating := by
    obtain ⟨D, K, _, hKU, hfix, hsphere⟩ := htransport j hj
    have hcomponent : D '' connectedComponent (C.neck j).center =
        connectedComponent N.center := by
      exact (Homeomorph.image_connectedComponent_eq_of_eqOn_compl D.toHomeomorph
        C.isConnected_union.isPreconnected
        (fun x hx => hfix x (fun h => hx (hKU h))) _).trans
          (connectedComponent_eq (C.union_subset_connectedComponent hj hcenterU))
    exact ((C.neck j).isSeparating_iff_of_homeomorph N D.toHomeomorph
      hcomponent hsphere).mpr hsepN
  obtain ⟨D, j, hj, c, hc, hDzero⟩ := cylinder_with_middle_of_epsilon_le C hε hsep
  have hc' : c ∈ Ioo (-(C.neck j).epsilon⁻¹) (C.neck j).epsilon⁻¹ := by
    simpa only [C.epsilon_eq j hj] using hc
  obtain ⟨G, K₀, hK₀, hK₀N, hGfix, _, hGsphere⟩ :=
    (C.neck j).exists_smooth_graph_transport (fun _ => c) contMDiff_const (fun _ => hc')
  obtain ⟨E, K₁, _, hK₁U, hEfix, hEsphere⟩ := htransport j hj
  let H := G.symm.trans E
  have hHfix (x : M) (hx : x ∉ (C.unionOpen : Set M)) : H x = x := by
    have hG : G x = x := hGfix x (fun h => hx (hsub j hj (hK₀N h)))
    have hGinv : G.symm x = x := (congrArg G.symm hG).symm.trans (G.symm_apply_apply x)
    change E (G.symm x) = x
    rw [hGinv, hEfix x (fun h => hx (hK₁U h))]
  let H₀ := H.restrictOpensOfFixedCompl C.unionOpen subset_rfl hHfix
  refine ⟨D.trans H₀, ?_⟩
  change range (fun q : UnitTwoSphere => H (D (q, 0))) = N.central_sphere
  rw [show (fun q : UnitTwoSphere => H (D (q, 0))) =
      H ∘ (fun q : UnitTwoSphere => (D (q, 0) : M)) from rfl, range_comp,
    hDzero, ← hGsphere]
  change (E ∘ G.symm) '' (G '' (C.neck j).central_sphere) = N.central_sphere
  have hcancel : G.symm '' (G '' (C.neck j).central_sphere) = (C.neck j).central_sphere :=
    G.toEquiv.symm_image_image _
  rw [image_comp, hcancel, hEsphere]



theorem openCylinderModel_at_neck_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)
        (N : EpsilonNeck g), ε ≤ 1 / 200 → N.epsilon ≤ 1 / 200 →
        N.carrier ⊆ C.unionOpen → N.IsSeparating →
        ∃ Q : OpenCylinderModel (C.unionOpen : Set M), Q.middleSphere = N.central_sphere := by
  intro M _ _ _ _ _ _ _ g ε C N hε hN hNU hsep
  obtain ⟨D, hD⟩ := cylinder_at_neck_of_epsilon_le C N hε hN hNU hsep
  obtain ⟨E, hE⟩ := N.exists_unit_to_real_cylinder
  let q₀ := (N.coordinate_inverse N.center).1
  refine ⟨OpenCylinderModel.ofDiffeomorph C.unionOpen (E.trans D) q₀, ?_⟩
  rw [OpenCylinderModel.ofDiffeomorph_middleSphere, ← hD]
  congr 1
  funext q
  change (D (E ⟨(q, 1 / 2), mem_univ _, by norm_num⟩) : M) = _
  rw [hE]

end PoincareConjecture.BalancedNeckChain
