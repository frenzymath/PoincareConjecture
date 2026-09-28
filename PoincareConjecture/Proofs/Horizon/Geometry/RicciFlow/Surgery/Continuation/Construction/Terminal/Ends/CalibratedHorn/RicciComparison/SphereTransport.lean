import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.Projection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.NeckGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.SmoothSliceTransport




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem sphereSlice_graph_and_isotopy_of_epsilon_le
    (A B : EpsilonNeck g) (hA : A.epsilon ≤ 1 / 200) (hB : B.epsilon ≤ 1 / 200)
    {s : ℝ} (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hc : ∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) :
    ∃ h : UnitTwoSphere → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ q, h q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹) ∧
      range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
        range (fun q : UnitTwoSphere => A.coordinate_map (q, h q)) ∧
      SmoothSphereIsotopicIn A.carrier A.central_sphere
        (range (fun q : UnitTwoSphere => B.coordinate_map (q, s))) := by
  obtain ⟨e, he⟩ := A.sphereSlice_projection_diffeomorph_of_epsilon_le B hA hB hs hc
  let h : UnitTwoSphere → ℝ :=
    fun q => (A.coordinate_inverse (B.coordinate_map (e.symm q, s))).2
  have hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h := by
    have hcoord : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q => A.coordinate_inverse (B.coordinate_map (e.symm q, s))) := by
      intro q
      exact (A.coordinate_inverse_smooth.contMDiffAt
        (A.carrier_open.mem_nhds (hc (e.symm q)))).comp q
        ((B.sphereSlice_contMDiff hs).comp e.symm.contMDiff q)
    exact contMDiff_snd.comp hcoord
  have hdom (q : UnitTwoSphere) : h q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ :=
    (A.coordinate_inverse_mem _ (hc (e.symm q))).2
  have hgraph (q : UnitTwoSphere) :
      A.coordinate_map (q, h q) = B.coordinate_map (e.symm q, s) := by
    have hcoord : (q, h q) = A.coordinate_inverse (B.coordinate_map (e.symm q, s)) := by
      refine Prod.ext ?_ (show h q = _ from rfl)
      rw [← he, e.apply_symm_apply]
    rw [hcoord, A.coordinate_map_coordinate_inverse (hc (e.symm q))]
  have hrange : range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
      range (fun q : UnitTwoSphere => A.coordinate_map (q, h q)) := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨e q, by simpa only [e.symm_apply_apply] using hgraph (e q)⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e.symm q, (hgraph q).symm⟩
  refine ⟨h, hh, hdom, hrange, ?_⟩
  have hzero (q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr A.epsilon_pos), inv_pos.mpr A.epsilon_pos⟩
  have hisotopy := A.coordinate_graphs_isotopic (fun _ => 0) h contMDiff_const hh hzero hdom
  rwa [A.centralSphere_range, ← hrange] at hisotopy

theorem contained_slice_smooth_transport_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    {a : ℝ} (ha : a ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹)
    (hmem : ∀ q : UnitTwoSphere, P.coordinate_map (q, a) ∈ N.carrier) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ N.carrier ∪ P.carrier ∧
      (∀ x, x ∉ K → D x = x) ∧ D '' P.central_sphere = N.central_sphere := by
  obtain ⟨h, hh, hdom, hslice, _⟩ := N.sphereSlice_graph_and_isotopy_of_epsilon_le P hN hP ha hmem
  obtain ⟨DN, KN, hKN, hKNN, hDNfix, _, hDNsphere⟩ :=
    N.exists_smooth_graph_transport h hh hdom
  obtain ⟨DP, KP, hKP, hKPP, hDPfix, _, hDPsphere⟩ :=
    P.exists_smooth_graph_transport (fun _ => a) contMDiff_const (fun _ => ha)
  refine ⟨DP.trans DN.symm, KN ∪ KP, hKN.union hKP,
    union_subset_union hKNN hKPP, ?_, ?_⟩
  · intro x hx
    change DN.symm (DP x) = x
    rw [hDPfix x (fun h => hx (Or.inr h))]
    have hfix := hDNfix x (fun h => hx (Or.inl h))
    exact (congrArg DN.symm hfix).symm.trans (DN.symm_apply_apply x)
  · change (DN.symm ∘ DP) '' P.central_sphere = N.central_sphere
    rw [image_comp, hDPsphere, hslice, ← hDNsphere]
    exact DN.toEquiv.symm_image_image _

theorem central_sphere_smooth_transport_of_center_mem
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    (hcenter : N.center ∈ P.carrier) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ N.carrier ∪ P.carrier ∧
      (∀ x, x ∉ K → D x = x) ∧ D '' P.central_sphere = N.central_sphere := by
  exact N.contained_slice_smooth_transport_of_epsilon_le P hN hP
    (P.coordinate_inverse_mem N.center hcenter).2
    (P.slice_through_center_subset_of_epsilon_le N hP hN hcenter)

end PoincareConjecture.EpsilonNeck
