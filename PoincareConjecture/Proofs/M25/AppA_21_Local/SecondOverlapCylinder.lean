import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCommonSphereProducer
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapChainIntersection
import PoincareConjecture.Proofs.M25.AppA_21_Local.FullBoundarySecondOverlap
import PoincareConjecture.Proofs.M25.AppA_21_Local.MixedSecondOverlap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M25

set_option linter.unusedVariables false in

theorem L3a_second_overlap_cylinder_model :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C0 C1 : CapCertificate g) (D : BalancedNeckChain g C0.epsilon) {b : ℤ}
      (hsmall : C0.epsilon ≤ epsilon0)
      (hε : C1.epsilon = C0.epsilon)
      (hshape : D.shape = ChainShape.finite 0 b) (hstart : D.neck 0 = C0.end_neck)
      (hsep : ∀ i ∈ D.shape.active, (D.neck i).IsSeparating)
      (hout : ∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C0.carrier)
      (hquarters : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
        closure ((D.neck i).region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹) ⊆
            (D.neck (i + 1)).carrier ∧
          closure ((D.neck (i + 1)).region
              (-C0.epsilon⁻¹) (-C0.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier)
      (hno : ¬ (C0.carrier \ C0.end_neck.region
        (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core))
      (K : CappedTubeCertificate g) (hKcap : K.cap = C0)
      (hKtube : K.tube.carrier = (⋃ i ∈ D.shape.active, (D.neck i).carrier))
      (hdisjoint : Disjoint C0.closed_core C1.carrier)
      (y : M) (hycore : y ∈ C1.core)
      (hyclosure : y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹))
      (hyout : y ∉ K.carrier)
      (hmeet : (K.carrier ∩ C1.boundary_sphere).Nonempty)
      (hcompact : IsCompact (K.carrier ∪ C1.carrier)),
      Nonempty (OpenCylinderModel (C1.carrier ∩ K.tube.carrier)) := by
  obtain ⟨eg, hgp, hgcap, graph⟩ :=
    CapCertificate.exists_common_outward_graph_of_finite_core_frontier.{u}
  obtain ⟨ef, hfp, _, full⟩ :=
    CapCertificate.exists_full_boundary_second_overlap_cylinder.{u}
  obtain ⟨em, hmp, _, mixed⟩ :=
    CapCertificate.exists_mixed_second_overlap_cylinder.{u}
  refine ⟨min eg (min ef em), lt_min hgp (lt_min hfp hmp),
    (min_le_left _ _).trans hgcap, ?_⟩
  intro M _ _ _ _ _ _ g C0 C1 D b hsmall he hshape hstart hsep hout hquarters hno
    K hKcap hKtube hdisjoint y hycore hyclosure hyout hmeet _hcompact
  classical
  let U : Set M := ⋃ i ∈ D.shape.active, (D.neck i).carrier
  let V : TopologicalSpace.Opens M :=
    ⟨C0.carrier ∪ U, C0.carrier_open.union
      (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
  have heg : C0.epsilon ≤ eg := hsmall.trans (min_le_left _ _)
  have hef : C0.epsilon ≤ ef :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hem : C0.epsilon ≤ em :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb0 : (0 : ℤ) ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    rw [hshape] at hi
    exact hi.1.trans hi.2
  have hzero : (0 : ℤ) ∈ D.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, hb0⟩
  have hfirstIndex : ∀ i ∈ D.shape.active, (0 : ℤ) ≤ i := by
    intro i hi
    rw [hshape] at hi
    exact hi.1
  have hfirst : C0.carrier ∩ U = C0.end_neck.carrier :=
    C0.inter_chain_union_eq_end_neck D hzero hfirstIndex hstart hout
  have hKV : K.carrier = (V : Set M) := by
    change K.carrier = C0.carrier ∪ U
    simpa only [U, hKcap, hKtube] using K.carrier_eq_union
  have hyVout : y ∉ (V : Set M) := by
    rwa [← hKV]
  have hVmeet : ((V : Set M) ∩ C1.boundary_sphere).Nonempty := by
    rwa [← hKV]
  obtain ⟨d, _, _, hyV, R, f, N, s, hR, _, _, _, hcore, _, hf, _, _,
      hlevel, _, hcases⟩ :=
    graph C0 C1 D heg he hshape hstart hsep hout hquarters hno
      y hycore hyclosure hyVout hVmeet
  have hcyl : Nonempty (OpenCylinderModel (C1.carrier ∩ U)) := by
    rcases hcases with hfull | ⟨z, _, _, _, _, _, _, hN, hs, hbounds, hend⟩
    · exact full C0 C1 D hef he hshape hsep hfirst hdisjoint hfull.1
        d.toHomeomorph y hycore hyV hyVout
    · have hL : 0 < C0.epsilon⁻¹ := inv_pos.mpr C0.epsilon_pos
      have hfdom : ∀ q, f q ∈ Ioo (0 : ℝ) C1.epsilon⁻¹ := by
        intro q
        rw [he]
        constructor <;> linarith only [(hbounds q).1, (hbounds q).2, hL]
      have hlevel' :
          range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)) =
            range (fun q : UnitTwoSphere =>
              (D.neck b).coordinate_map (q, 3 * C0.epsilon⁻¹ / 4)) := by
        simpa only [hN, hs] using hlevel
      have hend' : range (fun q : UnitTwoSphere =>
          (D.neck b).coordinate_map (q, 3 * C0.epsilon⁻¹ / 4)) ⊆
            C1.end_neck.carrier := by
        rwa [← hlevel']
      exact mixed C0 C1 D hem he hshape hfirst hdisjoint d.toHomeomorph
        R hR hcore f hf.continuous hfdom hlevel' hend'
        y hycore hyclosure hyVout
  simpa only [hKtube, U] using hcyl

end PoincareConjecture.M25
