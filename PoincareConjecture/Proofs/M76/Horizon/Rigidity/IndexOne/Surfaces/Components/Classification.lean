import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Annulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.ExactBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.ClosedPhaseSphere












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1



theorem other_source_component_disjoint_old_boundary
    (phi : C(H, H)) (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {S T : Set X} (hT : T ⊆ sourceSurface phi theta)
    (hScomp : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hTcomp : ∀ x ∈ T, connectedComponentIn (sourceSurface phi theta) x = T)
    (hne : T ≠ S) (A : Ann ≃ₜ S) (scale : C32 ≃ₜ C)
    (hmark : ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) (scale z) : X)) :
    Disjoint T (frontier R) := by
  apply disjoint_left.mpr
  intro x hx hxR
  obtain ⟨side, c, hc⟩ := exists_original_boundaryCircle_of_mem_rim phi theta F0 ⟨hT hx, hxR⟩
  have hxS : x ∈ S := by
    have h := (A (Dehn.annulusRimPoint side (scale.symm c))).property
    rw [hmark, scale.apply_symm_apply, hc] at h
    exact h
  exact hne ((hTcomp x hx).symm.trans (hScomp x hxS))



theorem exists_finite_source_components_of_model
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace Y] [T2Space Y]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {S : Set Y}
    (Hmodel : K.space ≃ₜ S) (F : Y → E) (hF : Continuous F)
    (hHF : ∀ x : S, (Hmodel.symm x : E) = F x) :
    ∃ (n : ℕ) (M : Fin n → Set Y),
      (⋃ i, M i) = S ∧ Pairwise (fun i j => Disjoint (M i) (M j)) ∧
      ∀ i, IsCompact (M i) ∧ IsConnected (M i) ∧ M i ⊆ S ∧
        ∀ x ∈ M i, connectedComponentIn S x = M i := by
  classical
  let D := K.vertexAbstractComplex.edgeGraph.ConnectedComponent
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let : Fintype D := Fintype.ofFinite D
  choose T G hTS hcomponent hG hGF using
    (fun d : D => exists_source_component_of_model K hK Hmodel F hF hHF d)
  have hFT (d : D) {y : Y} (hy : y ∈ T d) : F y ∈ (K.edgeComponentComplex d).space := by
    rw [← hGF d ⟨y, hy⟩]
    exact ((G d).symm ⟨y, hy⟩).property
  have hdis : Pairwise (fun d d' : D => Disjoint (T d) (T d')) := by
    intro d d' hne
    apply disjoint_left.mpr
    intro y hy hy'
    exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_space hne) (hFT d hy) (hFT d' hy')
  have hcover : (⋃ d, T d) = S := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨d, hd⟩ := mem_iUnion.mp hy
      exact hTS d hd
    · intro y hy
      have hFy : F y ∈ K.space := by
        rw [← hHF ⟨y, hy⟩]
        exact (Hmodel.symm ⟨y, hy⟩).property
      rw [← K.iUnion_edgeComponentComplex_space] at hFy
      obtain ⟨d, hd⟩ := mem_iUnion.mp hFy
      have hh : (G d ⟨F y, hd⟩ : Y) = y := by
        rw [hG]
        have hp : Set.inclusion (SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le d))
            (⟨F y, hd⟩ : (K.edgeComponentComplex d).space) = Hmodel.symm ⟨y, hy⟩ :=
          Subtype.ext (hHF ⟨y, hy⟩).symm
        rw [hp, Hmodel.apply_symm_apply]
      exact mem_iUnion.mpr ⟨d, hh ▸ (G d ⟨F y, hd⟩).property⟩
  have htop (d : D) : IsCompact (T d) ∧ IsConnected (T d) := by
    let J := K.edgeComponentComplex d
    let : CompactSpace J.space := isCompact_iff_compactSpace.mp
      (J.isCompact_space_of_finite (hK.subset (K.edgeComponentComplex_le d)))
    have hr : range (fun z : J.space => (G d z : Y)) = T d := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact (G d z).property
      · intro hy
        exact ⟨(G d).symm ⟨y, hy⟩, congrArg Subtype.val ((G d).apply_symm_apply ⟨y, hy⟩)⟩
    have hc : Continuous (fun z : J.space => (G d z : Y)) :=
      continuous_subtype_val.comp (G d).continuous
    let : ConnectedSpace J.space :=
      isConnected_iff_connectedSpace.mp (K.edgeComponentComplex_isPathConnected d).isConnected
    rw [← hr]
    exact ⟨isCompact_range hc, isConnected_range hc⟩
  let equiv : Fin (Fintype.card D) ≃ D := (Fintype.equivFin D).symm
  refine ⟨Fintype.card D, fun i => T (equiv i), ?_, ?_, ?_⟩
  · rw [equiv.surjective.iUnion_comp, hcover]
  · intro i j hij
    exact hdis (fun h => hij (equiv.injective h))
  · intro i
    exact ⟨(htop (equiv i)).1, (htop (equiv i)).2, hTS (equiv i), hcomponent (equiv i)⟩



theorem exists_compressed_source_phase_classification
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x)) :
    ∃ (S : Set X) (A : Ann ≃ₜ S) (q : ℝ × ℝ → X) (n : ℕ) (T : Fin n → Set X),
      S ⊆ sourceSurface phi theta ∧
      (∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S) ∧
      PolyhedralPLInCharts e q Ann ∧ (∀ x : Ann, (A x : X) = q x) ∧
      (∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
            (by norm_num) (by norm_num) z) : X)) ∧
      S ∪ (⋃ i, T i) = sourceSurface phi theta ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      (∀ i, Disjoint S (T i)) ∧
      ∀ i, IsCompact (T i) ∧ IsConnected (T i) ∧ T i ⊆ sourceSurface phi theta ∧
        (∀ x ∈ T i, connectedComponentIn (sourceSurface phi theta) x = T i) ∧
        Disjoint (T i) (frontier R) ∧ Nonempty (ChartwisePLSphere e (T i)) := by
  classical
  let h := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))
  let : T2Space X := h.isEmbedding.t2Space
  obtain ⟨S, A, q, hS, hScomp, hq, hA, hmark⟩ :=
    exists_compressed_source_annulus_with_original_rims
      e d hd phi hphi F0 heN hfront hAB hcorner hinj
  obtain ⟨s, F, K, J, Hmodel, g, hFc, _, _, hK, _, _, _, _, hHF, _⟩ :=
    exists_compressed_sourceSurface_incidence_model e d phi hphi F0 heN hfront hAB hcorner
  obtain ⟨m, M, hcover, hdis, hM⟩ :=
    exists_finite_source_components_of_model K hK Hmodel F hFc hHF
  let remaining := {i : Fin m // M i ≠ S}
  let equiv : Fin (Fintype.card remaining) ≃ remaining := (Fintype.equivFin remaining).symm
  let index (i : Fin (Fintype.card remaining)) : Fin m := (equiv i).val
  let T (i : Fin (Fintype.card remaining)) := M (index i)
  have hne (i : Fin (Fintype.card remaining)) : T i ≠ S := (equiv i).property
  have hidx : Function.Injective index := by
    intro i j hij
    exact equiv.injective (Subtype.ext hij)
  have hTS (i : Fin (Fintype.card remaining)) : Disjoint S (T i) := by
    apply disjoint_left.mpr
    intro x hxS hxT
    exact hne i (((hM (index i)).2.2.2 x hxT).symm.trans (hScomp x hxS))
  refine ⟨S, A, q, Fintype.card remaining, T, hS, hScomp, hq, hA, hmark, ?_, ?_, hTS, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · exact hS hx
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact (hM (index i)).2.2.1 hi
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
      by_cases hiS : M i = S
      · exact Or.inl (hiS ▸ hi)
      · refine Or.inr (mem_iUnion.mpr ⟨equiv.symm ⟨i, hiS⟩, ?_⟩)
        change x ∈ M ((equiv (equiv.symm ⟨i, hiS⟩)).val)
        rw [equiv.apply_symm_apply]
        exact hi
  · intro i j hij
    exact hdis (fun h => hij (hidx h))
  · intro i
    obtain ⟨hc, hconn, hTF, hTcomp⟩ := hM (index i)
    let scale := AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
      (by norm_num) (by norm_num)
    have hrim := other_source_component_disjoint_old_boundary phi theta F0
      hTF hScomp hTcomp (hne i) A scale hmark
    exact ⟨hc, hconn, hTF, hTcomp, hrim,
      exists_closed_source_component_sphere e d phi hphi F0 heN hfront hAB hcorner hinj
        hconn.nonempty hTF hTcomp hrim⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
