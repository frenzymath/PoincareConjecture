import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.ClosedPhaseSphere
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalSphereBicollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallBicollarSides
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

private theorem opposite_sides_of_local_frontier
    {X : Type*} [TopologicalSpace X] {D P N U : Set X}
    (hD : IsClosed D) (hregular : closure (interior D) = D)
    (hne : (frontier D ∩ U).Nonempty) (hU : IsOpen U)
    (hcover : U ⊆ frontier D ∪ P ∪ N)
    (hP : IsPreconnected P) (hN : IsPreconnected N)
    (hPF : Disjoint P (frontier D)) (hNF : Disjoint N (frontier D)) :
    (P ⊆ interior D ∧ Disjoint N D) ∨ (N ⊆ interior D ∧ Disjoint P D) := by
  obtain ⟨x, hx, hxU⟩ := hne
  have hxcl : x ∈ closure (interior D) := hregular.symm ▸ hD.frontier_subset hx
  obtain ⟨y, hyU, hyint⟩ := mem_closure_iff.mp hxcl U hU hxU
  have hxcompl : x ∈ closure Dᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  obtain ⟨z, hzU, hzout⟩ := mem_closure_iff.mp hxcompl U hU hxU
  have hy : y ∈ P ∪ N := by
    rcases hcover hyU with (hf | hp) | hn
    · exact (hf.2 hyint).elim
    · exact Or.inl hp
    · exact Or.inr hn
  have hz : z ∈ P ∪ N := by
    rcases hcover hzU with (hf | hp) | hn
    · exact (hzout (hD.frontier_subset hf)).elim
    · exact Or.inl hp
    · exact Or.inr hn
  rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier hP hD hPF with
    hPi | hPo
  · rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier hN hD hNF with
      hNi | hNo
    · exact (hzout (interior_subset (hz.elim (fun h => hPi h) (fun h => hNi h)))).elim
    · exact Or.inl ⟨hPi, hNo⟩
  · rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier hN hD hNF with
      hNi | hNo
    · exact Or.inr ⟨hNi, hPo⟩
    · exact (hy.elim (fun h => disjoint_left.mp hPo h (interior_subset hyint))
        (fun h => disjoint_left.mp hNo h (interior_subset hyint))).elim



theorem ChartwisePLSphere.bicollar_component_sides
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {N S : Set X}
    (sph : ChartwisePLSphere e S) (hN : IsClosed N)
    (hregular : closure (interior N) = N)
    (A : Set E) (HB : A ≃ₜ S) (c : E × ℝ → X)
    {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn c (A ×ˢ Icc (-r) r))
    (hfront : ∀ z ∈ A ×ˢ Icc (-r) r, c z ∈ frontier N ↔ z.2 = 0)
    (hopen : IsOpen (c '' (A ×ˢ Ioo (-r) r))) :
    (c '' (A ×ˢ Ioc 0 r) ⊆ interior N ∧ Disjoint (c '' (A ×ˢ Ico (-r) 0)) N) ∨
      (c '' (A ×ˢ Ico (-r) 0) ⊆ interior N ∧ Disjoint (c '' (A ×ˢ Ioc 0 r)) N) := by
  have hA : IsConnected A := isConnected_iff_connectedSpace.mpr
    (HB.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp sph.isConnected))
  have hpossub : A ×ˢ Ioc 0 r ⊆ A ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
  have hnegsub : A ×ˢ Ico (-r) 0 ⊆ A ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  refine opposite_sides_of_local_frontier hN hregular ?_ hopen ?_ ?_ ?_ ?_ ?_
  · obtain ⟨x, hx⟩ := hA.nonempty
    refine ⟨c (x, 0), (hfront (x, 0) ⟨hx, by constructor <;> linarith⟩).mpr rfl,
      (x, 0), ⟨hx, by constructor <;> linarith⟩, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    rcases lt_trichotomy z.2 0 with hneg | hzero | hpos
    · exact Or.inr ⟨z, ⟨hz.1, hz.2.1.le, hneg⟩, rfl⟩
    · exact Or.inl (Or.inl ((hfront z ⟨hz.1, hz.2.1.le, hz.2.2.le⟩).mpr hzero))
    · exact Or.inl (Or.inr ⟨z, ⟨hz.1, hpos, hz.2.2.le⟩, rfl⟩)
  · exact (hA.isPreconnected.prod isPreconnected_Ioc).image c (hc.mono hpossub)
  · exact (hA.isPreconnected.prod isPreconnected_Ico).image c (hc.mono hnegsub)
  · apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact hz.2.1.ne' ((hfront z (hpossub hz)).mp hx)
  · apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact hz.2.2.ne ((hfront z (hnegsub hz)).mp hx)

namespace HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))



theorem exists_isolating_open_of_source_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (phi : C(H, H)) (theta theta' : C)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (Hmodel : K.space ≃ₜ sourceSurface phi theta)
    {N S U : Set X} (hN : IsClosed N)
    (hfront : frontier N = (N ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hSne : S.Nonempty) (hS : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hrim : Disjoint S (frontier R)) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ W : Set X, IsOpen W ∧ S ⊆ W ∧ W ⊆ U ∧
      (∀ y ∈ W, y ∈ frontier N ↔ y ∈ S) ∧
      Disjoint W (sourceSurface phi theta \ S) ∧ Disjoint W (sourceSurface phi theta') := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let : LocallyPathConnectedSpace K.space := K.locallyPathConnectedSpace_of_finite hK
  let : LocallyPathConnectedSpace (sourceSurface phi theta) :=
    Hmodel.isQuotientMap.locallyPathConnectedSpace
  obtain ⟨x, hx⟩ := hSne
  have hSo : IsOpen ((Subtype.val : sourceSurface phi theta → X) ⁻¹' S) := by
    rw [← hcomponent x hx, connectedComponentIn_eq_image (hS hx),
      preimage_image_eq _ Subtype.val_injective]
    exact isOpen_connectedComponent
  obtain ⟨V, hV, hVS⟩ := isOpen_induced_iff.mp hSo
  have hVS' (y : X) (hy : y ∈ sourceSurface phi theta) : y ∈ V ↔ y ∈ S := by
    exact Iff.of_eq (congrArg
      (fun A : Set (sourceSurface phi theta) => (⟨y, hy⟩ : sourceSurface phi theta) ∈ A) hVS)
  let G : Set X := (N ∩ frontier R) ∪ sourceSurface phi theta'
  have hG : IsClosed G :=
    (hN.inter isClosed_frontier).union (sourceSurface_isCompact phi theta').isClosed
  let W : Set X := (V \ G) ∩ U
  have hSW : S ⊆ W := by
    intro y hy
    refine ⟨⟨(hVS' y (hS hy)).mpr hy, ?_⟩, hSU hy⟩
    rintro (hyold | hyother)
    · exact disjoint_left.mp hrim hy hyold.2
    · exact disjoint_left.mp hAB (hS hy) hyother
  refine ⟨W, (hV.sdiff hG).inter hU, hSW, inter_subset_right, ?_, ?_, ?_⟩
  · intro y hy
    constructor
    · intro hyf
      rw [hfront] at hyf
      rcases hyf with hyold | (hyphase | hyother)
      · exact (hy.1.2 (Or.inl hyold)).elim
      · exact (hVS' y hyphase).mp hy.1.1
      · exact (hy.1.2 (Or.inr hyother)).elim
    · intro hyS
      rw [hfront]
      exact Or.inr (Or.inl (hS hyS))
  · exact disjoint_left.mpr fun y hy hz => hz.2 ((hVS' y hz.1).mp hy.1.1)
  · exact disjoint_left.mpr fun y hy hz => hy.1.2 (Or.inr hz)

end HamiltonIntervalTorus



theorem ChartwisePLSphere.exists_small_component_bicollar
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R N S U : Set X}
    (sph : ChartwisePLSphere e S) (hR : IsCompact R) (heR : PLDomain e R)
    (heN : PLDomain e N) (hSint : S ⊆ interior R)
    (hU : IsOpen U) (hSU : S ⊆ U)
    (hcut : ∀ x ∈ U, x ∈ frontier N ↔ x ∈ S) :
    ∃ (t : Finset R) (K : SimplicialComplex ℝ (t → ℝ × (Fin 3 → ℝ)))
      (HB : K.space ≃ₜ S) (c : (t → ℝ × (Fin 3 → ℝ)) × ℝ → X) (r : ℝ),
      K.faces.Finite ∧ 0 < r ∧ r ≤ 1 / 2 ∧
      PolyhedralPLInCharts e c (K.space ×ˢ Icc (-1 : ℝ) 1) ∧
      Topology.IsEmbedding (fun z : (K.space ×ˢ Icc (-1 : ℝ) 1 :
        Set ((t → ℝ × (Fin 3 → ℝ)) × ℝ)) => c z) ∧
      (∀ x : K.space, c ((x : t → ℝ × (Fin 3 → ℝ)), 0) = HB x) ∧
      MapsTo c (K.space ×ˢ Icc (-r) r) (U ∩ interior R) ∧
      (∀ z ∈ K.space ×ˢ Icc (-r) r, c z ∈ frontier N ↔ z.2 = 0) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ r → IsOpen (c '' (K.space ×ˢ Ioo (-ε) ε))) ∧
      ((c '' (K.space ×ˢ Ioc 0 r) ⊆ interior N ∧
          Disjoint (c '' (K.space ×ˢ Ico (-r) 0)) N) ∨
        (c '' (K.space ×ˢ Ico (-r) 0) ⊆ interior N ∧
          Disjoint (c '' (K.space ×ˢ Ioc 0 r)) N)) := by
  obtain ⟨t, K, HB, c, hK, hc, hi, _, hbase, hzero, r, hr, hrhalf, hmaps, hopen⟩ :=
    sph.exists_original_small_bicollar hR heR hSint hU hSU
  have hsub : K.space ×ˢ Icc (-r) r ⊆ K.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hfront (z) (hz : z ∈ K.space ×ˢ Icc (-r) r) :
      c z ∈ frontier N ↔ z.2 = 0 :=
    (hcut (c z) (hmaps hz).1).trans (hzero ⟨z, hsub hz⟩)
  refine ⟨t, K, HB, c, r, hK, hr, hrhalf, hc, hi, hbase, hmaps, hfront, hopen, ?_⟩
  exact sph.bicollar_component_sides heN.closed heN.closure_interior K.space HB c hr
    (hc.continuousOn.mono hsub) hfront (hopen r hr le_rfl)

namespace HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))




theorem exists_closed_source_component_bicollar
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3) (phi : C(H, H))
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
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x))
    {S U : Set X} (hSne : S.Nonempty) (hS : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hrim : Disjoint S (frontier R)) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ (t : Finset R) (K : SimplicialComplex ℝ (t → ℝ × V3))
      (HB : K.space ≃ₜ S) (c : (t → ℝ × V3) × ℝ → X) (r : ℝ),
      K.faces.Finite ∧ 0 < r ∧ r ≤ 1 / 2 ∧
      PolyhedralPLInCharts e c (K.space ×ˢ Icc (-1 : ℝ) 1) ∧
      Topology.IsEmbedding (fun z : (K.space ×ˢ Icc (-1 : ℝ) 1 :
        Set ((t → ℝ × V3) × ℝ)) => c z) ∧
      (∀ x : K.space, c ((x : t → ℝ × V3), 0) = HB x) ∧
      MapsTo c (K.space ×ˢ Icc (-r) r) (U ∩ interior R) ∧
      (∀ z ∈ K.space ×ˢ Icc (-r) r,
        c z ∈ frontier (sourceSlab phi u v) ↔ z.2 = 0) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ r → IsOpen (c '' (K.space ×ˢ Ioo (-ε) ε))) ∧
      ((c '' (K.space ×ˢ Ioc 0 r) ⊆ interior (sourceSlab phi u v) ∧
          Disjoint (c '' (K.space ×ˢ Ico (-r) 0)) (sourceSlab phi u v)) ∨
        (c '' (K.space ×ˢ Ico (-r) 0) ⊆ interior (sourceSlab phi u v) ∧
          Disjoint (c '' (K.space ×ˢ Ioc 0 r)) (sourceSlab phi u v))) ∧
      Disjoint (c '' (K.space ×ˢ Icc (-r) r)) (sourceSurface phi theta \ S) ∧
      Disjoint (c '' (K.space ×ˢ Icc (-r) r)) (sourceSurface phi theta') := by
  let h := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))
  let : TopologicalSpace.MetrizableSpace X := h.isEmbedding.metrizableSpace
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨sph⟩ := exists_closed_source_component_sphere e d phi hphi F0 heN hfront
    hAB hcorner hinj hSne hS hcomponent hrim
  obtain ⟨s, F, K0, A, Hmodel, g, _, _, _, hK0, _⟩ :=
    exists_compressed_sourceSurface_incidence_model e d phi hphi F0 heN hfront hAB hcorner
  obtain ⟨W, hW, hSW, hWU, hcut, hrest, hother⟩ :=
    exists_isolating_open_of_source_component phi theta theta' K0 hK0 Hmodel
      heN.closed hfront hAB hSne hS hcomponent hrim hU hSU
  have hSint : S ⊆ interior R := by
    intro x hx
    by_contra hn
    apply disjoint_left.mp hrim hx
    rw [hphi.source_domain.closed.frontier_eq]
    exact ⟨sourceSurface_subset phi theta (hS hx), hn⟩
  obtain ⟨t, K, HB, c, r, hK, hr, hrhalf, hc, hi, hbase, hmaps, hf, hopen, hsides⟩ :=
    sph.exists_small_component_bicollar (isCompact_latticeHandleDomain (Fin 1) (Fin 2) L)
      hphi.source_domain heN hSint hW hSW hcut
  refine ⟨t, K, HB, c, r, hK, hr, hrhalf, hc, hi, hbase,
    (fun z hz => ⟨hWU (hmaps hz).1, (hmaps hz).2⟩), hf, hopen, hsides, ?_, ?_⟩
  · exact disjoint_left.mpr fun _ ⟨z, hz, hzx⟩ hx =>
      disjoint_left.mp hrest (hzx ▸ (hmaps hz).1) hx
  · exact disjoint_left.mpr fun _ ⟨z, hz, hzx⟩ hx =>
      disjoint_left.mp hother (hzx ▸ (hmaps hz).1) hx

end HamiltonIntervalTorus
end PoincareConjecture.M76
