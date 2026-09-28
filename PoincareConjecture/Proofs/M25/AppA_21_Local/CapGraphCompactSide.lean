import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBasics
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Reversal
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement
import PoincareConjecture.Proofs.M25.Mathlib.OppositeCollarComponents
import Mathlib.Topology.Order.Compact









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem CapCertificate.outward_graph_compact_side
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) (R : EpsilonNeck g)
    (hR : R = C.boundary_neck ∨ R = C.boundary_neck.reverse)
    (hcore : R.carrier ∩ C.core = R.region (-C.epsilon⁻¹) 0)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hfdom : ∀ q, f q ∈ Ico (0 : ℝ) C.epsilon⁻¹) :
    let L := C.epsilon⁻¹
    let q := (R.coordinate_inverse R.center).1
    let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, f v))
    let a := R.coordinate_map (q, -L / 2)
    let b := R.coordinate_map (q, (f q + L) / 2)
    let A := connectedComponentIn Sᶜ a
    let B := connectedComponentIn Sᶜ b
    let U := C.core ∪ R.coordinate_map ''
      {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < f z.1}
    let K := C.closed_core ∪ R.coordinate_map ''
      {z : RoundCylinderSpace | 0 ≤ z.2 ∧ z.2 ≤ f z.1}
    U = A ∧ closure A = K ∧ IsCompact (closure A) ∧
      closure A ⊆ C.carrier ∧ C.closed_core ⊆ closure A ∧
      a ∉ S ∧ b ∉ S ∧ A ≠ B ∧ frontier A = S ∧ frontier B = S := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := C.epsilon⁻¹
  let q := (R.coordinate_inverse R.center).1
  let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, f v))
  let a := R.coordinate_map (q, -L / 2)
  let b := R.coordinate_map (q, (f q + L) / 2)
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  let Dm : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < f z.1}
  let Dp : Set RoundCylinderSpace := {z | f z.1 < z.2 ∧ z.2 < L}
  let Dc : Set RoundCylinderSpace := {z | 0 ≤ z.2 ∧ z.2 ≤ f z.1}
  let Em := R.coordinate_map '' Dm
  let Ep := R.coordinate_map '' Dp
  let U := C.core ∪ Em
  let K := C.closed_core ∪ R.coordinate_map '' Dc
  change U = A ∧ closure A = K ∧ IsCompact (closure A) ∧
    closure A ⊆ C.carrier ∧ C.closed_core ⊆ closure A ∧
    a ∉ S ∧ b ∉ S ∧ A ≠ B ∧ frontier A = S ∧ frontier B = S
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hepsilon : R.epsilon = C.epsilon := by
    rcases hR with h | h <;> rw [h] <;> exact C.boundary_neck_epsilon
  have hRsub : R.carrier ⊆ C.carrier := by
    rcases hR with h | h <;> rw [h] <;> exact C.boundary_neck_subset
  have hRsphere : R.central_sphere = C.boundary_sphere := by
    rcases hR with h | h <;> rw [h] <;> exact C.boundary_eq_neck_sphere.symm
  have hcoreK : C.core ⊆ C.closed_core := by
    rw [C.core_eq_interior_closed_core]
    exact interior_subset
  have hKC : C.closed_core ⊆ C.carrier := by
    rw [C.closed_core_eq_complement_end]
    exact sdiff_subset
  have hcoreOpen : IsOpen C.core := by
    rw [C.core_eq_interior_closed_core]
    exact isOpen_interior
  have hcoreEnd : Disjoint C.core C.end_neck.carrier := by
    apply disjoint_left.mpr
    intro x hx hxEnd
    have hxK := hcoreK hx
    rw [C.closed_core_eq_complement_end] at hxK
    exact hxK.2 hxEnd
  have hboundary (x : M) (hxK : x ∈ C.closed_core) (hxc : x ∉ C.core) :
      x ∈ R.central_sphere := by
    rw [hRsphere, ← C.core_frontier_eq_boundary]
    refine ⟨subset_closure hxK, ?_⟩
    simpa only [← C.core_eq_interior_closed_core] using hxc
  have hfd (v : UnitTwoSphere) : f v ∈ Ioo (-L) L :=
    ⟨(neg_lt_zero.mpr hL).trans_le (hfdom v).1, (hfdom v).2⟩
  have hDm : Dm ⊆ R.cylinderDomain := by
    intro z hz
    rw [EpsilonNeck.cylinderDomain, hepsilon]
    exact ⟨mem_univ _, hz.1, hz.2.trans (hfdom z.1).2⟩
  have hDp : Dp ⊆ R.cylinderDomain := by
    intro z hz
    rw [EpsilonNeck.cylinderDomain, hepsilon]
    exact ⟨mem_univ _, (hfd z.1).1.trans hz.1, hz.2⟩
  have hDc : Dc ⊆ R.cylinderDomain := by
    intro z hz
    rw [EpsilonNeck.cylinderDomain, hepsilon]
    exact ⟨mem_univ _, (neg_lt_zero.mpr hL).trans_le hz.1,
      hz.2.trans_lt (hfdom z.1).2⟩
  have hgraphDom (v : UnitTwoSphere) : (v, f v) ∈ R.cylinderDomain := by
    rw [EpsilonNeck.cylinderDomain, hepsilon]
    exact ⟨mem_univ _, hfd v⟩
  have hDmOpen : IsOpen Dm :=
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd (hf.comp continuous_fst))
  have hEmOpen : IsOpen Em :=
    R.coordinatePartialHomeomorph.isOpen_image_of_subset_source hDmOpen hDm
  have hDmConnected : IsConnected Dm :=
    isConnected_between_continuous_graphs
      (f := fun _ : UnitTwoSphere => -L) (g := f) continuous_const hf
      (fun v => (hfd v).1)
  have hDpConnected : IsConnected Dp :=
    isConnected_between_continuous_graphs
      (f := f) (g := fun _ : UnitTwoSphere => L) hf continuous_const
      (fun v => (hfd v).2)
  have hEmConnected : IsConnected Em := hDmConnected.image R.coordinate_map
    (R.coordinate_map_smooth.continuousOn.mono hDm)
  have hEpConnected : IsConnected Ep := hDpConnected.image R.coordinate_map
    (R.coordinate_map_smooth.continuousOn.mono hDp)
  have hEmmem (x : M) : x ∈ Em ↔ x ∈ R.carrier ∧
      -L < (R.coordinate_inverse x).2 ∧
        (R.coordinate_inverse x).2 < f (R.coordinate_inverse x).1 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨R.coordinate_map_mem (hDm hz), ?_⟩
      rw [R.coordinate_inverse_coordinate_map (hDm hz)]
      exact hz
    · rintro ⟨hx, hlo, hhi⟩
      exact ⟨R.coordinate_inverse x, ⟨hlo, hhi⟩, R.coordinate_map_coordinate_inverse hx⟩
  have hEpmem (x : M) : x ∈ Ep ↔ x ∈ R.carrier ∧
      f (R.coordinate_inverse x).1 < (R.coordinate_inverse x).2 ∧
        (R.coordinate_inverse x).2 < L := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨R.coordinate_map_mem (hDp hz), ?_⟩
      rw [R.coordinate_inverse_coordinate_map (hDp hz)]
      exact hz
    · rintro ⟨hx, hlo, hhi⟩
      exact ⟨R.coordinate_inverse x, ⟨hlo, hhi⟩, R.coordinate_map_coordinate_inverse hx⟩
  have hSmem (x : M) : x ∈ S ↔ x ∈ R.carrier ∧
      (R.coordinate_inverse x).2 = f (R.coordinate_inverse x).1 := by
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨R.coordinate_map_mem (hgraphDom v), ?_⟩
      rw [R.coordinate_inverse_coordinate_map (hgraphDom v)]
    · rintro ⟨hx, ht⟩
      refine ⟨(R.coordinate_inverse x).1, ?_⟩
      change R.coordinate_map
        ((R.coordinate_inverse x).1, f (R.coordinate_inverse x).1) = x
      rw [← ht]
      exact R.coordinate_map_coordinate_inverse hx
  have haEm : a ∈ Em := by
    refine ⟨(q, -L / 2), ?_, rfl⟩
    change -L < -L / 2 ∧ -L / 2 < f q
    constructor <;> linarith only [hL, (hfdom q).1]
  have hbEp : b ∈ Ep := by
    refine ⟨(q, (f q + L) / 2), ?_, rfl⟩
    change f q < (f q + L) / 2 ∧ (f q + L) / 2 < L
    constructor <;> linarith only [(hfdom q).2]
  have hSU : S ⊆ Uᶜ := by
    intro x hxS hxU
    obtain ⟨hxR, ht⟩ := (hSmem x).mp hxS
    rcases hxU with hxc | hxm
    · have hneg : x ∈ R.region (-L) 0 := hcore ▸ ⟨hxR, hxc⟩
      linarith only [hneg.2.2, ht, (hfdom (R.coordinate_inverse x).1).1]
    · exact (ne_of_lt ((hEmmem x).mp hxm).2.2) ht
  have hEpU : Ep ⊆ Uᶜ := by
    intro x hxp hxU
    obtain ⟨hxR, hlo, _⟩ := (hEpmem x).mp hxp
    rcases hxU with hxc | hxm
    · have hneg : x ∈ R.region (-L) 0 := hcore ▸ ⟨hxR, hxc⟩
      linarith only [hneg.2.2, hlo, (hfdom (R.coordinate_inverse x).1).1]
    · exact (not_lt_of_ge hlo.le) ((hEmmem x).mp hxm).2.2
  have hEmS : Em ⊆ Sᶜ := fun _ hx hxS => hSU hxS (Or.inr hx)
  have hEpS : Ep ⊆ Sᶜ := by
    intro x hx hxS
    exact (ne_of_lt ((hEpmem x).mp hx).2.1) ((hSmem x).mp hxS).2.symm
  have haS : a ∉ S := hEmS haEm
  have hbS : b ∉ S := hEpS hbEp
  have hDcClosed : IsClosed Dc :=
    (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd (hf.comp continuous_fst))
  have hSphereCompact : IsCompact (univ : Set UnitTwoSphere) := isCompact_univ
  obtain ⟨vmax, _, hmax⟩ := hSphereCompact.exists_isMaxOn
    ⟨q, mem_univ _⟩ hf.continuousOn
  have hDcCompact : IsCompact Dc := by
    have hprod := hSphereCompact.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) (f vmax)))
    apply hprod.of_isClosed_subset hDcClosed
    intro z hz
    exact ⟨mem_univ _, hz.1, hz.2.trans (hmax (mem_univ z.1))⟩
  have hKcompact : IsCompact K := C.closed_core_compact.union
    (hDcCompact.image_of_continuousOn (R.coordinate_map_smooth.continuousOn.mono hDc))
  have hKsub : K ⊆ C.carrier := by
    rintro x (hx | ⟨z, hz, rfl⟩)
    · exact hKC hx
    · exact hRsub (R.coordinate_map_mem (hDc hz))
  have hUK : U ⊆ K := by
    rintro x (hx | ⟨z, hz, rfl⟩)
    · exact Or.inl (hcoreK hx)
    · by_cases hneg : z.2 < 0
      · apply Or.inl
        apply hcoreK
        have hxneg : R.coordinate_map z ∈ R.region (-L) 0 := by
          refine ⟨R.coordinate_map_mem (hDm hz), ?_⟩
          rw [R.coordinate_inverse_coordinate_map (hDm hz)]
          exact ⟨hz.1, hneg⟩
        exact (show R.coordinate_map z ∈ R.carrier ∩ C.core from
          hcore.symm ▸ hxneg).2
      · exact Or.inr ⟨z, ⟨le_of_not_gt hneg, hz.2.le⟩, rfl⟩
  have hUopen : IsOpen U := hcoreOpen.union hEmOpen
  have hline (v : UnitTwoSphere) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      ContinuousAt (fun s : ℝ => R.coordinate_map (v, s)) t := by
    have hdom : (v, t) ∈ R.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, hepsilon]
      exact ⟨mem_univ _, ht⟩
    have hc : ContinuousAt R.coordinate_map (v, t) :=
      R.coordinate_map_smooth.continuousOn.continuousAt
        (R.cylinderDomain_open.mem_nhds hdom)
    exact hc.comp (continuous_const.prodMk continuous_id).continuousAt
  have hSclm : S ⊆ closure Em := by
    rintro x ⟨v, rfl⟩
    let l := (f v - L) / 2
    have hl : -L < l := by dsimp only [l]; linarith only [hL, (hfdom v).1]
    have hlf : l < f v := by dsimp only [l]; linarith only [hL, (hfdom v).1]
    have hc : ContinuousWithinAt (fun t : ℝ => R.coordinate_map (v, t))
        (Ioo l (f v)) (f v) := (hline v (hfd v)).continuousWithinAt
    apply hc.mem_closure
    · rw [closure_Ioo (ne_of_lt hlf)]
      exact ⟨hlf.le, le_rfl⟩
    · intro t ht
      exact ⟨(v, t), ⟨hl.trans ht.1, ht.2⟩, rfl⟩
  have hSclp : S ⊆ closure Ep := by
    rintro x ⟨v, rfl⟩
    let r := (f v + L) / 2
    have hfr : f v < r := by dsimp only [r]; linarith only [(hfdom v).2]
    have hr : r < L := by dsimp only [r]; linarith only [(hfdom v).2]
    have hc : ContinuousWithinAt (fun t : ℝ => R.coordinate_map (v, t))
        (Ioo (f v) r) (f v) := (hline v (hfd v)).continuousWithinAt
    apply hc.mem_closure
    · rw [closure_Ioo (ne_of_lt hfr)]
      exact ⟨le_rfl, hfr.le⟩
    · intro t ht
      exact ⟨(v, t), ⟨ht.1, ht.2.trans hr⟩, rfl⟩
  have hKclU : K ⊆ closure U := by
    rintro x (hx | ⟨z, hz, rfl⟩)
    · rw [← C.m25_closure_core_eq_closed_core] at hx
      exact closure_mono (fun _ hy => Or.inl hy) hx
    · by_cases hlt : z.2 < f z.1
      · apply subset_closure
        exact Or.inr ⟨z, ⟨(neg_lt_zero.mpr hL).trans_le hz.1, hlt⟩, rfl⟩
      · have heq : z.2 = f z.1 := le_antisymm hz.2 (le_of_not_gt hlt)
        have hxS : R.coordinate_map z ∈ S := by
          refine ⟨z.1, congrArg R.coordinate_map ?_⟩
          exact Prod.ext rfl heq.symm
        exact closure_mono (fun _ hy => Or.inr hy) (hSclm hxS)
  have hUclosure : closure U = K :=
    Subset.antisymm (closure_minimal hUK hKcompact.isClosed) hKclU
  have hSK : S ⊆ K := by
    intro x hx
    rw [← hUclosure]
    exact closure_mono (fun _ hy => Or.inr hy) (hSclm hx)
  have hUfront : frontier U = S := by
    rw [hUopen.frontier_eq, hUclosure]
    apply Subset.antisymm
    · rintro x ⟨hxK, hxU⟩
      rcases hxK with hxc | hxband
      · have hxcentral := (R.mem_central_sphere_iff x).mp
          (hboundary x hxc (fun hx => hxU (Or.inl hx)))
        apply (hSmem x).mpr
        refine ⟨hxcentral.1, ?_⟩
        have hnotpos : ¬ 0 < f (R.coordinate_inverse x).1 := by
          intro hpos
          apply hxU
          apply Or.inr
          apply (hEmmem x).mpr
          refine ⟨hxcentral.1, ?_, ?_⟩
          · rw [hxcentral.2]
            exact neg_lt_zero.mpr hL
          · rw [hxcentral.2]
            exact hpos
        have hfzero : f (R.coordinate_inverse x).1 = 0 :=
          le_antisymm (le_of_not_gt hnotpos) (hfdom _).1
        exact hxcentral.2.trans hfzero.symm
      · obtain ⟨z, hz, rfl⟩ := hxband
        have heq : z.2 = f z.1 := by
          apply le_antisymm hz.2
          apply le_of_not_gt
          intro hlt
          exact hxU (Or.inr ⟨z,
            ⟨(neg_lt_zero.mpr hL).trans_le hz.1, hlt⟩, rfl⟩)
        exact ⟨z.1, congrArg R.coordinate_map (Prod.ext rfl heq.symm)⟩
    · intro x hx
      exact ⟨hSK hx, hSU hx⟩
  have hSclosed : IsClosed S := by rw [← hUfront]; exact isClosed_frontier
  have hEmA : Em ⊆ A := hEmConnected.isPreconnected.subset_connectedComponentIn haEm hEmS
  have hEpB : Ep ⊆ B := hEpConnected.isPreconnected.subset_connectedComponentIn hbEp hEpS
  have hAopen : IsOpen A := hSclosed.isOpen_compl.connectedComponentIn
  have hBopen : IsOpen B := hSclosed.isOpen_compl.connectedComponentIn
  have hAsub : A ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hBsub : B ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hApre : IsPreconnected A := isPreconnected_connectedComponentIn
  have hAU : A ⊆ U := by
    apply hApre.subset_of_closure_inter_subset hUopen ⟨a, hEmA haEm, Or.inr haEm⟩
    intro x hx
    by_contra hxU
    have hxfront : x ∈ frontier U := by
      rw [hUopen.frontier_eq]
      exact ⟨hx.1, hxU⟩
    exact hAsub hx.2 (hUfront ▸ hxfront)
  have hUR : U ∩ R.carrier ⊆ Em := by
    rintro x ⟨hxc | hxm, hxR⟩
    · have hneg : x ∈ R.region (-L) 0 := hcore ▸ ⟨hxR, hxc⟩
      exact (hEmmem x).mpr ⟨hxR, hneg.2.1,
        hneg.2.2.trans_le (hfdom (R.coordinate_inverse x).1).1⟩
    · exact hxm
  have hUEnd : U ∩ C.end_neck.carrier ⊆ Em := by
    rintro x ⟨hxc | hxm, hxEnd⟩
    · exact (disjoint_left.mp hcoreEnd hxc hxEnd).elim
    · exact hxm
  have hcover : C.carrier ⊆ U ∪ R.carrier ∪ C.end_neck.carrier := by
    intro x hx
    by_cases hxEnd : x ∈ C.end_neck.carrier
    · exact Or.inr hxEnd
    · have hxK : x ∈ C.closed_core := by
        rw [C.closed_core_eq_complement_end]
        exact ⟨hx, hxEnd⟩
      by_cases hxc : x ∈ C.core
      · exact Or.inl (Or.inl (Or.inl hxc))
      · exact Or.inl (Or.inr (R.central_sphere_subset (hboundary x hxK hxc)))

  let P := A ∪ R.carrier ∪ C.end_neck.carrier
  let Q := U ∩ (closure A)ᶜ
  have hPopen : IsOpen P := (hAopen.union R.carrier_open).union C.end_neck.carrier_open
  have hQopen : IsOpen Q := hUopen.inter isClosed_closure.isOpen_compl
  have hclA : closure A ⊆ A ∪ S :=
    Poincare.Topology.closure_connectedComponentIn_compl_subset hSclosed a
  have hPQcover : C.carrier ⊆ P ∪ Q := by
    intro x hx
    rcases hcover hx with (hxU | hxR) | hxEnd
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl (Or.inl hxA))
      · refine Or.inr ⟨hxU, ?_⟩
        intro hxclosure
        rcases hclA hxclosure with hxA' | hxS
        · exact hxA hxA'
        · exact hSU hxS hxU
    · exact Or.inl (Or.inl (Or.inr hxR))
    · exact Or.inl (Or.inr hxEnd)
  have hPQdisjoint : Disjoint P Q := by
    apply disjoint_left.mpr
    intro x hxP hxQ
    rcases hxP with (hxA | hxR) | hxEnd
    · exact hxQ.2 (subset_closure hxA)
    · exact hxQ.2 (subset_closure (hEmA (hUR ⟨hxQ.1, hxR⟩)))
    · exact hxQ.2 (subset_closure (hEmA (hUEnd ⟨hxQ.1, hxEnd⟩)))
  have hCP : C.carrier ⊆ P := by
    rcases C.m25_isConnected_carrier.isPreconnected.subset_or_subset
        hPopen hQopen hPQdisjoint hPQcover with hCP | hCQ
    · exact hCP
    · have haC : a ∈ C.carrier := hRsub ((hEmmem a).mp haEm).1
      exact (disjoint_left.mp hPQdisjoint (Or.inl (Or.inl (hEmA haEm)))
        (hCQ haC)).elim
  have hUA : U ⊆ A := by
    intro x hxU
    rcases hCP (hKsub (hUK hxU)) with (hxA | hxR) | hxEnd
    · exact hxA
    · exact hEmA (hUR ⟨hxU, hxR⟩)
    · exact hEmA (hUEnd ⟨hxU, hxEnd⟩)
  have hUAeq : U = A := Subset.antisymm hUA hAU
  have hAclosure : closure A = K := by rw [← hUAeq]; exact hUclosure
  have hAfront : frontier A = S := by rw [← hUAeq]; exact hUfront
  have hne : A ≠ B := by
    intro hAB
    have hbA : b ∈ A := hAB.symm ▸ hEpB hbEp
    exact hEpU hbEp (hAU hbA)
  have hBfront : frontier B = S := by
    rw [hBopen.frontier_eq]
    apply Subset.antisymm
    · intro x hx
      rcases Poincare.Topology.closure_connectedComponentIn_compl_subset
          hSclosed b hx.1 with hxB | hxS
      · exact (hx.2 hxB).elim
      · exact hxS
    · intro x hxS
      exact ⟨closure_mono hEpB (hSclp hxS), fun hxB => hBsub hxB hxS⟩
  refine ⟨hUAeq, hAclosure, ?_, ?_, ?_, haS, hbS, hne, hAfront, hBfront⟩
  · rw [hAclosure]
    exact hKcompact
  · rw [hAclosure]
    exact hKsub
  · rw [hAclosure]
    exact fun _ hx => Or.inl hx

end PoincareConjecture
