import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBoundaryOrientation
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCommonSphereComponent

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.full_end_subset_of_boundary_in_cap_extension
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C0 C1 : CapCertificate g)
    (U V : TopologicalSpace.Opens M)
    (hV : (V : Set M) = C0.carrier ∪ (U : Set M))
    (hfirst : C0.carrier ∩ (U : Set M) = C0.end_neck.carrier)
    (d : V ≃ₜ (⟨C0.carrier, C0.carrier_open⟩ : TopologicalSpace.Opens M))
    (hdisjoint : Disjoint C0.closed_core C1.carrier)
    (hboundary : C1.boundary_sphere ⊆ (V : Set M))
    (y : M) (hycore : y ∈ C1.core)
    (hyclosure : y ∈ closure (V : Set M)) (hyout : y ∉ (V : Set M)) :
    let W := (V : Set M) ∪ C1.carrier
    C1.boundary_sphere ⊆ (U : Set M) ∧
      C1.end_neck.carrier ⊆ (U : Set M) ∧
      C1.carrier ∩ (U : Set M) =
        C1.end_neck.carrier ∪ C1.boundary_sphere ∪
          (C1.core ∩ (U : Set M)) ∧
      C1.carrier \ (U : Set M) = W \ (V : Set M) ∧
      IsCompact (C1.carrier \ (U : Set M)) ∧
      C1.carrier \ (U : Set M) ⊆ C1.core ∧
      y ∈ C1.carrier \ (U : Set M) := by
  classical
  let W : Set M := (V : Set M) ∪ C1.carrier
  have hUV : (U : Set M) ⊆ (V : Set M) := by
    intro x hx
    rw [hV]
    exact Or.inr hx
  have hVU : (V : Set M) \ (U : Set M) = C0.closed_core := by
    rw [C0.closed_core_eq_complement_end]
    ext x
    constructor
    · intro hx
      have hxC : x ∈ C0.carrier := by
        rcases hV ▸ hx.1 with hxC | hxU
        · exact hxC
        · exact False.elim (hx.2 hxU)
      refine ⟨hxC, ?_⟩
      intro hxE
      have hxCU : x ∈ C0.carrier ∩ (U : Set M) := hfirst.symm ▸ hxE
      exact hx.2 hxCU.2
    · intro hx
      refine ⟨?_, ?_⟩
      · rw [hV]
        exact Or.inl hx.1
      · intro hxU
        exact hx.2 (hfirst ▸ (show x ∈ C0.carrier ∩ (U : Set M) from ⟨hx.1, hxU⟩))
  have hmove (x : M) (hxC : x ∈ C1.carrier) (hxV : x ∈ (V : Set M)) :
      x ∈ (U : Set M) := by
    by_contra hxU
    have hxK : x ∈ C0.closed_core :=
      hVU ▸ (show x ∈ (V : Set M) \ (U : Set M) from ⟨hxV, hxU⟩)
    exact disjoint_left.mp hdisjoint hxK hxC
  have hboundaryU : C1.boundary_sphere ⊆ (U : Set M) := by
    intro x hx
    exact hmove x (C1.boundary_subset hx) (hboundary hx)
  obtain ⟨R, hR, hRepsilon, _, hRsphere, hcore, _⟩ :=
    C1.exists_outward_boundary_neck
  let L := C1.epsilon⁻¹
  let f : UnitTwoSphere → ℝ := fun _ => 0
  let q := (R.coordinate_inverse R.center).1
  let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, f v))
  let a := R.coordinate_map (q, -L / 2)
  let b := R.coordinate_map (q, (f q + L) / 2)
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  have hL : 0 < L := inv_pos.mpr C1.epsilon_pos
  have hf : Continuous f := continuous_const
  have hfdom : ∀ v, f v ∈ Ico (0 : ℝ) C1.epsilon⁻¹ :=
    fun _ => ⟨le_rfl, hL⟩
  have hS : S = C1.boundary_sphere := by
    change range (fun v : UnitTwoSphere => R.coordinate_map (v, 0)) = _
    rw [← hRsphere, R.central_sphere_eq]
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨(v, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨v, t⟩, ⟨_, ht⟩, hx⟩
      have ht' : t = 0 := ht
      subst t
      exact ⟨v, hx⟩
  have hAeq := (C1.outward_graph_compact_side R hR hcore f hf hfdom).1
  change C1.core ∪ R.coordinate_map ''
    {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < f z.1} = A at hAeq
  have hnegative : R.coordinate_map ''
      {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < f z.1} ⊆ C1.core := by
    rintro x ⟨z, hz, rfl⟩
    change -L < z.2 ∧ z.2 < 0 at hz
    have hzs : z ∈ R.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, hRepsilon]
      exact ⟨mem_univ _, hz.1, hz.2.trans hL⟩
    have hxneg : R.coordinate_map z ∈ R.region (-L) 0 := by
      refine ⟨R.coordinate_map_mem hzs, ?_⟩
      rw [R.coordinate_inverse_coordinate_map hzs]
      exact hz
    exact (show R.coordinate_map z ∈ R.carrier ∩ C1.core from hcore.symm ▸ hxneg).2
  have hAcore : A = C1.core := by
    apply Subset.antisymm
    · rw [← hAeq]
      exact union_subset subset_rfl hnegative
    · intro x hx
      rw [← hAeq]
      exact Or.inl hx
  have hAcl : closure A = C1.closed_core := by
    rw [hAcore, C1.m25_closure_core_eq_closed_core]
  have hlevel : range (fun v : UnitTwoSphere => R.coordinate_map (v, f v)) =
      range (fun v : UnitTwoSphere => R.coordinate_map (v, 0)) := rfl
  have hSV : range (fun v : UnitTwoSphere => R.coordinate_map (v, f v)) ⊆
      (V : Set M) := by
    change S ⊆ (V : Set M)
    rw [hS]
    exact hboundary
  obtain ⟨_, _, _, _, _, _, _, hBV, _, _, hcover, hWcompact, _, _, _⟩ :=
    C0.compact_union_component_of_common_outward_graph C1 V d R hR hcore f hf hfdom
      R 0 R.zero_mem_interval hlevel hSV y hycore hyclosure hyout
  change closure B ⊆ (V : Set M) at hBV
  change W = closure A ∪ closure B at hcover
  change IsCompact W at hWcompact
  have hendU : C1.end_neck.carrier ⊆ (U : Set M) := by
    intro x hx
    have hxW : x ∈ W := Or.inr (C1.end_neck_subset hx)
    have hxparts : x ∈ closure A ∪ closure B := hcover ▸ hxW
    apply hmove x (C1.end_neck_subset hx)
    apply hBV
    rcases hxparts with hxA | hxB
    · have hxK : x ∈ C1.closed_core := hAcl ▸ hxA
      rw [C1.closed_core_eq_complement_end] at hxK
      exact False.elim (hxK.2 hx)
    · exact hxB
  have hdecomp : C1.carrier =
      C1.end_neck.carrier ∪ C1.boundary_sphere ∪ C1.core := by
    ext x
    constructor
    · intro hx
      by_cases hxE : x ∈ C1.end_neck.carrier
      · exact Or.inl (Or.inl hxE)
      have hxK : x ∈ C1.closed_core := by
        rw [C1.closed_core_eq_complement_end]
        exact ⟨hx, hxE⟩
      by_cases hxc : x ∈ C1.core
      · exact Or.inr hxc
      apply Or.inl
      apply Or.inr
      rw [← C1.core_frontier_eq_boundary]
      refine ⟨subset_closure hxK, ?_⟩
      intro hxi
      apply hxc
      rwa [C1.core_eq_interior_closed_core]
    · rintro ((hx | hx) | hx)
      · exact C1.end_neck_subset hx
      · exact C1.boundary_subset hx
      · exact C1.m25_core_subset_carrier hx
  have hoverlap : C1.carrier ∩ (U : Set M) =
      C1.end_neck.carrier ∪ C1.boundary_sphere ∪ (C1.core ∩ (U : Set M)) := by
    ext x
    constructor
    · intro hx
      rcases hdecomp ▸ hx.1 with (hxE | hxS) | hxc
      · exact Or.inl (Or.inl hxE)
      · exact Or.inl (Or.inr hxS)
      · exact Or.inr ⟨hxc, hx.2⟩
    · rintro ((hxE | hxS) | ⟨hxc, hxU⟩)
      · exact ⟨C1.end_neck_subset hxE, hendU hxE⟩
      · exact ⟨C1.boundary_subset hxS, hboundaryU hxS⟩
      · exact ⟨C1.m25_core_subset_carrier hxc, hxU⟩
  have hdiff : C1.carrier \ (U : Set M) = W \ (V : Set M) := by
    ext x
    constructor
    · intro hx
      exact ⟨Or.inr hx.1, fun hxV => hx.2 (hmove x hx.1 hxV)⟩
    · rintro ⟨hxW, hxV⟩
      rcases hxW with hxV' | hxC
      · exact False.elim (hxV hxV')
      · exact ⟨hxC, fun hxU => hxV (hUV hxU)⟩
  have hcompact : IsCompact (C1.carrier \ (U : Set M)) := by
    rw [hdiff]
    exact hWcompact.diff V.isOpen
  have hmiss : C1.carrier \ (U : Set M) ⊆ C1.core := by
    intro x hx
    rcases hdecomp ▸ hx.1 with (hxE | hxS) | hxc
    · exact False.elim (hx.2 (hendU hxE))
    · exact False.elim (hx.2 (hboundaryU hxS))
    · exact hxc
  exact ⟨hboundaryU, hendU, hoverlap, hdiff, hcompact, hmiss,
    C1.m25_core_subset_carrier hycore, fun hyU => hyout (hUV hyU)⟩

end PoincareConjecture
