import PoincareConjecture.Proofs.M25.AppA_21_Local.CapLowerCutComponent
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrderedChainCuts
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCoreContact
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Reversal

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.finite_chain_mixed_boundary_side_alternative
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C C' : CapCertificate g) (D : BalancedNeckChain g C.epsilon)
    {a b : ℤ} (hshape : D.shape = ChainShape.finite a b)
    (hstart : D.neck a = C.end_neck)
    (hsep : ∀ i ∈ D.shape.active, (D.neck i).IsSeparating)
    (R : EpsilonNeck g) (f : UnitTwoSphere → ℝ)
    (hR : R = C'.boundary_neck ∨ R = C'.boundary_neck.reverse)
    (hfdom : ∀ q, f q ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹)
    (hfnegative : ∀ q, f q < 0)
    (hgraph :
      range (fun q : UnitTwoSphere =>
        (D.neck b).coordinate_map (q, 3 * C.epsilon⁻¹ / 4)) =
      range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)))
    (y z : M) (hycore : y ∈ C'.core)
    (hyclosure : y ∈ closure ((D.neck b).region 0 C.epsilon⁻¹))
    (hyout : y ∉ C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier))
    (hzsphere : z ∈ C'.boundary_sphere)
    (hzclosure : z ∈ closure ((D.neck b).region 0 C.epsilon⁻¹))
    (hzout : z ∉ (D.neck b).carrier) :
    let L := C.epsilon⁻¹
    let N := D.neck b
    let t := 3 * L / 4
    let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
    let q := (N.coordinate_inverse N.center).1
    let A := connectedComponentIn Sᶜ (N.coordinate_map (q, (t - L) / 2))
    let B := connectedComponentIn Sᶜ (N.coordinate_map (q, (t + L) / 2))
    let K0 := C.carrier \ C.end_neck.region (L / 2) L
    K0 ⊆ A ∧ C'.boundary_sphere ⊆ B ∧ y ∈ B ∧ y ≠ z ∧
      (S ⊆ C'.end_neck.carrier ∨ (A ⊆ C'.core ∧ K0 ⊆ C'.core)) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := C.epsilon⁻¹
  let N := D.neck b
  let t := 3 * L / 4
  let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
  let q := (N.coordinate_inverse N.center).1
  let A := connectedComponentIn Sᶜ (N.coordinate_map (q, (t - L) / 2))
  let B := connectedComponentIn Sᶜ (N.coordinate_map (q, (t + L) / 2))
  let K0 := C.carrier \ C.end_neck.region (L / 2) L
  let A0 : ℤ → ℝ → Set M := fun i s =>
    connectedComponentIn (range (fun v : UnitTwoSphere =>
      (D.neck i).coordinate_map (v, s)))ᶜ
      ((D.neck i).coordinate_map (((D.neck i).coordinate_inverse
        (D.neck i).center).1, (s - L) / 2))
  change K0 ⊆ A ∧ C'.boundary_sphere ⊆ B ∧ y ∈ B ∧ y ≠ z ∧
    (S ⊆ C'.end_neck.carrier ∨ (A ⊆ C'.core ∧ K0 ⊆ C'.core))
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hactive (i : ℤ) : i ∈ D.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ D.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ D.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have heN : N.epsilon = C.epsilon := D.epsilon_eq b hb
  have ht : t ∈ Ioo (-L) L := by
    dsimp only [t]
    constructor <;> linarith only [hL]
  have htStrict : t ∈ Ioo (L / 2) L := by
    dsimp only [t]
    constructor <;> linarith only [hL]
  have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [heN] using ht
  obtain ⟨H, _, hH, _, _, hcomponents, horder⟩ :=
    D.exists_ordered_saturated_heights hsep
  let F := H b
  let K := connectedComponent N.center
  have hFc : Continuous F := (hH b hb).1
  have hFin (x : M) (hx : x ∈ N.carrier) : F x = (N.coordinate_inverse x).2 :=
    (hH b hb).2.1 x hx
  have hplateau (x : M) (hx : x ∈ K \ N.carrier) : F x = -L ∨ F x = L :=
    (hH b hb).2.2.1 x hx
  obtain ⟨hAeq, hBeq, hfront, _, _⟩ := hcomponents b hb t ht
  change A = K ∩ F ⁻¹' Iio t at hAeq
  change B = K ∩ F ⁻¹' Ioi t at hBeq
  change frontier A = S at hfront
  have hK0cut {s : ℝ} (hs : L / 2 < s) :
      K0 ⊆ C.closed_core ∪ C.end_neck.region (-L) s := by
    intro x hx
    by_cases hxN : x ∈ C.end_neck.carrier
    · apply Or.inr
      have hcoord := (C.end_neck.coordinate_inverse_mem x hxN).2
      have hlo : -L < (C.end_neck.coordinate_inverse x).2 := by
        simpa only [C.end_neck_epsilon] using hcoord.1
      have hhi : (C.end_neck.coordinate_inverse x).2 < L := by
        simpa only [C.end_neck_epsilon] using hcoord.2
      have hhalf : (C.end_neck.coordinate_inverse x).2 ≤ L / 2 := by
        by_contra h
        exact hx.2 ⟨hxN, lt_of_not_ge h, hhi⟩
      exact ⟨hxN, hlo, hhalf.trans_lt hs⟩
    · apply Or.inl
      rw [C.closed_core_eq_complement_end]
      exact ⟨hx.1, hxN⟩
  have hcut (s : ℝ) (hs : s ∈ Ioo (-L) L) :
      C.closed_core ∪ C.end_neck.region (-L) s = A0 a s := by
    simpa only [A0, hstart] using (C.end_neck_lower_cut_eq_negative_component hs).1
  have hK0A : K0 ⊆ A := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · have hsub : K0 ⊆ A0 a t := by
        rw [← hcut t ht]
        exact hK0cut htStrict.1
      simpa only [heq] using hsub
    · have hs : 5 * L / 8 ∈ Ioo (-L) L := by
        constructor <;> linarith only [hL]
      have hsStrict : 5 * L / 8 ∈ Ioo (L / 2) L := by
        constructor <;> linarith only [hL]
      have hsub : K0 ⊆ A0 a (5 * L / 8) := by
        rw [← hcut (5 * L / 8) hs]
        exact hK0cut hsStrict.1
      have hordered := (horder a ha b hb hlt (5 * L / 8) hsStrict t htStrict).1
      change closure (A0 a (5 * L / 8)) ⊆ A at hordered
      exact hsub.trans (subset_closure.trans hordered)
  have hgraphS : S = range (fun v : UnitTwoSphere => R.coordinate_map (v, f v)) := hgraph
  have hSN : S ⊆ N.carrier := by
    rintro x ⟨v, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _, htN⟩
  have hSR : S ⊆ R.carrier := by
    rw [hgraphS]
    rintro x ⟨v, rfl⟩
    exact R.coordinate_map_mem ⟨mem_univ _, hfdom v⟩
  have hpS : N.coordinate_map (q, t) ∈ S := ⟨q, rfl⟩
  have hcomponent : connectedComponent R.center = K :=
    (connectedComponent_eq (R.m25_carrier_subset_connectedComponent (hSR hpS))).trans
      (connectedComponent_eq (N.m25_carrier_subset_connectedComponent (hSN hpS))).symm
  have hRK : R.carrier ⊆ K := by
    rw [← hcomponent]
    exact R.m25_carrier_subset_connectedComponent
  have hRcarrier : R.carrier = C'.boundary_neck.carrier := by
    rcases hR with rfl | rfl <;> rfl
  have hRcentral : R.central_sphere = C'.boundary_sphere := by
    rcases hR with rfl | rfl <;> exact C'.boundary_eq_neck_sphere.symm
  have hRcap : R.carrier ⊆ C'.carrier := by
    rw [hRcarrier]
    exact C'.boundary_neck_subset
  have hBoundaryR : C'.boundary_sphere ⊆ R.carrier := by
    rw [← hRcentral]
    exact R.central_sphere_subset
  have hBoundaryK : C'.boundary_sphere ⊆ K := hBoundaryR.trans hRK
  have hSboundary : Disjoint S C'.boundary_sphere := by
    apply disjoint_left.mpr
    intro x hxS hxBoundary
    have hxcentral : x ∈ R.central_sphere := by rw [hRcentral]; exact hxBoundary
    have hxzero := ((R.mem_central_sphere_iff x).mp hxcentral).2
    rw [hgraphS] at hxS
    obtain ⟨v, hv⟩ := hxS
    rw [← hv, R.coordinate_inverse_map (v, f v) (hfdom v)] at hxzero
    exact (hfnegative v).ne hxzero
  have hclosureK : closure (N.region 0 L) ⊆ K :=
    closure_minimal (fun _ hx => N.m25_carrier_subset_connectedComponent hx.1)
      isClosed_connectedComponent
  have hclosureNonneg : closure (N.region 0 L) ⊆ {x | 0 ≤ F x} := by
    apply closure_minimal ?_ (isClosed_le continuous_const hFc)
    intro x hx
    change 0 ≤ F x
    rw [hFin x hx.1]
    exact hx.2.1.le
  have hfrontValue {x : M} (hx : x ∈ closure (N.region 0 L))
      (hxout : x ∉ N.carrier) : F x = L := by
    rcases hplateau x ⟨hclosureK hx, hxout⟩ with hnegative | hpositive
    · have hnonneg := hclosureNonneg hx
      change 0 ≤ F x at hnonneg
      rw [hnegative] at hnonneg
      exact (not_le_of_gt hL (by linarith only [hnonneg])).elim
    · exact hpositive
  have hyN : y ∉ N.carrier := by
    intro hy
    apply hyout
    exact Or.inr (mem_iUnion₂.mpr ⟨b, hb, hy⟩)
  have hFy : F y = L := hfrontValue hyclosure hyN
  have hFz : F z = L := hfrontValue hzclosure hzout
  have hlevel (x : M) (hxK : x ∈ K) : F x = t ↔ x ∈ S := by
    by_cases hxN : x ∈ N.carrier
    · rw [hFin x hxN]
      constructor
      · intro hxt
        refine ⟨(N.coordinate_inverse x).1, ?_⟩
        have heq : ((N.coordinate_inverse x).1, t) = N.coordinate_inverse x :=
          Prod.ext rfl hxt.symm
        change N.coordinate_map ((N.coordinate_inverse x).1, t) = x
        rw [heq]
        exact N.coordinate_map_inverse hxN
      · rintro ⟨v, rfl⟩
        exact congrArg Prod.snd (N.coordinate_inverse_map (v, t) htN)
    · have hne : F x ≠ t := by
        intro hxt
        rcases hplateau x ⟨hxK, hxN⟩ with hnegative | hpositive
        · exact (ne_of_lt ht.1) (hnegative.symm.trans hxt)
        · exact (ne_of_gt ht.2) (hpositive.symm.trans hxt)
      exact iff_of_false hne (fun hxS => hxN (hSN hxS))
  have hBoundaryConnected : IsConnected C'.boundary_sphere := by
    rw [C'.boundary_eq_neck_sphere]
    exact C'.boundary_neck.isConnected_central_sphere
  have hBoundaryPositive (x : M) (hx : x ∈ C'.boundary_sphere) : t < F x := by
    apply hBoundaryConnected.isPreconnected.lt_of_ne hFc.continuousOn ?_ ?_ hx
    · intro w hw heq
      exact disjoint_left.mp hSboundary ((hlevel w (hBoundaryK hw)).mp heq) hw
    · exact ⟨z, hzsphere, by rw [hFz]; exact ht.2⟩
  have hBoundaryB : C'.boundary_sphere ⊆ B := by
    intro x hx
    rw [hBeq]
    exact ⟨hBoundaryK hx, hBoundaryPositive x hx⟩
  have hyB : y ∈ B := by
    rw [hBeq]
    refine ⟨hclosureK hyclosure, ?_⟩
    change t < F y
    rw [hFy]
    exact ht.2
  have hyz : y ≠ z := by
    intro heq
    have hyInterior : y ∈ interior C'.closed_core := by
      rw [← C'.core_eq_interior_closed_core]
      exact hycore
    have hyFrontier : y ∈ frontier C'.closed_core := by
      rw [C'.core_frontier_eq_boundary, heq]
      exact hzsphere
    exact disjoint_left.mp disjoint_interior_frontier hyInterior hyFrontier
  have hAavoid : Disjoint A C'.boundary_sphere := by
    apply disjoint_left.mpr
    intro x hxA hxBoundary
    rw [hAeq] at hxA
    exact lt_asymm (show F x < t from hxA.2) (hBoundaryPositive x hxBoundary)
  refine ⟨hK0A, hBoundaryB, hyB, hyz, ?_⟩
  by_cases hgood : S ⊆ C'.end_neck.carrier
  · exact Or.inl hgood
  · apply Or.inr
    obtain ⟨p, hpS, hpout⟩ := Set.not_subset.mp hgood
    have hpClosed : p ∈ C'.closed_core := by
      rw [C'.closed_core_eq_complement_end]
      exact ⟨hRcap (hSR hpS), hpout⟩
    have hpCore : p ∈ C'.core := by
      rw [C'.core_eq_interior_closed_core]
      by_contra hpInterior
      have hpBoundary : p ∈ C'.boundary_sphere := by
        rw [← C'.core_frontier_eq_boundary]
        exact ⟨subset_closure hpClosed, hpInterior⟩
      exact disjoint_left.mp hSboundary hpS hpBoundary
    have hpClosure : p ∈ closure A := by
      apply frontier_subset_closure
      rw [hfront]
      exact hpS
    have hAcore : A ⊆ C'.core := C'.subset_core_of_avoids_boundary
      isPreconnected_connectedComponentIn hAavoid ⟨p, hpClosure, hpCore⟩
    exact ⟨hAcore, hK0A.trans hAcore⟩

end PoincareConjecture
