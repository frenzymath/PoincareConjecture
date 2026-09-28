import PoincareConjecture.Proofs.M25.AppA_21_Local.CapGraphCompactSide
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapLowerCutComponent
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrderedChainCuts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.closed_cores_disjoint_of_last_slice_outward_graph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C0 C1 : CapCertificate g) (D : BalancedNeckChain g C0.epsilon)
    {a b : ℤ} (hshape : D.shape = ChainShape.finite a b)
    (hstart : D.neck a = C0.end_neck)
    (hsep : ∀ i ∈ D.shape.active, (D.neck i).IsSeparating)
    {t : ℝ} (ht : t ∈ Ioo (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹)
    (R : EpsilonNeck g)
    (hR : R = C1.boundary_neck ∨ R = C1.boundary_neck.reverse)
    (hcore : R.carrier ∩ C1.core = R.region (-C1.epsilon⁻¹) 0)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hfdom : ∀ q, f q ∈ Ico (0 : ℝ) C1.epsilon⁻¹)
    (hlevel :
      range (fun q : UnitTwoSphere => (D.neck b).coordinate_map (q, t)) =
      range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)))
    (y : M) (hycore : y ∈ C1.core)
    (hyclosure : y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹))
    (hyout : y ∉ C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)) :
    let L := C0.epsilon⁻¹
    let N := D.neck b
    let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
    let q := (N.coordinate_inverse N.center).1
    let A := connectedComponentIn Sᶜ (N.coordinate_map (q, (t - L) / 2))
    let B := connectedComponentIn Sᶜ (N.coordinate_map (q, (t + L) / 2))
    let K0 := C0.carrier \ C0.end_neck.region (L / 2) L
    K0 ⊆ A ∧ C1.closed_core ⊆ closure B ∧
      Disjoint K0 C1.closed_core ∧ Disjoint C0.closed_core C1.closed_core := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := C0.epsilon⁻¹
  let N := D.neck b
  let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
  let q := (N.coordinate_inverse N.center).1
  let A := connectedComponentIn Sᶜ (N.coordinate_map (q, (t - L) / 2))
  let B := connectedComponentIn Sᶜ (N.coordinate_map (q, (t + L) / 2))
  let K0 := C0.carrier \ C0.end_neck.region (L / 2) L
  let A0 : ℤ → ℝ → Set M := fun i s =>
    connectedComponentIn (range (fun v : UnitTwoSphere =>
      (D.neck i).coordinate_map (v, s)))ᶜ
      ((D.neck i).coordinate_map (((D.neck i).coordinate_inverse
        (D.neck i).center).1, (s - L) / 2))
  change K0 ⊆ A ∧ C1.closed_core ⊆ closure B ∧
    Disjoint K0 C1.closed_core ∧ Disjoint C0.closed_core C1.closed_core
  have hL : 0 < L := inv_pos.mpr C0.epsilon_pos
  have hactive (i : ℤ) : i ∈ D.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ D.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ D.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have htStrict : t ∈ Ioo (L / 2) L := ht
  have htDom : t ∈ Ioo (-L) L := by
    exact ⟨by linarith only [hL, htStrict.1], htStrict.2⟩
  obtain ⟨H, _, hH, _, _, hcomponents, horder⟩ :=
    D.exists_ordered_saturated_heights hsep
  let F := H b
  let K := connectedComponent N.center
  have hFc : Continuous F := (hH b hb).1
  have hFin (x : M) (hx : x ∈ N.carrier) : F x = (N.coordinate_inverse x).2 :=
    (hH b hb).2.1 x hx
  have hplateau (x : M) (hx : x ∈ K \ N.carrier) : F x = -L ∨ F x = L :=
    (hH b hb).2.2.1 x hx
  obtain ⟨hAeq, hBeq, _⟩ := hcomponents b hb t htDom
  change A = K ∩ F ⁻¹' Iio t at hAeq
  change B = K ∩ F ⁻¹' Ioi t at hBeq
  have hK0cut {s : ℝ} (hs : L / 2 < s) :
      K0 ⊆ C0.closed_core ∪ C0.end_neck.region (-L) s := by
    intro x hx
    by_cases hxN : x ∈ C0.end_neck.carrier
    · apply Or.inr
      have hcoord := (C0.end_neck.coordinate_inverse_mem x hxN).2
      have hlo : -L < (C0.end_neck.coordinate_inverse x).2 := by
        simpa only [C0.end_neck_epsilon] using hcoord.1
      have hhi : (C0.end_neck.coordinate_inverse x).2 < L := by
        simpa only [C0.end_neck_epsilon] using hcoord.2
      have hhalf : (C0.end_neck.coordinate_inverse x).2 ≤ L / 2 := by
        by_contra h
        exact hx.2 ⟨hxN, lt_of_not_ge h, hhi⟩
      exact ⟨hxN, hlo, hhalf.trans_lt hs⟩
    · apply Or.inl
      rw [C0.closed_core_eq_complement_end]
      exact ⟨hx.1, hxN⟩
  have hcut (s : ℝ) (hs : s ∈ Ioo (-L) L) :
      C0.closed_core ∪ C0.end_neck.region (-L) s = A0 a s := by
    simpa only [A0, hstart] using (C0.end_neck_lower_cut_eq_negative_component hs).1
  have hK0A : K0 ⊆ A := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · have hsub : K0 ⊆ A0 a t := by
        rw [← hcut t htDom]
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
  have hclosureK : closure (N.region 0 L) ⊆ K :=
    closure_minimal (fun _ hx => N.m25_carrier_subset_connectedComponent hx.1)
      isClosed_connectedComponent
  have hclosureNonneg : closure (N.region 0 L) ⊆ {x | 0 ≤ F x} := by
    apply closure_minimal ?_ (isClosed_le continuous_const hFc)
    intro x hx
    change 0 ≤ F x
    rw [hFin x hx.1]
    exact hx.2.1.le
  have hyN : y ∉ N.carrier := by
    intro hy
    apply hyout
    exact Or.inr (mem_iUnion₂.mpr ⟨b, hb, hy⟩)
  have hFy : F y = L := by
    rcases hplateau y ⟨hclosureK hyclosure, hyN⟩ with hnegative | hpositive
    · have hnonneg := hclosureNonneg hyclosure
      change 0 ≤ F y at hnonneg
      rw [hnegative] at hnonneg
      exact (not_le_of_gt hL (by linarith only [hnonneg])).elim
    · exact hpositive
  have hyB : y ∈ B := by
    rw [hBeq]
    refine ⟨hclosureK hyclosure, ?_⟩
    change t < F y
    rw [hFy]
    exact htStrict.2
  let r := (R.coordinate_inverse R.center).1
  let AR := connectedComponentIn
    (range (fun v : UnitTwoSphere => R.coordinate_map (v, f v)))ᶜ
    (R.coordinate_map (r, -C1.epsilon⁻¹ / 2))
  have hside := C1.outward_graph_compact_side R hR hcore f hf hfdom
  have hC1A : C1.closed_core ⊆ closure AR := hside.2.2.2.2.1
  have hyAR : y ∈ AR := by
    dsimp only [AR, r]
    rw [← hside.1]
    exact Or.inl hycore
  have hyAR' : y ∈ connectedComponentIn Sᶜ
      (R.coordinate_map (r, -C1.epsilon⁻¹ / 2)) := by
    dsimp only [S, N]
    rw [hlevel]
    exact hyAR
  have hARB : AR = B := by
    dsimp only [AR]
    rw [← hlevel]
    exact (connectedComponentIn_eq hyAR').trans (connectedComponentIn_eq hyB).symm
  have hC1B : C1.closed_core ⊆ closure B := by
    rw [← hARB]
    exact hC1A
  have hclosureB : closure B ⊆ {x | t ≤ F x} := by
    apply closure_minimal ?_ (isClosed_le continuous_const hFc)
    intro x hx
    rw [hBeq] at hx
    exact (show t < F x from hx.2).le
  have hdisj : Disjoint K0 C1.closed_core := by
    apply disjoint_left.mpr
    intro x hx0 hx1
    have hxA := hK0A hx0
    rw [hAeq] at hxA
    exact (not_le_of_gt (show F x < t from hxA.2)) (hclosureB (hC1B hx1))
  have hC0K0 : C0.closed_core ⊆ K0 := by
    intro x hx
    rw [C0.closed_core_eq_complement_end] at hx
    exact ⟨hx.1, fun h => hx.2 h.1⟩
  exact ⟨hK0A, hC1B, hdisj, hdisj.mono_left hC0K0⟩

end PoincareConjecture
