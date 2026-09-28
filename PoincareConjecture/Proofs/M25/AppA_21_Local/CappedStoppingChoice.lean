import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedStoppingStages
import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedChainTube
import PoincareConjecture.Proofs.M25.AppA_1_Necks.CoherentChainLimit
import PoincareConjecture.Proofs.M25.AppA_1_Necks.MiddleFrontier

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem ConnectedNeckCapCover.exists_outward_cappedTube_or_core_frontier :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      ∀ (C : CapCertificate g), C ∈ H.caps →
      (H.X ∩ C.carrier).Nonempty →
      (∃ K : CappedTubeCertificate g,
        K.cap = C ∧ K.tube.epsilon = H.epsilon ∧ H.X ⊆ K.carrier) ∨
      (∃ (b : ℤ) (D : BalancedNeckChain g C.epsilon),
        0 ≤ b ∧ D.shape = ChainShape.finite 0 b ∧
        D.source_necks = insert C.end_neck H.necks ∧ D.neck 0 = C.end_neck ∧
        (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) ∧
        (∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∈ H.X \ C.carrier) ∧
        (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          closure ((D.neck i).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) ⊆
              (D.neck (i + 1)).carrier ∧
            closure ((D.neck (i + 1)).region
                (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) ∧
        (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
          (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 C.epsilon⁻¹) ∧
            (D.neck (i + 1)).center ∉ (D.neck i).carrier) ∧
        ∃ C1 ∈ H.caps, ∃ y ∈ H.X,
          y ∈ C1.core ∧
          y ∉ C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
          y ∈ closure ((D.neck b).region 0 C.epsilon⁻¹)) := by
  classical
  obtain ⟨epsilonS, hS, hScap, hstages⟩ :=
    ConnectedNeckCapCover.exists_finite_capped_stopping_stages.{u}
  obtain ⟨epsilonT, hT, _, htube⟩ :=
    CapCertificate.exists_cappedTubeCertificate_of_outward_chain.{u}
  obtain ⟨epsilonF, hF, _, hfrontier⟩ :=
    BalancedNeckChain.exists_frontier_subset_exposed_end_closures.{u}
  refine ⟨min epsilonS (min epsilonT epsilonF), lt_min hS (lt_min hT hF),
    (min_le_left _ _).trans hScap, ?_⟩
  intro M _ _ _ _ _ _ g H he C hC hmeet
  have hCe : C.epsilon = H.epsilon := H.cap_epsilon C hC
  have heT : C.epsilon ≤ epsilonT := by
    rw [hCe]
    exact he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heF : C.epsilon ≤ epsilonF := by
    rw [hCe]
    exact he.trans ((min_le_right _ _).trans (min_le_right _ _))
  let U (D : BalancedNeckChain g C.epsilon) : Set M :=
    ⋃ i ∈ D.shape.active, (D.neck i).carrier
  let Stop (b : ℤ) (D : BalancedNeckChain g C.epsilon) : Prop :=
    H.X ⊆ C.carrier ∪ U D ∨
      ∃ C1 ∈ H.caps, ∃ y ∈ H.X,
        y ∈ C1.core ∧ y ∉ C.carrier ∪ U D ∧
          y ∈ closure ((D.neck b).region 0 C.epsilon⁻¹)
  have hcertificate (D : BalancedNeckChain g C.epsilon)
      (hzero : (0 : ℤ) ∈ D.shape.active)
      (hfirst : ∀ i ∈ D.shape.active, 0 ≤ i)
      (hstart : D.neck 0 = C.end_neck)
      (hsep : ∀ i ∈ D.shape.active, (D.neck i).IsSeparating)
      (hout : ∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C.carrier)
      (hcover : H.X ⊆ C.carrier ∪ U D) :
      ∃ K : CappedTubeCertificate g,
        K.cap = C ∧ K.tube.epsilon = H.epsilon ∧ H.X ⊆ K.carrier := by
    obtain ⟨K, hKcap, hKepsilon, _, _, hKcarrier⟩ :=
      htube C D heT hzero hfirst hstart hsep hout
    refine ⟨K, hKcap, hKepsilon.trans hCe, ?_⟩
    rw [hKcarrier]
    exact hcover
  obtain ⟨b, E, hb0, _, hshape, hsource, hbmono, hretain, hstart,
    hsep, hcenters, hquarters, hincidence, _, hgrow⟩ :=
    hstages H (he.trans (min_le_left _ _)) C hC hmeet
  have hbn0 (n : ℕ) : 0 ≤ b n := by
    have h := hbmono (Nat.zero_le n)
    rwa [hb0] at h
  by_cases hfinite : ∃ n, Stop (b n) (E n)
  · obtain ⟨n, hn⟩ := hfinite
    rcases hn with hcovered | hcore
    · have hzero : (0 : ℤ) ∈ (E n).shape.active := by
        rw [hshape n]
        exact ⟨le_rfl, hbn0 n⟩
      have hfirst : ∀ i ∈ (E n).shape.active, (0 : ℤ) ≤ i := by
        intro i hi
        rw [hshape n] at hi
        exact hi.1
      exact Or.inl (hcertificate (E n) hzero hfirst (hstart n) (hsep n)
        (fun i hi hi0 => (hcenters n i hi hi0).2) hcovered)
    · exact Or.inr ⟨b n, E n, hbn0 n, hshape n, hsource n, hstart n,
        hsep n, hcenters n, hquarters n, hincidence n, hcore⟩
  have hnot (n : ℕ) : ¬ Stop (b n) (E n) := fun hn => hfinite ⟨n, hn⟩
  have hbn (n : ℕ) : b n = (n : ℤ) := by
    induction n with
    | zero => exact hb0
    | succ n ih =>
      simpa only [Int.natCast_succ, ih] using hgrow n (hnot n)
  have hactive (n : ℕ) (i : ℤ) : i ∈ (E n).shape.active ↔ 0 ≤ i ∧ i ≤ b n := by
    rw [hshape n]
    rfl
  have hmono : Monotone (fun n => (E n).shape.active) := by
    intro n m hnm i hi
    have hii := (hactive n i).mp hi
    exact (hactive m i).mpr ⟨hii.1, hii.2.trans (hbmono hnm)⟩
  obtain ⟨D, hDactive, _, hDneck⟩ :=
    BalancedNeckChain.exists_coherent_finite_limit E (fun _ => 0) b hshape
      (fun n => hmono (Nat.le_succ n)) hretain
      (fun n => (hsource n).trans (hsource 0).symm)
  have hDactiveIci : D.shape.active = Ici (0 : ℤ) := by
    rw [hDactive]
    ext i
    constructor
    · intro hi
      obtain ⟨n, hn⟩ := mem_iUnion.mp hi
      exact ((hactive n i).mp hn).1
    · intro hi
      refine mem_iUnion.mpr ⟨i.toNat, (hactive i.toNat i).mpr ⟨hi, ?_⟩⟩
      rw [hbn, Int.toNat_of_nonneg (show 0 ≤ i from hi)]
  have hDmem (i : ℤ) : i ∈ D.shape.active ↔ 0 ≤ i := by
    rw [hDactiveIci]
    rfl
  have hDforward : D.shape = ChainShape.forward 0 := by
    cases hs : D.shape with
    | finite a c =>
      have hzero : a ≤ 0 ∧ 0 ≤ c := by
        simpa only [hs, ChainShape.active, mem_Icc] using (hDmem 0).mpr le_rfl
      have hnonneg : 0 ≤ c + 1 := by omega
      have hnext : a ≤ c + 1 ∧ c + 1 ≤ c := by
        simpa only [hs, ChainShape.active, mem_Icc] using (hDmem (c + 1)).mpr hnonneg
      omega
    | forward a =>
      have hle : a ≤ 0 := by
        simpa only [hs, ChainShape.active, mem_Ici] using (hDmem 0).mpr le_rfl
      have ha : a ∈ D.shape.active := by
        rw [hs]
        change a ≤ a
        exact le_rfl
      have hge : 0 ≤ a := (hDmem a).mp ha
      have ha0 : a = 0 := le_antisymm hle hge
      rw [ha0]
    | backward c =>
      have hneg : min c (-1) ∈ D.shape.active := by
        rw [hs]
        change min c (-1) ≤ c
        exact min_le_left _ _
      have hnonneg : 0 ≤ min c (-1) := (hDmem _).mp hneg
      have hle : min c (-1) ≤ -1 := min_le_right _ _
      omega
    | biInfinite =>
      have hneg : (-1 : ℤ) ∈ D.shape.active := by
        rw [hs]
        exact mem_univ _
      have hnonneg : (0 : ℤ) ≤ -1 := (hDmem _).mp hneg
      omega
  have hstage {i : ℤ} (hi : i ∈ D.shape.active) : ∃ n, i ∈ (E n).shape.active := by
    rw [hDactive] at hi
    exact mem_iUnion.mp hi
  have hcommon {i j : ℤ} (hi : i ∈ D.shape.active) (hj : j ∈ D.shape.active) :
      ∃ n, i ∈ (E n).shape.active ∧ j ∈ (E n).shape.active := by
    obtain ⟨n, hn⟩ := hstage hi
    obtain ⟨m, hm⟩ := hstage hj
    exact ⟨max n m, hmono (Nat.le_max_left _ _) hn,
      hmono (Nat.le_max_right _ _) hm⟩
  have hzeroStage : (0 : ℤ) ∈ (E 0).shape.active :=
    (hactive 0 0).mpr ⟨le_rfl, hbn0 0⟩
  have hDstart : D.neck 0 = C.end_neck :=
    (hDneck 0 0 hzeroStage).trans (hstart 0)
  have hDsep : ∀ i ∈ D.shape.active, (D.neck i).IsSeparating := by
    intro i hi
    obtain ⟨n, hn⟩ := hstage hi
    rw [hDneck n i hn]
    exact hsep n i hn
  have hDcenters : ∀ i ∈ D.shape.active, 0 < i →
      (D.neck i).center ∈ H.X \ C.carrier := by
    intro i hi hi0
    obtain ⟨n, hn⟩ := hstage hi
    rw [hDneck n i hn]
    exact hcenters n i hn hi0
  have hDincidence : ∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
      (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 C.epsilon⁻¹) ∧
        (D.neck (i + 1)).center ∉ (D.neck i).carrier := by
    intro i hi hi1
    obtain ⟨n, hni, hni1⟩ := hcommon hi hi1
    rw [hDneck n i hni, hDneck n (i + 1) hni1]
    exact hincidence n i hni hni1
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let V : Set M := C.carrier ∪ U D
  have hfrontU : frontier (U D) ⊆ closure (C.end_neck.region (-C.epsilon⁻¹) 0) := by
    have h := hfrontier D heF (fun i hi hi1 => Or.inl (hDincidence i hi hi1))
    change frontier (⋃ i ∈ D.shape.active, (D.neck i).carrier) ⊆ _
    simpa only [hDforward, hDstart] using h
  have hNU : C.end_neck.carrier ⊆ U D := by
    intro x hx
    refine mem_iUnion₂.mpr ⟨0, (hDmem 0).mpr le_rfl, ?_⟩
    simpa only [hDstart] using hx
  have hL : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hzero : (0 : ℝ) ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr hL, hL⟩
  let K := C.carrier \ C.end_neck.region 0 C.epsilon⁻¹
  have hKclosed : IsClosed K := (C.isCompact_end_neck_lower_cut hzero).isClosed
  have hnegK : C.end_neck.region (-C.epsilon⁻¹) 0 ⊆ K := by
    intro x hx
    refine ⟨C.end_neck_subset hx.1, ?_⟩
    intro hxpos
    exact lt_asymm hx.2.2 hxpos.2.1
  have hneg : closure (C.end_neck.region (-C.epsilon⁻¹) 0) ⊆ C.carrier :=
    (closure_minimal hnegK hKclosed).trans (show K ⊆ C.carrier from sdiff_subset)
  have hcapfront : frontier C.carrier ⊆
      closure (C.end_neck.region 0 C.epsilon⁻¹) :=
    (C.end_neck_lower_cut_topology hzero).2.2.2.2.2.2
  have hpositiveU : C.end_neck.region 0 C.epsilon⁻¹ ⊆ U D :=
    fun _ hx => hNU hx.1
  have hopenU : IsOpen (U D) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open
  have hopenV : IsOpen V := C.carrier_open.union hopenU
  have hnoFront (x : M) : x ∉ frontier V := by
    intro hx
    rw [hopenV.frontier_eq] at hx
    have hxC : x ∉ C.carrier := fun hxC => hx.2 (Or.inl hxC)
    have hxU : x ∉ U D := fun hxU => hx.2 (Or.inr hxU)
    have hxclosureU : x ∈ closure (U D) := by
      have hxparts : x ∈ closure C.carrier ∪ closure (U D) := by
        simpa only [V, closure_union] using hx.1
      rcases hxparts with hxcap | hxchain
      · have hxcapfront : x ∈ frontier C.carrier := by
          rw [C.carrier_open.frontier_eq]
          exact ⟨hxcap, hxC⟩
        exact closure_mono hpositiveU (hcapfront hxcapfront)
      · exact hxchain
    have hxfrontU : x ∈ frontier (U D) := by
      rw [hopenU.frontier_eq]
      exact ⟨hxclosureU, hxU⟩
    exact hxC (hneg (hfrontU hxfrontU))
  have hclosedV : IsClosed V :=
    frontier_subset_iff_isClosed.mp (fun x hx => (hnoFront x hx).elim)
  have hmeetV : (H.X ∩ V).Nonempty := by
    obtain ⟨x, hxX, hxC⟩ := hmeet
    exact ⟨x, hxX, Or.inl hxC⟩
  have hXV : H.X ⊆ V := by
    apply H.connected_X.isPreconnected.subset_of_closure_inter_subset hopenV hmeetV
    rw [hclosedV.closure_eq]
    exact inter_subset_left
  exact Or.inl (hcertificate D ((hDmem 0).mpr le_rfl)
    (fun i hi => (hDmem i).mp hi) hDstart hDsep
    (fun i hi hi0 => (hDcenters i hi hi0).2) hXV)

end PoincareConjecture
