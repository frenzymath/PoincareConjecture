import PoincareConjecture.Proofs.M25.AppA_21_Local.ShiftedClosingStripBoundary
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.InitialGraphCut
import PoincareConjecture.Proofs.M25.Mathlib.CompactGraphStrip
import Mathlib.Topology.Order.Compact









set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture



theorem BalancedNeckChain.exists_shifted_closing_three_piece_decomposition :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := epsilon⁻¹
        let N := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∀ (c : ℝ), c ∈ Set.Ioo (-L / 20) (3 * L / 20) →
        ∀ (R Rh Q : EpsilonNeck g), R.epsilon = epsilon →
          (Rh = R ∨ Rh = R.reverse) → Q.epsilon = epsilon →
          R.center ∈ closure (B.region 0 L) → R.center ∉ U →
          ∀ (f hN hR : UnitTwoSphere → ℝ),
            Continuous f → Continuous hN → Continuous hR →
            (∀ q, -(3 * L / 10) < f q ∧ f q < -(L / 5)) →
            (∀ q, -(9 * L / 10) < hN q ∧ hN q < -(4 * L / 5)) →
            (∀ q, -(L / 5) < hR q ∧ hR q < 19 * L / 20) →
            Set.range (fun q : UnitTwoSphere =>
              B.coordinate_map (q, 3 * L / 4)) =
              Set.range (fun q : UnitTwoSphere =>
                Rh.coordinate_map (q, f q)) →
            Set.range (fun q : UnitTwoSphere =>
              N.coordinate_map (q, hN q)) =
              Set.range (fun q : UnitTwoSphere => Q.coordinate_map (q, c)) →
            Set.range (fun q : UnitTwoSphere =>
              Rh.coordinate_map (q, hR q)) =
              Set.range (fun q : UnitTwoSphere => Q.coordinate_map (q, c - L / 4)) →
            (∀ (q : UnitTwoSphere) (s : ℝ),
              s ∈ Set.Icc (c - L / 40) (c + L / 40) →
              Q.coordinate_map (q, s) ∈ N.carrier ∧
              (N.coordinate_inverse (Q.coordinate_map (q, s))).2 ∈
                Set.Ioo (-(9 * L / 10)) (-(4 * L / 5)) ∧
              0 < N.scale * mvfderiv (𝓡 3)
                (fun x => (N.coordinate_inverse x).2) (Q.coordinate_map (q, s))
                (Q.normalizedAxialVector (Q.coordinate_map (q, s)))) →
            (∀ (q : UnitTwoSphere) (s : ℝ),
              s ∈ Set.Icc (c - 13 * L / 50) (c - 6 * L / 25) →
              Q.coordinate_map (q, s) ∈ Rh.carrier ∧
              (Rh.coordinate_inverse (Q.coordinate_map (q, s))).2 ∈
                Set.Ioo (-(L / 5)) (19 * L / 20) ∧
              0 < Rh.scale * mvfderiv (𝓡 3)
                (fun x => (Rh.coordinate_inverse x).2) (Q.coordinate_map (q, s))
                (Q.normalizedAxialVector (Q.coordinate_map (q, s)))) →
            let Sm : Set M := Set.range (fun q => N.coordinate_map (q, hN q))
            let Sp : Set M := Set.range (fun q : UnitTwoSphere =>
              B.coordinate_map (q, 3 * L / 4))
            let S2 : Set M := Set.range (fun q : UnitTwoSphere =>
              Q.coordinate_map (q, c - L / 4))
            let Gminus : Set M := N.coordinate_map ''
              {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < hN z.1}
            let Pplus : Set M := connectedComponentIn (U \ Sp)
              (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
            let K : Set M := U \ (Gminus ∪ Pplus)
            let DR : Set M := Rh.coordinate_map ''
              {z : RoundCylinderSpace | f z.1 < z.2 ∧ z.2 < hR z.1}
            let DQ : Set M := Q.region (c - L / 4) c
            let W : Set M := (U ∪ R.carrier) ∪ Q.carrier
            IsCompact K ∧ frontier K = Sm ∪ Sp ∧
            IsOpen DR ∧ IsConnected DR ∧ IsOpen DQ ∧ IsConnected DQ ∧
            closure DR = Rh.coordinate_map ''
              {z : RoundCylinderSpace | f z.1 ≤ z.2 ∧ z.2 ≤ hR z.1} ∧
            closure DQ = Q.coordinate_map '' (Set.univ ×ˢ Set.Icc (c - L / 4) c) ∧
            IsCompact (closure DR) ∧ IsCompact (closure DQ) ∧
            frontier DR = Sp ∪ S2 ∧ frontier DQ = S2 ∪ Sm ∧
            K ∩ closure DR = Sp ∧ K ∩ closure DQ = Sm ∧
            closure DR ∩ closure DQ = S2 ∧
            (K ∪ closure DR) ∪ closure DQ = W ∧
            (Rh.coordinate_map ''
              {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < f z.1}) ⊆ interior K ∧
            Q.region c (c + L / 40) ⊆ interior K ∧
            Q.region (c - 13 * L / 50) (c - L / 4) ⊆ DR := by
  obtain ⟨eA, hAp, hAcap, avoid⟩ :=
    BalancedNeckChain.exists_shifted_closing_strip_boundary_avoidance.{u}
  obtain ⟨eK, hKp, _, cut⟩ :=
    BalancedNeckChain.exists_compact_cut_between_initial_graph_and_last_slice.{u}
  obtain ⟨eJ, hJp, _, initial⟩ :=
    BalancedNeckChain.exists_oriented_frontier_initial_height_control.{u}
  obtain ⟨eW, hWp, _, runLine⟩ := EpsilonNeck.exists_signed_axial_line_control.{u}
  obtain ⟨eO, hOp, _, orient⟩ :=
    EpsilonNeck.exists_intersecting_coherent_orientation.{u}
      (η := (1 / 1000 : ℝ)) (by constructor <;> norm_num)
  refine ⟨min eA (min eK (min eJ (min eW eO))), by positivity,
    (min_le_left _ _).trans hAcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C heps a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  rcases le_min_iff.mp heps with ⟨heA, heps⟩
  rcases le_min_iff.mp heps with ⟨heK, heps⟩
  rcases le_min_iff.mp heps with ⟨heJ, heps⟩
  rcases le_min_iff.mp heps with ⟨heW, heO⟩
  let L : ℝ := epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  dsimp only
  intro c hshift R Rh Q heR hRh heQ hy hout f hN hR hf hhN hhR bf bN bR gSp gSm gS2 bandN bandR
  let Sm : Set M := range (fun q => N.coordinate_map (q, hN q))
  let Sp : Set M := range (fun q : UnitTwoSphere => B.coordinate_map (q, 3 * L / 4))
  let S2 : Set M := range (fun q : UnitTwoSphere => Q.coordinate_map (q, c - L / 4))
  let Gminus : Set M := N.coordinate_map '' {z | -L < z.2 ∧ z.2 < hN z.1}
  let Pplus : Set M := connectedComponentIn (U \ Sp)
    (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
  let K : Set M := U \ (Gminus ∪ Pplus)
  let DR : Set M := Rh.coordinate_map '' {z | f z.1 < z.2 ∧ z.2 < hR z.1}
  let DQ : Set M := Q.region (c - L / 4) c
  let W : Set M := (U ∪ R.carrier) ∪ Q.carrier
  let height (A : EpsilonNeck g) (x : M) := (A.coordinate_inverse x).2
  let cross (A D : EpsilonNeck g) (x : M) := D.scale * mvfderiv (𝓡 3)
    (fun y => (D.coordinate_inverse y).2) x (A.normalizedAxialVector x)
  let F : M → ℝ := fun x => if x ∈ N.carrier then height N x else L
  change IsCompact K ∧ frontier K = Sm ∪ Sp ∧ _
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb := (hactive b).mpr ⟨hab, le_rfl⟩
  have heN : N.epsilon = epsilon := C.epsilon_eq a ha
  have heB : B.epsilon = epsilon := C.epsilon_eq b hb
  have hRhfields : Rh.epsilon = epsilon ∧ Rh.center = R.center ∧ Rh.carrier = R.carrier := by
    rcases hRh with rfl | rfl <;> exact ⟨heR, rfl, rfl⟩
  rcases hRhfields with ⟨heRh, hRhcenter, hRhcarrier⟩
  have hL : 0 < L := inv_pos.mpr (heR ▸ R.epsilon_pos)
  have hcut : c ∈ Ioo (-L) L := by
    constructor <;> linarith only [hL, hshift.1, hshift.2]
  have hquarter : c - L / 4 ∈ Ioo (-L) L := by
    constructor <;> linarith only [hL, hshift.1, hshift.2]
  have dom (A : EpsilonNeck g) (he : A.epsilon = epsilon)
      {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-L) L) : z ∈ A.cylinderDomain :=
    ⟨mem_univ _, by simpa only [he] using hz⟩
  have coord (A : EpsilonNeck g) (he : A.epsilon = epsilon) {x : M}
      (hx : x ∈ A.carrier) : height A x ∈ Ioo (-L) L := by
    simpa only [he] using (A.coordinate_inverse_mem x hx).2
  have point (A : EpsilonNeck g) (he : A.epsilon = epsilon)
      (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-L) L) :
      A.coordinate_map (q, s) ∈ A.carrier ∧ height A (A.coordinate_map (q, s)) = s :=
    ⟨A.coordinate_map_mem (dom A he hs),
      congrArg Prod.snd (A.coordinate_inverse_coordinate_map (dom A he hs))⟩
  have hNU : N.carrier ⊆ U := fun _ hx => mem_iUnion₂.mpr ⟨a, ha, hx⟩
  have hBU : B.carrier ⊆ U := fun _ hx => mem_iUnion₂.mpr ⟨b, hb, hx⟩
  have bfg (q : UnitTwoSphere) : f q < hR q := (bf q).2.trans (bR q).1
  have domf (q : UnitTwoSphere) : f q ∈ Ioo (-L) L := by
    constructor <;> linarith only [hL, (bf q).1, (bf q).2]
  have domN (q : UnitTwoSphere) : hN q ∈ Ioo (-L) L := by
    constructor <;> linarith only [hL, (bN q).1, (bN q).2]
  have domR (q : UnitTwoSphere) : hR q ∈ Ioo (-L) L := by
    constructor <;> linarith only [hL, (bR q).1, (bR q).2]
  have graphMem (A : EpsilonNeck g) (he : A.epsilon = epsilon)
      (h : UnitTwoSphere → ℝ) (hd : ∀ q, h q ∈ Ioo (-L) L) (x : M) :
      x ∈ range (fun q => A.coordinate_map (q, h q)) ↔
        x ∈ A.carrier ∧ height A x = h (A.coordinate_inverse x).1 := by
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨(point A he q (hd q)).1, ?_⟩
      dsimp only [height]
      rw [A.coordinate_inverse_coordinate_map (dom A he (hd q))]
    · rintro ⟨hx, hs⟩
      refine ⟨(A.coordinate_inverse x).1, ?_⟩
      change A.coordinate_map ((A.coordinate_inverse x).1,
        h (A.coordinate_inverse x).1) = x
      dsimp only [height] at hs
      rw [← hs]
      exact A.coordinate_map_inverse hx
  have regionImage (A : EpsilonNeck g) (he : A.epsilon = epsilon)
      {c d : ℝ} (hc : -L ≤ c) (hd : d ≤ L) :
      A.region c d = A.coordinate_map '' {z : RoundCylinderSpace | c < z.2 ∧ z.2 < d} := by
    ext x
    constructor
    · rintro ⟨hx, hs⟩
      exact ⟨A.coordinate_inverse x, hs, A.coordinate_map_inverse hx⟩
    · rintro ⟨z, hz, rfl⟩
      have hstrip : z.2 ∈ Ioo (-L) L :=
        ⟨hc.trans_lt hz.1, hz.2.trans_le hd⟩
      have hp := point A he z.1 hstrip
      refine ⟨hp.1, ?_⟩
      change c < z.2 ∧ z.2 < d at hz
      simpa only [A.coordinate_inverse_coordinate_map (dom A he hstrip)] using hz
  have stripOC (A : EpsilonNeck g) (l r : UnitTwoSphere → ℝ)
      (hl : Continuous l) (hr : Continuous r) (hlt : ∀ q, l q < r q)
      (hdom : {z : RoundCylinderSpace | l z.1 < z.2 ∧ z.2 < r z.1} ⊆ A.cylinderDomain) :
      IsOpen (A.coordinate_map '' {z | l z.1 < z.2 ∧ z.2 < r z.1}) ∧
      IsConnected (A.coordinate_map '' {z | l z.1 < z.2 ∧ z.2 < r z.1}) :=
    ⟨A.coordinatePartialHomeomorph.isOpen_image_of_subset_source
      ((isOpen_lt (hl.comp continuous_fst) continuous_snd).inter
        (isOpen_lt continuous_snd (hr.comp continuous_fst))) hdom,
      (isConnected_between_continuous_graphs hl hr hlt).image A.coordinate_map
        (A.coordinate_map_smooth.continuousOn.mono hdom)⟩
  have regionConn (A : EpsilonNeck g) (he : A.epsilon = epsilon)
      {c d : ℝ} (hc : -L ≤ c) (hd : d ≤ L) (hcd : c < d) : IsConnected (A.region c d) := by
    rw [regionImage A he hc hd]
    exact (stripOC A (fun _ => c) (fun _ => d) continuous_const continuous_const
      (fun _ => hcd) (fun _ hz => dom A he ⟨hc.trans_lt hz.1, hz.2.trans_le hd⟩)).2
  obtain ⟨hUopen, _, _, _, _, _, hKcompact, hKU, hKregular, hKint,
      hKfront, hSmSp, hKN, hKiN, hKB, hKiB⟩ := cut C hshape heK hN hhN bN
  change IsCompact K at hKcompact
  change closure (interior K) = K at hKregular
  change interior K = K \ (Sm ∪ Sp) at hKint
  change frontier K = Sm ∪ Sp at hKfront
  have hKclosed := hKcompact.isClosed
  have hSmK : Sm ⊆ K := fun _ hx =>
    hKclosed.closure_eq ▸ frontier_subset_closure (hKfront.symm ▸ Or.inl hx)
  have hSpK : Sp ⊆ K := fun _ hx =>
    hKclosed.closure_eq ▸ frontier_subset_closure (hKfront.symm ▸ Or.inr hx)
  have hJ := initial C heJ a b hshape Rh heRh
    (by rw [hRhcenter]; exact hy) (by rw [hRhcenter]; exact hout) f bf gSp
  change (∀ q, 7 * L / 10 < F (B.coordinate_map (q, 3 * L / 4))) ∧ _ at hJ
  have hSpF (x : M) (hx : x ∈ Sp) : 7 * L / 10 < F x := by
    obtain ⟨q, rfl⟩ := hx
    exact hJ.1 q
  have hFSm (x : M) (hx : x ∈ Sm) : F x < -(4 * L / 5) := by
    obtain ⟨hxN, hs⟩ := (graphMem N heN hN domN x).mp hx
    simpa only [F, if_pos hxN, hs] using (bN (N.coordinate_inverse x).1).2
  have hAvoid := avoid C heA a b hshape c hshift Rh Q heRh heQ
    (by rw [hRhcenter]; exact hy) (by rw [hRhcenter]; exact hout) f hN hR bf bN bR gSp gSm gS2
    (fun q => (bandN q c (by constructor <;> linarith only [hL])).2.2)
    (fun q => (bandR q (c - L / 4) (by constructor <;> linarith only [hL])).2.2)
  have hDRfacts := Rh.coordinatePartialHomeomorph.compact_graph_strip f hR hf hhR bfg
    (c := -(3 * L / 10)) (d := 19 * L / 20)
    (fun q => ⟨(bf q).1.le, (bR q).2.le⟩)
    (fun z hz => dom Rh heRh ⟨(domf z.1).1.trans_le hz.1, hz.2.trans_lt (domR z.1).2⟩)
  change IsOpen DR ∧ IsConnected DR ∧ closure DR = _ ∧ IsCompact (closure DR) ∧ _ at hDRfacts
  rcases hDRfacts with ⟨hDRopen, hDRconn, hDRcl, hDRcompact, hDRfront⟩
  change frontier DR =
    range (fun q => Rh.coordinate_map (q, f q)) ∪
      range (fun q => Rh.coordinate_map (q, hR q)) at hDRfront
  rw [← gSp, gS2] at hDRfront
  have hDQimage := regionImage Q heQ (c := c - L / 4) (d := c)
    hquarter.1.le hcut.2.le
  have hDQfacts := Q.coordinatePartialHomeomorph.compact_graph_strip
    (fun _ => c - L / 4) (fun _ => c) continuous_const continuous_const
    (fun _ => by linarith only [hL])
    (c := c - L / 4) (d := c) (fun _ => ⟨le_rfl, le_rfl⟩)
    (fun z hz => dom Q heQ ⟨hquarter.1.trans_le hz.1, hz.2.trans_lt hcut.2⟩)
  change
    IsOpen (Q.coordinate_map '' {z : RoundCylinderSpace | c - L / 4 < z.2 ∧ z.2 < c}) ∧
      IsConnected (Q.coordinate_map '' {z : RoundCylinderSpace | c - L / 4 < z.2 ∧ z.2 < c}) ∧
        closure (Q.coordinate_map '' {z : RoundCylinderSpace |
          c - L / 4 < z.2 ∧ z.2 < c}) =
            Q.coordinate_map '' {z : RoundCylinderSpace | c - L / 4 ≤ z.2 ∧ z.2 ≤ c} ∧
          IsCompact (closure (Q.coordinate_map '' {z : RoundCylinderSpace |
            c - L / 4 < z.2 ∧ z.2 < c})) ∧
            frontier (Q.coordinate_map '' {z : RoundCylinderSpace |
              c - L / 4 < z.2 ∧ z.2 < c}) =
              range (fun q => Q.coordinate_map (q, c - L / 4)) ∪
                range (fun q => Q.coordinate_map (q, c)) at hDQfacts
  rw [← hDQimage] at hDQfacts
  rcases hDQfacts with ⟨hDQopen, hDQconn, hDQcl0, hDQcompact, hDQfront⟩
  have hDQslab : {z : RoundCylinderSpace | c - L / 4 ≤ z.2 ∧ z.2 ≤ c} =
      (univ : Set UnitTwoSphere) ×ˢ Icc (c - L / 4) c := by
    ext z
    simp
  rw [hDQslab] at hDQcl0
  have hDQcl : closure DQ = Q.coordinate_map '' (univ ×ˢ Icc (c - L / 4) c) := by
    exact hDQcl0
  change frontier DQ = S2 ∪ _ at hDQfront
  rw [← gSm] at hDQfront
  have spRh (x : M) : x ∈ Sp ↔
      x ∈ Rh.carrier ∧ height Rh x = f (Rh.coordinate_inverse x).1 := by
    change x ∈ range (fun q => B.coordinate_map (q, 3 * L / 4)) ↔ _
    rw [gSp]; exact graphMem Rh heRh f domf x
  have smQ (x : M) : x ∈ Sm ↔ x ∈ Q.carrier ∧ height Q x = c := by
    change x ∈ range (fun q => N.coordinate_map (q, hN q)) ↔ _
    rw [gSm]
    exact graphMem Q heQ (fun _ => c) (fun _ => hcut) x
  have s2Q (x : M) : x ∈ S2 ↔ x ∈ Q.carrier ∧ height Q x = c - L / 4 :=
    graphMem Q heQ (fun _ => c - L / 4) (fun _ => hquarter) x
  have small (A : EpsilonNeck g) (he : A.epsilon = epsilon) {e : ℝ}
      (h : epsilon ≤ e) : A.epsilon ≤ e := by rw [he]; exact h
  let line (A D : EpsilonNeck g) (heA : A.epsilon = epsilon)
      (heD : D.epsilon = epsilon) := runLine A D (small A heA heW) (heD.trans heA.symm)
  have pointSign (A D : EpsilonNeck g) (heA : A.epsilon = epsilon)
      (heD : D.epsilon = epsilon) (x : M) (hxA : x ∈ A.carrier) (hxD : x ∈ D.carrier) :
      ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧ 0 < sigma * cross A D x := by
    obtain ⟨sigma, hsigma, hc⟩ := orient A D (small A heA heO) (small D heD heO)
      {A.coordinate_inverse x} isPreconnected_singleton (by
        intro z hz; rw [mem_singleton_iff.mp hz]
        refine ⟨A.coordinate_inverse_mem x hxA, ?_⟩
        change A.coordinate_map (A.coordinate_inverse x) ∈ D.carrier
        rw [A.coordinate_map_inverse hxA]; exact hxD)
    have h := hc (A.coordinate_inverse x) (mem_singleton _)
    rw [A.coordinate_map_inverse hxA] at h
    have hh : |1 - sigma * cross A D x| < (1 / 1000 : ℝ) := by
      simpa only [cross, mul_assoc] using h
    exact ⟨sigma, hsigma, by linarith only [(abs_lt.mp hh).2]⟩

  have step (A D : EpsilonNeck g) (heA : A.epsilon = epsilon)
      (heD : D.epsilon = epsilon) (q : UnitTwoSphere) (s t : ℝ)
      (hs : s ∈ Ioo (-L) L) (ht : t ∈ Ioo (-L) L)
      (hx : A.coordinate_map (q, s) ∈ D.carrier)
      (hp : 0 < cross A D (A.coordinate_map (q, s)))
      (hv : height D (A.coordinate_map (q, s)) ∈ Ioo (-(9 * L / 10)) (19 * L / 20))
      (hlen : |t - s| ≤ L / 100) :
      A.coordinate_map (q, t) ∈ D.carrier ∧
        |height D (A.coordinate_map (q, t)) - height D (A.coordinate_map (q, s)) -
          (t - s)| ≤ (1 / 100 : ℝ) * |t - s| := by
    have h := line A D heA heD q s t 1 (-(23 * L / 25)) (97 * L / 100)
      (by simpa only [heA] using hs) (by simpa only [heA] using ht) (Or.inl rfl) hx
      (by simpa only [one_mul] using hp)
      (by rw [heD]; change -L < _; linarith only [hL])
      (by rw [heD]; change _ < L; linarith only [hL]) (by
        intro u hu
        have habs := (abs_sub_left_of_mem_uIcc hu).trans hlen
        change -(23 * L / 25) ≤ height D (A.coordinate_map (q, s)) +
            1 * (u - s) - (1 / 100 : ℝ) * |u - s| ∧
          height D (A.coordinate_map (q, s)) + 1 * (u - s) +
            (1 / 100 : ℝ) * |u - s| ≤ 97 * L / 100
        rw [one_mul]
        constructor <;> linarith only [hv.1, hv.2, habs,
          le_abs_self (u - s), neg_abs_le (u - s), hL])
    exact ⟨(h t right_mem_uIcc).1, by simpa only [one_mul] using
      (h t right_mem_uIcc).2.2.1⟩
  have stay {A D : Set M} (hA : IsPreconnected A) (hD : IsOpen D)
      (havoid : ∀ x ∈ A, x ∉ frontier D) (hmeet : (A ∩ D).Nonempty) : A ⊆ D := by
    apply hA.subset_of_closure_inter_subset hD hmeet
    rintro x ⟨hx, hAx⟩
    by_contra hn
    exact havoid x hAx (by rw [hD.frontier_eq]; exact ⟨hx, hn⟩)
  have offOpen {D : Set M} (hD : IsOpen D) {x : M} (hx : x ∈ D) :
      x ∉ frontier D := fun hf => (hD.frontier_eq ▸ hf).2 hx
  have drOff (x : M) (hx : x ∈ DR) : x ∉ Sm ∧ x ∉ Sp ∧ x ∉ S2 :=
    ⟨fun hm => disjoint_left.mp hAvoid.1 hx hm,
      fun hp => offOpen hDRopen hx (hDRfront.symm ▸ Or.inl hp),
      fun h2 => offOpen hDRopen hx (hDRfront.symm ▸ Or.inr h2)⟩
  have dqOff (x : M) (hx : x ∈ closure DQ) : x ∉ Sp := by
    rw [hDQcl] at hx
    exact fun hp => disjoint_left.mp hAvoid.2 hx hp
  have drBoundary (x : M) (hx : x ∈ DR) : x ∉ frontier K := by
    rw [hKfront]; exact fun h => h.elim (drOff x hx).1 (drOff x hx).2.1
  have dqBoundary (x : M) (hx : x ∈ DQ) : x ∉ frontier K := by
    rw [hKfront]
    exact fun h => h.elim
      (fun hm => offOpen hDQopen hx (hDQfront.symm ▸ Or.inr hm))
      (dqOff x (subset_closure hx))
  let qc := (Rh.coordinate_inverse Rh.center).1
  let v := f qc
  have hvdom : v ∈ Ioo (-L) L := domf qc
  have hxSp : Rh.coordinate_map (qc, v) ∈ Sp := by
    change Rh.coordinate_map (qc, f qc) ∈ range (fun q => B.coordinate_map (q, 3 * L / 4))
    rw [gSp]; exact mem_range_self qc
  have hxB : Rh.coordinate_map (qc, v) ∈ B.carrier ∧
      height B (Rh.coordinate_map (qc, v)) = 3 * L / 4 :=
    (graphMem B heB (fun _ => 3 * L / 4)
      (fun _ => by constructor <;> linarith only [hL]) _).mp hxSp
  have hpositive : 0 < cross Rh B (Rh.coordinate_map (qc, v)) := by
    obtain ⟨sigma, hsigma, hp⟩ := pointSign Rh B heRh heB _
      (point Rh heRh qc hvdom).1 hxB.1
    rcases hsigma with rfl | rfl
    · simpa only [one_mul] using hp
    · have h := line Rh B heRh heB qc v 0 (-1) (2 * L / 5) (4 * L / 5)
        (by simpa only [heRh] using hvdom)
        (by rw [heRh]; constructor <;> linarith only [hL])
        (Or.inr rfl) hxB.1 hp
        (by rw [heB]; change -L < _; linarith only [hL])
        (by rw [heB]; change _ < L; linarith only [hL]) (by
          intro t ht
          rw [uIcc_of_le (show v ≤ 0 by linarith only [(bf qc).2, hL])] at ht
          change 2 * L / 5 ≤ height B (Rh.coordinate_map (qc, v)) +
              (-1) * (t - v) - (1 / 100 : ℝ) * |t - v| ∧
            height B (Rh.coordinate_map (qc, v)) + (-1) * (t - v) +
              (1 / 100 : ℝ) * |t - v| ≤ 4 * L / 5
          rw [hxB.2, abs_of_nonneg (sub_nonneg.mpr ht.1)]
          dsimp only [v] at ht ⊢
          constructor <;> linarith only [hL, (bf qc).1, ht.1, ht.2])
      have hc := (Rh.mem_central_sphere_iff Rh.center).mp Rh.center_on_central_sphere
      have hz : Rh.coordinate_map (qc, 0) = Rh.center := by
        change Rh.coordinate_map ((Rh.coordinate_inverse Rh.center).1, 0) = Rh.center
        rw [← hc.2]; exact Rh.coordinate_map_inverse hc.1
      have hcU := hBU (h 0 right_mem_uIcc).1
      rw [hz, hRhcenter] at hcU
      exact (hout hcU).elim
  have anchor (t : ℝ) (ht : t ∈ Ioo (-L) L) (hlen : |t - v| ≤ L / 100) :=
    step Rh B heRh heB qc v t hvdom ht hxB.1 hpositive
      (by rw [hxB.2]; constructor <;> linarith only [hL]) hlen
  have hlow := anchor (v - L / 100)
    (by dsimp only [v]; constructor <;> linarith only [hL, (bf qc).1, (bf qc).2])
    (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity : 0 < L / 100)])
  have hlowErr := hlow.2
  rw [hxB.2, sub_sub_cancel_left, abs_neg,
    abs_of_pos (by positivity : 0 < L / 100)] at hlowErr
  have hlowBand : height B (Rh.coordinate_map (qc, v - L / 100)) ∈
      Ioo (5 * L / 8) (3 * L / 4) := by
    constructor <;> linarith only [hL, (abs_le.mp hlowErr).1, (abs_le.mp hlowErr).2]
  have hlowK : Rh.coordinate_map (qc, v - L / 100) ∈ interior K := by
    have hm : Rh.coordinate_map (qc, v - L / 100) ∈ B.region (5 * L / 8) (3 * L / 4) :=
      ⟨hlow.1, hlowBand⟩
    exact (hKiB.symm ▸ hm).1
  let delta := min (L / 100) ((hR qc - v) / 2)
  have hdpos : 0 < delta := lt_min (by positivity)
    (by dsimp only [v]; linarith only [bfg qc])
  have hdle : delta ≤ L / 100 := min_le_left _ _
  have hdh : delta ≤ (hR qc - v) / 2 := min_le_right _ _
  have hhigh := anchor (v + delta)
    (by constructor <;> linarith only [hvdom.1, hdpos, hdh, (domR qc).2])
    (by rw [add_sub_cancel_left, abs_of_pos hdpos]; exact hdle)
  have hhighErr := hhigh.2
  rw [hxB.2, add_sub_cancel_left, abs_of_pos hdpos] at hhighErr
  have hhighBand : height B (Rh.coordinate_map (qc, v + delta)) ∈ Ioo (3 * L / 4) L := by
    constructor <;> linarith only [hL, hdpos, hdle,
      (abs_le.mp hhighErr).1, (abs_le.mp hhighErr).2]
  have hhighDR : Rh.coordinate_map (qc, v + delta) ∈ DR := by
    refine ⟨(qc, v + delta), ?_, rfl⟩
    change f qc < v + delta ∧ v + delta < hR qc
    dsimp only [v] at hdpos hdh ⊢; constructor <;> linarith only [hdpos, hdh, bfg qc]
  have hhighOut : Rh.coordinate_map (qc, v + delta) ∉ K := by
    intro hk
    have hm : Rh.coordinate_map (qc, v + delta) ∈ K ∩ B.region (5 * L / 8) L :=
      ⟨hk, hhigh.1, by constructor <;> linarith only [hL, hhighBand.1, hhighBand.2]⟩
    rw [hKB] at hm
    obtain ⟨⟨q, s⟩, ⟨_, hslo, hshi⟩, heq⟩ := hm
    have hv := (point B heB q
      ⟨by nlinarith [hL, hslo], by nlinarith [hL, hshi]⟩).2
    have hv' : height B (Rh.coordinate_map (qc, v + delta)) = s := by
      calc
        height B (Rh.coordinate_map (qc, v + delta)) = height B (B.coordinate_map (q, s)) :=
          congrArg (fun x : M => height B x) heq.symm
        _ = s := hv
    linarith only [hv', hshi, hhighBand.1]
  have hDRout : DR ⊆ Kᶜ := stay hDRconn.2 hKclosed.isOpen_compl
    (fun x hx => by rw [frontier_compl]; exact drBoundary x hx)
    ⟨_, hhighDR, hhighOut⟩

  obtain ⟨qmin, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (univ : Set UnitTwoSphere).Nonempty) hhN.continuousOn
  obtain ⟨qmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (univ : Set UnitTwoSphere).Nonempty) hhN.continuousOn
  have cutAnchor (q : UnitTwoSphere) : ∃ p : UnitTwoSphere,
      height N (Q.coordinate_map (p, c)) = hN q := by
    have hm : N.coordinate_map (q, hN q) ∈ range (fun p => Q.coordinate_map (p, c)) := by
      rw [← gSm]; exact mem_range_self q
    obtain ⟨p, hp⟩ := hm
    refine ⟨p, ?_⟩
    calc
      height N (Q.coordinate_map (p, c)) = height N (N.coordinate_map (q, hN q)) :=
        congrArg (fun x : M => height N x) hp
      _ = hN q := (point N heN q (domN q)).2
  obtain ⟨pmin, hpmin⟩ := cutAnchor qmin
  obtain ⟨pmax, hpmax⟩ := cutAnchor qmax
  have cutStep (p q : UnitTwoSphere) (heq : height N (Q.coordinate_map (p, c)) = hN q)
      (t : ℝ) (ht : t ∈ Ioo (-L) L) (hlen : |t - c| ≤ L / 100) :=
    step Q N heQ heN p c t hcut ht
      (bandN p c (by constructor <;> linarith only [hL])).1
      (bandN p c (by constructor <;> linarith only [hL])).2.2
      (by rw [heq]; exact ⟨(bN q).1, by linarith only [(bN q).2, hL]⟩) hlen
  have hn := cutStep pmin qmin hpmin (c - L / 100)
    (by constructor <;> linarith only [hL, hshift.1, hshift.2])
    (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity : 0 < L / 100)])
  have hnerr := hn.2
  rw [hpmin, sub_sub_cancel_left, abs_neg,
    abs_of_pos (by positivity : 0 < L / 100)] at hnerr
  have hnlt : height N (Q.coordinate_map (pmin, c - L / 100)) <
      hN (N.coordinate_inverse (Q.coordinate_map (pmin, c - L / 100))).1 := by
    have hm := hmin
      (mem_univ (N.coordinate_inverse (Q.coordinate_map (pmin, c - L / 100))).1)
    have hupper := (abs_le.mp hnerr).2
    norm_num at hupper
    have hdec : height N (Q.coordinate_map (pmin, c - L / 100)) < hN qmin := by
      linarith only [hL, hupper]
    exact hdec.trans_le hm
  have hnDQ : Q.coordinate_map (pmin, c - L / 100) ∈ DQ := by
    have hp := point Q heQ pmin (s := c - L / 100)
      (by constructor <;> linarith only [hL, hshift.1, hshift.2])
    have hp2 := hp.2
    change (Q.coordinate_inverse (Q.coordinate_map (pmin, c - L / 100))).2 =
      c - L / 100 at hp2
    exact ⟨hp.1, by rw [hp2]; constructor <;> linarith only [hL]⟩
  have hDQout : DQ ⊆ Kᶜ := by
    apply stay hDQconn.2 hKclosed.isOpen_compl
      (fun x hx => by rw [frontier_compl]; exact dqBoundary x hx)
    refine ⟨_, hnDQ, fun hk => hk.2 (Or.inl ?_)⟩
    exact ⟨N.coordinate_inverse _, ⟨(coord N heN hn.1).1, hnlt⟩,
      N.coordinate_map_inverse hn.1⟩
  have hDRdecomp : closure DR = DR ∪ (Sp ∪ S2) := by
    rw [closure_eq_self_union_frontier, hDRfront]
  have hDQdecomp : closure DQ = DQ ∪ (S2 ∪ Sm) := by
    rw [closure_eq_self_union_frontier, hDQfront]
  have hSpcl : Sp ⊆ closure DR := fun _ hx => hDRdecomp.symm ▸ Or.inr (Or.inl hx)
  have hS2cl : S2 ⊆ closure DR ∩ closure DQ := fun _ hx =>
    ⟨hDRdecomp.symm ▸ Or.inr (Or.inr hx), hDQdecomp.symm ▸ Or.inr (Or.inl hx)⟩
  have hSmcl : Sm ⊆ closure DQ := fun _ hx => hDQdecomp.symm ▸ Or.inr (Or.inr hx)
  have h2notSm (x : M) (hx : x ∈ S2) : x ∉ Sm := by
    intro hm; have h1 := (smQ x).mp hm; have h2 := (s2Q x).mp hx
    linarith only [hL, h1.2, h2.2]
  have h2notK (x : M) (hx : x ∈ S2) : x ∉ K := by
    intro hk
    have hi : x ∈ interior K := by
      rw [hKint]; exact ⟨hk, fun h => h.elim (h2notSm x hx) (dqOff x (hS2cl hx).2)⟩
    obtain ⟨y, hyi, hyd⟩ := mem_closure_iff.mp (hS2cl hx).1 (interior K) isOpen_interior hi
    exact hDRout hyd (interior_subset hyi)
  have hKR : K ∩ closure DR = Sp := by
    rw [hDRdecomp]; ext x
    constructor
    · rintro ⟨hk, hd | hp | h2⟩
      · exact (hDRout hd hk).elim
      · exact hp
      · exact (h2notK x h2 hk).elim
    · exact fun hp => ⟨hSpK hp, Or.inr (Or.inl hp)⟩
  have hKQ : K ∩ closure DQ = Sm := by
    rw [hDQdecomp]; ext x
    constructor
    · rintro ⟨hk, hd | h2 | hm⟩
      · exact (hDQout hd hk).elim
      · exact (h2notK x h2 hk).elim
      · exact hm
    · exact fun hm => ⟨hSmK hm, Or.inr (Or.inr hm)⟩
  have hDRQ : Disjoint DR DQ := by
    apply disjoint_left.mpr
    intro x hxr hxq
    have hs : DR ⊆ DQ := stay hDRconn.2 hDQopen (fun y hy => by
      rw [hDQfront]; exact fun h => h.elim (drOff y hy).2.2 (drOff y hy).1) ⟨x, hxr, hxq⟩
    exact dqOff _ (closure_mono hs (hSpcl hxSp)) hxSp
  have hRQ : closure DR ∩ closure DQ = S2 := by
    rw [hDRdecomp]; ext x
    constructor
    · rintro ⟨hd | hp | h2, hq⟩
      · rw [hDQdecomp] at hq
        exact (hq.elim (fun h => disjoint_left.mp hDRQ hd h)
          (fun h => h.elim (drOff x hd).2.2 (drOff x hd).1)).elim
      · exact (dqOff x hq hp).elim
      · exact h2
    · exact fun hx => ⟨Or.inr (Or.inr hx), (hS2cl hx).2⟩
  let E : Set M := Rh.coordinate_map '' {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < f z.1}
  have hEconn : IsConnected E := (stripOC Rh (fun _ => -L) f continuous_const hf
    (fun q => (domf q).1) (fun z hz => dom Rh heRh ⟨hz.1, hz.2.trans (domf z.1).2⟩)).2
  have hEavoid (x : M) (hx : x ∈ E) : x ∉ frontier K := by
    obtain ⟨⟨q, s⟩, hs, rfl⟩ := hx
    have hj := hJ.2 q s hs.1 (by linarith only [hs.2, (bf q).2, hL])
    rw [hKfront]
    rintro (hm | hp)
    · have hlo := hFSm _ hm; linarith only [hlo, hj.2, hL]
    · have heq := ((spRh _).mp hp).2
      dsimp only [height] at heq
      rw [Rh.coordinate_inverse_coordinate_map
        (dom Rh heRh ⟨hs.1, hs.2.trans (domf q).2⟩)] at heq
      exact (ne_of_lt hs.2) heq
  have hEK : E ⊆ interior K := stay hEconn.2 isOpen_interior
    (fun x hx hf => hEavoid x hx (frontier_interior_subset hf))
    ⟨_, ⟨(qc, v - L / 100), by dsimp only [v]; constructor <;>
      linarith only [hL, (bf qc).1], rfl⟩, hlowK⟩
  have hp := cutStep pmax qmax hpmax (c + L / 100)
    (by constructor <;> linarith only [hL, hshift.1, hshift.2])
    (by rw [add_sub_cancel_left, abs_of_pos (by positivity : 0 < L / 100)])
  have hperr := hp.2
  rw [hpmax, add_sub_cancel_left, abs_of_pos (by positivity : 0 < L / 100)] at hperr
  have hplt : hN (N.coordinate_inverse (Q.coordinate_map (pmax, c + L / 100))).1 <
      height N (Q.coordinate_map (pmax, c + L / 100)) := by
    have hm := hmax (mem_univ (N.coordinate_inverse (Q.coordinate_map (pmax, c + L / 100))).1)
    have hlower := (abs_le.mp hperr).1
    norm_num at hlower
    have hinc : hN qmax < height N (Q.coordinate_map (pmax, c + L / 100)) := by
      linarith only [hL, hlower]
    exact hm.trans_lt hinc
  have hpneg : height N (Q.coordinate_map (pmax, c + L / 100)) < -L / 2 := by
    linarith only [hL, (bN qmax).2, (abs_le.mp hperr).2]
  have hpK : Q.coordinate_map (pmax, c + L / 100) ∈ interior K := by
    have hm : Q.coordinate_map (pmax, c + L / 100) ∈ N.coordinate_map ''
        {z : RoundCylinderSpace | -L < z.2 ∧ hN z.1 < z.2 ∧ z.2 < -L / 2} :=
      ⟨N.coordinate_inverse _, ⟨(coord N heN hp.1).1, hplt, hpneg⟩,
        N.coordinate_map_inverse hp.1⟩
    exact (hKiN.symm ▸ hm).1
  have hQplus : Q.region c (c + L / 40) ⊆ interior K := by
    apply stay (regionConn Q heQ (c := c) (d := c + L / 40)
      hcut.1.le (by linarith only [hL, hshift.2])
      (by linarith only [hL])).2 isOpen_interior
    · intro x hx hfront
      have hfK := frontier_interior_subset hfront
      rw [hKfront] at hfK
      have hband := bandN (Q.coordinate_inverse x).1 (height Q x)
        ⟨by linarith only [hx.2.1, hL], hx.2.2.le⟩
      have heq : Q.coordinate_map ((Q.coordinate_inverse x).1, height Q x) = x :=
        Q.coordinate_map_inverse hx.1
      rw [heq] at hband
      rcases hfK with hm | hs
      · exact (ne_of_gt hx.2.1) ((smQ x).mp hm).2
      · have hv := hSpF x hs
        change 7 * L / 10 < (if x ∈ N.carrier then height N x else L) at hv
        rw [if_pos hband.1] at hv
        linarith only [hv, hband.2.1.2, hL]
    · have hpt := point Q heQ pmax (s := c + L / 100)
        (by constructor <;> linarith only [hL, hshift.1, hshift.2])
      have hpt2 := hpt.2
      change (Q.coordinate_inverse (Q.coordinate_map (pmax, c + L / 100))).2 =
        c + L / 100 at hpt2
      exact ⟨_, ⟨hpt.1, by rw [hpt2]; constructor <;> linarith only [hL]⟩, hpK⟩
  obtain ⟨qrmin, _, hrmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (univ : Set UnitTwoSphere).Nonempty) hhR.continuousOn
  have hm2 : Rh.coordinate_map (qrmin, hR qrmin) ∈
      range (fun p : UnitTwoSphere => Q.coordinate_map (p, c - L / 4)) := by
    rw [← gS2]; exact mem_range_self qrmin
  obtain ⟨prmin, hprmin⟩ := hm2
  change Q.coordinate_map (prmin, c - L / 4) = Rh.coordinate_map (qrmin, hR qrmin) at hprmin
  have hvmin : height Rh (Q.coordinate_map (prmin, c - L / 4)) = hR qrmin := by
    rw [hprmin]; exact (point Rh heRh qrmin (domR qrmin)).2
  have hL200 : 0 < L / 200 := by positivity
  have hm := step Q Rh heQ heRh prmin (c - L / 4) (c - L / 4 - L / 200)
    hquarter (by constructor <;> linarith only [hL, hshift.1, hshift.2])
    (bandR prmin (c - L / 4) (by constructor <;> linarith only [hL])).1
    (bandR prmin (c - L / 4) (by constructor <;> linarith only [hL])).2.2
    (by rw [hvmin]; exact ⟨by linarith only [(bR qrmin).1, hL], (bR qrmin).2⟩)
    (by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hL200]
      linarith only [hL])
  have hmerr := hm.2
  rw [hvmin, sub_sub_cancel_left, abs_neg, abs_of_pos hL200] at hmerr
  have hmDR : Q.coordinate_map (prmin, c - L / 4 - L / 200) ∈ DR := by
    have hbnd := bandR prmin (c - L / 4 - L / 200) (by constructor <;> linarith only [hL])
    refine ⟨Rh.coordinate_inverse _, ⟨?_, ?_⟩, Rh.coordinate_map_inverse hm.1⟩
    · linarith only [(bf (Rh.coordinate_inverse
        (Q.coordinate_map (prmin, c - L / 4 - L / 200))).1).2, hbnd.2.1.1]
    · have hmin' := hrmin (mem_univ (Rh.coordinate_inverse
        (Q.coordinate_map (prmin, c - L / 4 - L / 200))).1)
      have hupper := (abs_le.mp hmerr).2
      norm_num at hupper
      have hdec : height Rh (Q.coordinate_map (prmin, c - L / 4 - L / 200)) < hR qrmin := by
        linarith only [hL, hupper]
      exact hdec.trans_le hmin'
  have hQminus : Q.region (c - 13 * L / 50) (c - L / 4) ⊆ DR := by
    apply stay (regionConn Q heQ (c := c - 13 * L / 50) (d := c - L / 4)
      (by linarith only [hL, hshift.1]) hquarter.2.le
      (by linarith only [hL])).2 hDRopen
    · intro x hx hfront
      rw [hDRfront] at hfront
      have hbnd := bandR (Q.coordinate_inverse x).1 (height Q x)
        ⟨hx.2.1.le, by linarith only [hx.2.2, hL]⟩
      have heq : Q.coordinate_map ((Q.coordinate_inverse x).1, height Q x) = x :=
        Q.coordinate_map_inverse hx.1
      rw [heq] at hbnd
      rcases hfront with hs | h2
      · have hs' := ((spRh x).mp hs).2
        linarith only [hbnd.2.1.1, hs', (bf (Rh.coordinate_inverse x).1).2]
      · exact (ne_of_lt hx.2.2) ((s2Q x).mp h2).2
    · have hpt := point Q heQ prmin (s := c - L / 4 - L / 200)
        (by constructor <;> linarith only [hL, hshift.1, hshift.2])
      have hpt2 := hpt.2
      change (Q.coordinate_inverse
        (Q.coordinate_map (prmin, c - L / 4 - L / 200))).2 = c - L / 4 - L / 200 at hpt2
      exact ⟨_, ⟨hpt.1, by rw [hpt2]; constructor <;> linarith only [hL]⟩, hmDR⟩
  let T : Set M := (K ∪ closure DR) ∪ closure DQ
  have hKT : K ⊆ T := fun _ hx => Or.inl (Or.inl hx)
  have hRT : closure DR ⊆ T := fun _ hx => Or.inl (Or.inr hx)
  have hQT : closure DQ ⊆ T := fun _ hx => Or.inr hx
  have hTclosed : IsClosed T := ((hKcompact.union hDRcompact).union hDQcompact).isClosed
  have hSpNhd (x : M) (hx : x ∈ Sp) : T ∈ 𝓝 x := by
    let A : Set M := Rh.coordinate_map '' {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < hR z.1}
    have hAopen : IsOpen A := (stripOC Rh (fun _ => -L) hR continuous_const hhR
      (fun q => (domR q).1) (fun z hz => dom Rh heRh ⟨hz.1, hz.2.trans (domR z.1).2⟩)).1
    have hAx : x ∈ A := by
      have hxg : x ∈ range (fun q => Rh.coordinate_map (q, f q)) := gSp ▸ hx
      obtain ⟨q, rfl⟩ := hxg
      exact ⟨(q, f q), ⟨(domf q).1, bfg q⟩, rfl⟩
    apply Filter.mem_of_superset (hAopen.mem_nhds hAx)
    rintro y ⟨⟨q, s⟩, hs, rfl⟩
    rcases lt_trichotomy s (f q) with hlt | heq | hgt
    · exact hKT (interior_subset (hEK ⟨(q, s), ⟨hs.1, hlt⟩, rfl⟩))
    · subst s
      exact hKT (hSpK (by
        change Rh.coordinate_map (q, f q) ∈ range (fun q => B.coordinate_map (q, 3 * L / 4))
        rw [gSp]
        exact mem_range_self q))
    · exact hRT (subset_closure ⟨(q, s), ⟨hgt, hs.2⟩, rfl⟩)
  have hSmNhd (x : M) (hx : x ∈ Sm) : T ∈ 𝓝 x := by
    have hxq := (smQ x).mp hx
    have hxq' : (Q.coordinate_inverse x).2 = c := hxq.2
    have hxband : x ∈ Q.region (c - L / 40) (c + L / 40) :=
      ⟨hxq.1, by rw [hxq']; constructor <;> linarith only [hL]⟩
    apply Filter.mem_of_superset ((Q.isOpen_region _ _).mem_nhds hxband)
    intro y hy
    rcases lt_trichotomy (height Q y) c with hlt | heq | hgt
    · exact hQT (subset_closure ⟨hy.1, by constructor <;> linarith only [hy.2.1, hlt, hL]⟩)
    · exact hKT (hSmK ((smQ y).mpr ⟨hy.1, heq⟩))
    · exact hKT (interior_subset (hQplus ⟨hy.1, hgt, hy.2.2⟩))
  have hS2Nhd (x : M) (hx : x ∈ S2) : T ∈ 𝓝 x := by
    have hxq := (s2Q x).mp hx
    have hxq' : (Q.coordinate_inverse x).2 = c - L / 4 := hxq.2
    have hxband : x ∈ Q.region (c - 13 * L / 50) (c - 6 * L / 25) :=
      ⟨hxq.1, by rw [hxq']; constructor <;> linarith only [hL]⟩
    apply Filter.mem_of_superset ((Q.isOpen_region _ _).mem_nhds hxband)
    intro y hy
    rcases lt_trichotomy (height Q y) (c - L / 4) with hlt | heq | hgt
    · exact hRT (subset_closure (hQminus ⟨hy.1, hy.2.1, hlt⟩))
    · exact hQT (hS2cl ((s2Q y).mpr ⟨hy.1, heq⟩)).2
    · exact hQT (subset_closure ⟨hy.1, hgt, by linarith only [hy.2.2, hL]⟩)
  have hTopen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rcases hx with (hk | hr) | hq
    · by_cases hi : x ∈ interior K
      · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hi)
          (fun _ hy => hKT (interior_subset hy))
      · have hfK := (mem_frontier_iff_notMem_interior hk).mpr hi
        rw [hKfront] at hfK
        exact hfK.elim (hSmNhd x) (hSpNhd x)
    · rw [hDRdecomp] at hr
      rcases hr with hd | hs | h2
      · exact Filter.mem_of_superset (hDRopen.mem_nhds hd) (fun _ hy => hRT (subset_closure hy))
      · exact hSpNhd x hs
      · exact hS2Nhd x h2
    · rw [hDQdecomp] at hq
      rcases hq with hd | h2 | hs
      · exact Filter.mem_of_superset (hDQopen.mem_nhds hd) (fun _ hy => hQT (subset_closure hy))
      · exact hS2Nhd x h2
      · exact hSmNhd x hs
  have hTW : T ⊆ W := by
    rintro x ((hk | hr) | hq)
    · exact Or.inl (Or.inl (hKU hk))
    · rw [hDRcl] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      apply Or.inl ∘ Or.inr
      rw [← hRhcarrier]
      exact Rh.coordinate_map_mem (dom Rh heRh
        ⟨(domf z.1).1.trans_le hz.1, hz.2.trans_lt (domR z.1).2⟩)
    · rw [hDQcl] at hq
      obtain ⟨z, hz, rfl⟩ := hq
      exact Or.inr (Q.coordinate_map_mem (dom Q heQ
        ⟨hquarter.1.trans_le hz.2.1, hz.2.2.trans_lt hcut.2⟩))
  have hUconn : IsConnected U := by
    apply IsConnected.biUnion_of_chain C.active_nonempty
    · rw [hshape]; exact ordConnected_Icc
    · intro i _; exact (C.neck i).isConnected_carrier
    · intro i hi hn
      change i + 1 ∈ C.shape.active at hn
      exact C.adjacent_overlap i hi hn
  have hUR : IsConnected (U ∪ R.carrier) := IsConnected.union
    ⟨_, hKU (hSpK hxSp), hRhcarrier ▸ (point Rh heRh qc hvdom).1⟩
    hUconn R.isConnected_carrier
  have hWconn : IsConnected W := IsConnected.union
    ⟨Q.coordinate_map (pmin, c), Or.inl (hNU (bandN pmin c
      (by constructor <;> linarith only [hL])).1),
      (point Q heQ pmin hcut).1⟩
    hUR Q.isConnected_carrier
  have hcover : T = W := Subset.antisymm hTW
    (hWconn.2.subset_isClopen ⟨hTclosed, hTopen⟩
      ⟨_, hTW (hKT (hSpK hxSp)), hKT (hSpK hxSp)⟩)
  exact ⟨hKcompact, hKfront, hDRopen, hDRconn, hDQopen, hDQconn, hDRcl, hDQcl,
    hDRcompact, hDQcompact, hDRfront, hDQfront, hKR, hKQ, hRQ, hcover, hEK, hQplus, hQminus⟩

end PoincareConjecture
