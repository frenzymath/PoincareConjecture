import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Compression.MinimalBoth
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Compression.Complement.Preservation









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

private theorem arc_add_period (a b : ℝ) :
    AddCircle.closedIntervalArc p (a + p) (b + p) = AddCircle.closedIntervalArc p a b := by
  ext z
  constructor
  · rintro ⟨t, ht, htz⟩
    refine ⟨t - p, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have h := AddCircle.coe_add_period p (t - p)
    rw [sub_add_cancel] at h
    exact h.symm.trans htz
  · rintro ⟨t, ht, htz⟩
    exact ⟨t + p, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      (AddCircle.coe_add_period p t).trans htz⟩

private structure ComplementarySecondStage {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (R : Set X0) (a b : ℝ) where
  map : C(H0, H0)
  support : Set X0
  compact_support : IsCompact support
  support_interior : support ⊆ interior R
  fixed : ∀ x ∉ support, hamiltonZeroAmbientMap map x = hamiltonZeroAmbientMap phi x
  normal : hamiltonZeroCircleMap map = hamiltonZeroCircleMap phi
  pl : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 map)
  fromOriginal : phi.HomotopyRel map B0
  fromIdentity : (ContinuousMap.id H0).HomotopyRel map B0
  relative : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap map) (interior R)ᶜ
  domain : ∀ side : Bool, PLDomain e (R ∩ hamiltonZeroSecondCircleMap map ⁻¹' AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))
  frontier_eq : ∀ side : Bool, frontier (R ∩ hamiltonZeroSecondCircleMap map ⁻¹' AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) =
    ((R ∩ hamiltonZeroSecondCircleMap map ⁻¹' AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) ∩ frontier R) ∪
      ((R ∩ hamiltonZeroSecondCircleMap map ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap map ⁻¹' {(b : C0)}))
  model : ∀ k : Bool, FrontierResidualModel e univ
    (R ∩ hamiltonZeroSecondCircleMap map ⁻¹' {((if k then b else a : ℝ) : C0)})

private theorem complement_model_complexity_eq_of_surface_eq
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {F F' : Set X0}
    (h : F = F') (M : FrontierResidualModel e univ F) (M' : FrontierResidualModel e univ F')
    [T2Space X0] : M.complexity = M'.complexity := by
  subst F'
  exact M.complexity_eq_of_same_surface M' (subset_univ _)

set_option maxHeartbeats 800000 in
theorem exists_hamiltonZero_complementary_second_phase_kernel_control
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R) {c a b : ℝ}
    (ha : c < a) (hab : a < b) (hb : b < c + p)
    (he : PLDomain e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (heC : PLDomain e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p b (a + p)))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)})))
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0))
    (hne : ∀ theta ∈ ({a, b} : Set ℝ),
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)}).Nonempty) :
    ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
      ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)})) ∧
      ∀ theta ∈ ({a, b} : Set ℝ),
      let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}
      let M := S \ frontier R
      ∃ hMN : M ⊆ N, ∀ x : M, ∀ gamma : FundamentalGroup M x,
        FundamentalGroup.map (ContinuousMap.inclusion hMN) x gamma = 1 →
          FundamentalGroup.map (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)) x gamma = 1 := by
  classical
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : Fact (0 < p) := ⟨by norm_num⟩
  let lo (side : Bool) : ℝ := if side then b else a
  let up (side : Bool) : ℝ := if side then a + p else b
  let cut (side : Bool) : ℝ := if side then (a + b) / 2 else c
  have hlo (side : Bool) : cut side < lo side := by
    cases side <;> dsimp [cut, lo] <;> linarith
  have hlu (side : Bool) : lo side < up side := by
    cases side <;> dsimp [lo, up] <;> linarith
  have hup (side : Bool) : up side < cut side + p := by
    cases side <;> dsimp [up, cut] <;> linarith
  let theta (k : Bool) : ℝ := if k then b else a
  have htheta (k : Bool) : theta k ∈ ({a, b} : Set ℝ) := by cases k <;> simp [theta]
  have hcompact (f : C(H0, H0)) (t : C0) :
      IsCompact (R ∩ hamiltonZeroSecondCircleMap f ⁻¹' {t}) :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset
      (heR.closed.inter (isClosed_singleton.preimage (hamiltonZeroSecondCircleMap f).continuous))
      (subset_univ _)
  have hinitial (k : Bool) : Nonempty (FrontierResidualModel e univ
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta k : C0)})) :=
    nonempty_residual_model_of_compact_marked_surface e
      isCompact_hamiltonZeroAmbient heR (hcompact phi (theta k)) (hne _ (htheta k))
      (hreg _ (htheta k)).exists_marked_surface_chart
  let initial : ComplementarySecondStage e d phi R a b := {
    map := phi
    support := ∅
    compact_support := isCompact_empty
    support_interior := empty_subset _
    fixed := fun _ _ => rfl
    normal := rfl
    pl := hphi
    fromOriginal := ContinuousMap.HomotopyRel.refl phi B0
    fromIdentity := F0
    relative := ContinuousMap.HomotopyRel.refl (hamiltonZeroAmbientMap phi) (interior R)ᶜ
    domain := fun side => by cases side; exact he; exact heC
    frontier_eq := fun side => by
      cases side
      · exact hfront
      · exact frontier_complementary_circle_slab (hamiltonZeroSecondCircleMap phi)
          heR.closed ha hab hb he hfront
    model := fun k => Classical.choice (hinitial k) }
  let measure (s : ComplementarySecondStage e d phi R a b) :=
    (s.model false).complexity + (s.model true).complexity
  have hex : ∃ n : ℕ, ∃ s : ComplementarySecondStage e d phi R a b, measure s = n :=
    ⟨measure initial, initial, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hminimal (t : ComplementarySecondStage e d phi R a b) : measure s ≤ measure t := by
    rw [hs]
    exact Nat.find_min' hex ⟨t, rfl⟩
  let face (f : C(H0, H0)) (k : Bool) := R ∩ hamiltonZeroSecondCircleMap f ⁻¹' {(theta k : C0)}
  have habq : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico c (c + p) by constructor <;> linarith)
      (show b ∈ Ico c (c + p) by constructor <;> linarith)).mp h)
  have hdisab (f : C(H0, H0)) : Disjoint (face f false) (face f true) :=
    disjoint_left.mpr (fun _ hx hy => habq (hx.2.symm.trans hy.2))
  have hdis (f : C(H0, H0)) (k : Bool) : Disjoint (face f k) (face f (!k)) := by
    cases k with
    | false => exact hdisab f
    | true => exact (hdisab f).symm
  refine ⟨s.map, s.support, s.compact_support, s.support_interior, s.fixed, s.normal, s.pl,
    ⟨s.fromOriginal⟩, ⟨s.fromIdentity⟩, ⟨s.relative⟩, ?_⟩
  intro side
  let N := R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)
  have hNc : IsCompact N :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset (s.domain side).closed (subset_univ _)
  have hfront_s (k : Bool) : frontier N = (N ∩ frontier R) ∪ (face s.map k ∪ face s.map (!k)) := by
    cases k with
    | false => exact s.frontier_eq side
    | true => simpa only [face, theta, Bool.false_eq_true, Bool.not_true, if_false, if_true,
        union_comm] using s.frontier_eq side
  have hfront_ordered : frontier N = (N ∩ frontier R) ∪
      ((R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' {(lo side : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' {(up side : C0)})) := by
    cases side with
    | false => exact s.frontier_eq false
    | true => simpa only [N, lo, up, if_true, AddCircle.coe_add_period, union_comm] using
        s.frontier_eq true
  have hdis_ordered : Disjoint
      (R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' {(lo side : C0)})
      (R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' {(up side : C0)}) := by
    cases side with
    | false => exact hdisab s.map
    | true => simpa only [lo, up, face, theta, if_true, Bool.false_eq_true, if_false,
        AddCircle.coe_add_period] using (hdisab s.map).symm
  refine ⟨s.domain side, s.frontier_eq side, ?_⟩
  intro value hvalue
  obtain ⟨k, rfl⟩ : ∃ k : Bool, value = theta k := by
    rcases hvalue with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  let endpoint : Bool := if side then !k else k
  let selected : ℝ := if endpoint then up side else lo side
  have hselected : selected ∈ ({lo side, up side} : Set ℝ) := by
    cases he : endpoint <;> simp [selected, he]
  have hselected_coe : (selected : C0) = (theta k : C0) := by
    cases side <;> cases k <;> simp [selected, endpoint, lo, up, theta]
  have hopposite_coe : ((if !endpoint then up side else lo side : ℝ) : C0) =
      (theta (!k) : C0) := by
    cases side <;> cases k <;> simp [endpoint, lo, up, theta]
  let S := face s.map k
  have halternative := hamiltonZero_second_slab_disk_alternative e s.map heR.closed
    (s.domain side) hfront_ordered hdis_ordered selected hselected
  rw [hselected_coe] at halternative
  obtain ⟨hMN, halt⟩ := halternative
  refine ⟨hMN, ?_⟩
  intro x
  obtain hker | ⟨j, rim, hj, hi, hjN, hjrim, hproper, havoid, hessential⟩ := halt x
  · exact hker
  · have hrim (z : V2) (hz : z ∈ Q) :
        j z ∈ R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' {(selected : C0)} := by
      rw [hselected_coe]
      exact (hjrim ⟨z, hz⟩) ▸ (rim ⟨z, hz⟩).property.1
    obtain ⟨P, psi, A, G, hPB, hcut, hcutc, hA, heA, hSA, hAR,
      hstart, hend, hfixed, hnormal, hpsi, ⟨H⟩, ⟨Fpsi⟩, hfirst,
      hGa, hGb, hslab, hopen, hside⟩ :=
      exists_hamiltonZero_second_slab_map_at_endpoint hd s.pl s.fromIdentity endpoint
        (hlo side) (hlu side) (hup side) hNc (s.domain side) hfront_ordered
        hj hi hjN hproper hrim havoid
    change R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(selected : C0)} =
      (R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' {(selected : C0)}) \ P.openStrip ∪ P.endDisks at hGa
    rw [hselected_coe] at hGa
    rw [hopposite_coe] at hGb
    change face psi k = (face s.map k \ P.openStrip) ∪ P.endDisks at hGa
    change face psi (!k) = face s.map (!k) at hGb
    change ∀ z ∈ D ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ frontier N →
      P.map z ∈ R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹' {(selected : C0)} at hside
    rw [hselected_coe] at hside
    have htotal (y : X0) (hy : y ∉ s.support ∪ A) :
        hamiltonZeroAmbientMap psi y = hamiltonZeroAmbientMap phi y := by
      rw [← hend, hfixed 1 y (fun h => hy (Or.inr (interior_subset h)))]
      exact s.fixed y (fun h => hy (Or.inl h))
    have htotalint : s.support ∪ A ⊆ interior R := union_subset s.support_interior hAR
    have hnewfront := P.marked_frontier_cut hNc (hfront_s k) (hdis s.map k) hopen hPB hside
    have hfrontpsi_k : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) =
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) ∩ frontier R) ∪
          (face psi k ∪ face psi (!k)) := by
      rw [hslab, hGa, hGb, ← union_assoc]
      exact hnewfront.1
    have hfrontpsi : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) =
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) ∩ frontier R) ∪
          ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
            (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)})) := by
      cases k with
      | false => exact hfrontpsi_k
      | true => simpa only [face, theta, Bool.false_eq_true, Bool.not_true, if_false, if_true,
          union_comm] using hfrontpsi_k
    have hnewPL : PLDomain e
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) := hslab ▸ hcut
    have hfrontpsi_ordered : frontier
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) =
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) ∩ frontier R) ∪
          ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(lo side : C0)}) ∪
            (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(up side : C0)})) := by
      cases side with
      | false => exact hfrontpsi
      | true => simpa only [lo, up, if_true, AddCircle.coe_add_period, union_comm] using hfrontpsi
    have holdComp : PLDomain e (R ∩ hamiltonZeroSecondCircleMap s.map ⁻¹'
        AddCircle.closedIntervalArc p (up side) (lo side + p)) := by
      cases side with
      | false => exact s.domain true
      | true => simpa only [lo, up, if_true, Bool.false_eq_true, if_false, arc_add_period]
          using s.domain false
    have hcompPL := plDomain_complementary_circle_slab_of_supported_map
      (hamiltonZeroSecondCircleMap s.map) (hamiltonZeroSecondCircleMap psi) heR.closed
      (hlo side) (hlu side) (hup side) holdComp hnewPL hfrontpsi_ordered hA.isClosed hAR
      (by
        intro y hy
        have heq : hamiltonZeroAmbientMap psi y = hamiltonZeroAmbientMap s.map y := by
          rw [← hend]
          exact hfixed 1 y (fun h => hy (interior_subset h))
        simp only [hamiltonZeroSecondCircleMap_ambient, heq])
    have hcompFront := frontier_complementary_circle_slab
      (hamiltonZeroSecondCircleMap psi) heR.closed (hlo side) (hlu side) (hup side)
      hnewPL hfrontpsi_ordered
    have newdomains (v : Bool) : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
        AddCircle.closedIntervalArc p (lo v) (up v)) := by
      cases side <;> cases v
      · exact hnewPL
      · exact hcompPL
      · simpa only [lo, up, if_true, Bool.false_eq_true, if_false, arc_add_period] using hcompPL
      · exact hnewPL
    have newfronts (v : Bool) : frontier
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo v) (up v)) =
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo v) (up v)) ∩ frontier R) ∪
          ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
            (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)})) := by
      cases side <;> cases v
      · exact hfrontpsi
      · exact hcompFront
      · simpa only [lo, up, if_true, Bool.false_eq_true, if_false, arc_add_period, AddCircle.coe_add_period,
          union_comm] using hcompFront
      · exact hfrontpsi
    have hfrontpsi_at (u : Bool) : frontier
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) =
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)) ∩ frontier R) ∪
          (face psi u ∪ face psi (!u)) := by
      cases u with
      | false => exact hfrontpsi
      | true => simpa only [face, theta, Bool.false_eq_true, Bool.not_true, if_false, if_true,
          union_comm] using hfrontpsi
    have hnewne (u : Bool) : (face psi u).Nonempty := by
      by_cases hu : u = k
      · subst u
        rw [hGa]
        exact ⟨P.map (0, (1 / 2 : ℝ)), Or.inr
          ⟨(0, 1 / 2), ⟨mem_closedBall_self zero_le_one, Or.inr rfl⟩, rfl⟩⟩
      · have hueq : u = !k := by
          cases u <;> cases k <;> first | rfl | exact (hu rfl).elim
        rw [hueq, hGb]
        let i : Fin (s.model (!k)).count := ⟨0, (s.model (!k)).positive⟩
        exact ((s.model (!k)).component i).2.1.nonempty.mono
          ((s.model (!k)).component i).2.2.1
    have hmodels (u : Bool) : Nonempty (FrontierResidualModel e univ (face psi u)) := by
      have hlocal := marked_surface_charts_after_interior_change hnewPL isClosed_frontier
        (hcompact psi (theta (!u))).isClosed (hfrontpsi_at u) (hdis psi u)
        (s.compact_support.union hA).isClosed
        (disjoint_interior_frontier.mono_left htotalint)
        (S := face phi u)
        (by
          intro y hy
          have hq : hamiltonZeroSecondCircleMap psi y = hamiltonZeroSecondCircleMap phi y := by
            simp only [hamiltonZeroSecondCircleMap_ambient, htotal y hy]
          simp only [face, mem_inter_iff, mem_preimage, mem_singleton_iff, hq])
        (by
          intro y hy
          obtain ⟨T, hyT, hcompat, hkind⟩ := (hreg _ (htheta u)).exists_marked_surface_chart y hy.1
          rcases hkind with ⟨_, _, _, _, hdis⟩ | ⟨ell, psi, u, v, hu, hv, huv, hS, hB⟩
          · exact (disjoint_left.mp hdis hyT hy.2).elim
          · exact ⟨T, ell, psi, u, v, hyT, hcompat, hu, hv, huv, hS, hB⟩)
      exact nonempty_residual_model_of_compact_marked_surface e
        isCompact_hamiltonZeroAmbient heR (hcompact psi (theta u)) (hnewne u) hlocal
    let newmodels (u : Bool) := Classical.choice (hmodels u)
    let ambientH : (hamiltonZeroAmbientMap s.map).HomotopyRel
        (hamiltonZeroAmbientMap psi) (interior R)ᶜ := {
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hstart
      map_one_left := hend
      prop' := fun t y hy => hfixed t y (fun h => hy (hAR (interior_subset h))) }
    let t : ComplementarySecondStage e d phi R a b := {
      map := psi
      support := s.support ∪ A
      compact_support := s.compact_support.union hA
      support_interior := htotalint
      fixed := htotal
      normal := hfirst.trans s.normal
      pl := hpsi
      fromOriginal := s.fromOriginal.trans H
      fromIdentity := Fpsi
      relative := s.relative.trans ambientH
      domain := newdomains
      frontier_eq := newfronts
      model := newmodels }
    let rimS : C(Q, S) := (ContinuousMap.inclusion (sdiff_subset : S \ frontier R ⊆ S)).comp rim
    have hrimS (z : Q) : (rimS z : X0) = j z := hjrim z |>.symm
    have hdecrease := P.marked_face_residual_complexity_decreases hNc (s.domain side)
      (fun _ hx => (hfront_s k).symm.subset (Or.inr (Or.inl hx))) hopen hside hGa
      (subset_univ _) rimS hrimS hessential (s.model k) (newmodels k)
    have hsame := complement_model_complexity_eq_of_surface_eq hGb (newmodels (!k)) (s.model (!k))
    have hmin := hminimal t
    change (s.model false).complexity + (s.model true).complexity ≤
      (newmodels false).complexity + (newmodels true).complexity at hmin
    cases k with
    | false =>
      change (newmodels true).complexity = (s.model true).complexity at hsame
      omega
    | true =>
      change (newmodels false).complexity = (s.model false).complexity at hsame
      omega

end PoincareConjecture.M76
