import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripExteriorRims

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

structure MarkedPLIntervalPath {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (Fmark : Set X) (f : E → X) (W : Set E) (a b : E) where
  chart : I01 ≃ₜ W
  chart_finitePL : chart.IsFinitePL
  chart_zero : (chart (0 : unitInterval) : E) = a
  chart_one : (chart (1 : unitInterval) : E) = b
  initial : Fmark
  terminal : Fmark
  initial_val : (initial : X) = f a
  terminal_val : (terminal : X) = f b
  path : Path initial terminal
  path_val : ∀ t : I01, (path t : X) = f (chart t)
  path_range : range (fun t : I01 ↦ (path t : X)) = f '' W

theorem nonempty_markedPLIntervalPath
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {S Q W : Set E} {a b : E} {Fmark : Set X} (f : E → X)
    (hf : ContinuousOn f S) (hfmark : MapsTo f Q Fmark)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hWS : W ⊆ S) (hWQ : W ⊆ Q) :
    Nonempty (MarkedPLIntervalPath Fmark f W a b) := by
  obtain ⟨p, hp, hp0, hp1⟩ := hW.exists_unitInterval_chart_with_endpoints hab
  let x : Fmark := ⟨f a, hfmark (hWQ (hW.1 (by simp)))⟩
  let y : Fmark := ⟨f b, hfmark (hWQ (hW.1 (by simp)))⟩
  let r : Path x y :=
    { toFun := fun t ↦ ⟨f (p t), hfmark (hWQ (p t).property)⟩
      continuous_toFun := (hf.comp_continuous
        (continuous_subtype_val.comp p.continuous) (fun t ↦ hWS (p t).property)).subtype_mk _
      source' := Subtype.ext (congrArg f hp0)
      target' := Subtype.ext (congrArg f hp1) }
  refine ⟨{
    chart := p, chart_finitePL := hp, chart_zero := hp0, chart_one := hp1
    initial := x, terminal := y, initial_val := rfl, terminal_val := rfl
    path := r, path_val := fun _ ↦ rfl, path_range := ?_ }⟩
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨p t, (p t).property, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨t, ht⟩ := p.surjective ⟨w, hw⟩
    exact ⟨t, congrArg f (congrArg Subtype.val ht)⟩

theorem exists_original_exterior_paths
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {S Q : Set E} (hS : IsFinitePLBallPair P2 S Q) (c : Bool → P2 → E)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source S)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    {Fmark : Set X} (f : E → X) (hf : ContinuousOn f S) (hfmark : MapsTo f Q Fmark) :
    ∃ (A M C L R : Set E) (s0 s1 : Bool) (u v : E),
      let a0 := c false (0, farArmParameter (!s0))
      let a1 := c false (1, farArmParameter (!s0))
      let l0 := c false (0, farArmParameter s0)
      let l1 := c false (1, farArmParameter s0)
      let r0 := c true (0, farArmParameter s1)
      let r1 := c true (1, farArmParameter s1)
      let c0 := c true (0, farArmParameter (!s1))
      let c1 := c true (1, farArmParameter (!s1))
      let WA := c false '' arm (farArmParameter (!s0))
      let WL := c false '' arm (farArmParameter s0)
      let WR := c true '' arm (farArmParameter s1)
      let WC := c true '' arm (farArmParameter (!s1))
      ∃ (_pA : MarkedPLIntervalPath Fmark f (A ∩ Q) a0 a1)
        (_pC : MarkedPLIntervalPath Fmark f (C ∩ Q) c1 c0)
        (_pL : MarkedPLIntervalPath Fmark f L l0 u)
        (_pR : MarkedPLIntervalPath Fmark f R v l1),
        IsFinitePLBallPair P2 A ((A ∩ Q) ∪ WA) ∧
        IsFinitePLBallPair P2 M (((M ∩ Q) ∪ WL) ∪ WR) ∧
        IsFinitePLBallPair P2 C ((C ∩ Q) ∪ WC) ∧
        Disjoint A M ∧ Disjoint M C ∧ Disjoint A C ∧
        ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S ∧
        (c false '' source) ∩ A = WA ∧ (c false '' source) ∩ M = WL ∧
        (c true '' source) ∩ M = WR ∧ (c true '' source) ∩ C = WC ∧
        Disjoint A (c true '' source) ∧ Disjoint C (c false '' source) ∧
        IsFinitePLBallPair ℝ (A ∩ Q) {a0, a1} ∧
        IsFinitePLBallPair ℝ (C ∩ Q) {c0, c1} ∧
        ((u = r0 ∧ v = r1) ∨ (u = r1 ∧ v = r0)) ∧ u ≠ v ∧
        IsFinitePLBallPair ℝ L {l0, u} ∧ IsFinitePLBallPair ℝ R {v, l1} ∧
        Disjoint L R ∧ L ∪ R = M ∩ Q ∧
        L ∩ WL = {l0} ∧ R ∩ WL = {l1} ∧ L ∩ WR = {u} ∧ R ∩ WR = {v} := by
  obtain ⟨A, M, C, L, R, s0, s1, u, v, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hA1, hC0, hAI, hCI, hpair, huv,
    hL, hR, hLR, hLRQ, hLW, hRW, hLZ, hRZ⟩ :=
    exists_strip_exterior_disks_with_rim_intervals hS c hcPL hci hcS hcQ hdisj
  have hfar (s : Bool) : farArmParameter s ∈ Icc (-1 : ℝ) 1 := by
    cases s <;> norm_num [farArmParameter]
  have hpoint (i s : Bool) (t : I01) :
      c i ((t : ℝ), farArmParameter s) ∈ c i '' source :=
    ⟨((t : ℝ), farArmParameter s), ⟨t.property, hfar s⟩, rfl⟩
  have hu : u ∈ c true '' source := by
    rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hpoint true s1 0
    · exact hpoint true s1 1
  have hv : v ∈ c true '' source := by
    rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hpoint true s1 1
    · exact hpoint true s1 0
  have hlne : c false (0, farArmParameter s0) ≠ u := by
    intro heq
    exact Set.disjoint_left.mp hdisj (heq ▸ hpoint false s0 0) hu
  have hrne : v ≠ c false (1, farArmParameter s0) := by
    intro heq
    exact Set.disjoint_left.mp hdisj (hpoint false s0 1) (heq ▸ hv)
  obtain ⟨_, hane, _⟩ := exists_embedded_strip_arm_parameter
    (c false) (hcPL false) (hci false) (farArmParameter (!s0)) (hfar (!s0))
  obtain ⟨_, hcne, _⟩ := exists_embedded_strip_arm_parameter
    (c true) (hcPL true) (hci true) (farArmParameter (!s1)) (hfar (!s1))
  have hLQ : L ⊆ Q := (subset_union_left.trans hLRQ.subset).trans inter_subset_right
  have hRQ : R ⊆ Q := (subset_union_right.trans hLRQ.subset).trans inter_subset_right
  obtain ⟨pA⟩ := nonempty_markedPLIntervalPath f hf hfmark hAI hane
    (inter_subset_right.trans hS.1) inter_subset_right
  have hCI' : IsFinitePLBallPair ℝ (C ∩ Q)
      {c true (1, farArmParameter (!s1)), c true (0, farArmParameter (!s1))} := by
    rwa [pair_comm]
  obtain ⟨pC⟩ := nonempty_markedPLIntervalPath f hf hfmark hCI' hcne.symm
    (inter_subset_right.trans hS.1) inter_subset_right
  obtain ⟨pL⟩ := nonempty_markedPLIntervalPath f hf hfmark hL hlne (hLQ.trans hS.1) hLQ
  obtain ⟨pR⟩ := nonempty_markedPLIntervalPath f hf hfmark hR hrne (hRQ.trans hS.1) hRQ
  exact ⟨A, M, C, L, R, s0, s1, u, v, pA, pC, pL, pR,
    hA, hM, hC, hAM, hMC, hAC, hcover, h0A, h0M, h1M, h1C, hA1, hC0,
    hAI, hCI, hpair, huv, hL, hR, hLR, hLRQ, hLW, hRW, hLZ, hRZ⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
