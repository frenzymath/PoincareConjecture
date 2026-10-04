import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.MarkedIntervalDiskAttachment

/-!
# A three-piece disk map with its complete marked boundary

Perform two prescribed whole-interval attachments on the original three
source disks. The complete final boundary is the preimage of the target mark,
and the map retains all three original source maps and target-set preimages.
See Dehn039, section 6, and Hatcher, section 3.1, printed pp. 56--57.
-/

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareMT.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)

/-- Construct a target-marked disk from three original finite PL disk pairs
and four prescribed arm charts. The intermediate outgoing arm and its exact
endpoint contact are constructed by the first actual attachment. -/
theorem exists_three_piece_marked_disk_map
    {E0 E1 E2 F X ι : Type*}
    [NormedAddCommGroup E0] [NormedSpace ℝ E0] [FiniteDimensional ℝ E0]
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S0 Q0 W0 : Set E0} {S1 Q1 L1 R1 : Set E1} {S2 Q2 W2 : Set E2}
    {a0 b0 : E0} {aL bL aR bR : E1} {a2 b2 : E2}
    (hS0 : IsFinitePLBallPair P2 S0 Q0) (hS1 : IsFinitePLBallPair P2 S1 Q1)
    (hS2 : IsFinitePLBallPair P2 S2 Q2)
    (hW0 : IsFinitePLBallPair ℝ W0 {a0, b0})
    (hL1 : IsFinitePLBallPair ℝ L1 {aL, bL})
    (hR1 : IsFinitePLBallPair ℝ R1 {aR, bR})
    (hW2 : IsFinitePLBallPair ℝ W2 {a2, b2})
    (hW0Q : W0 ⊆ Q0) (hL1Q : L1 ⊆ Q1) (hR1Q : R1 ⊆ Q1) (hW2Q : W2 ⊆ Q2)
    (hdisj : Disjoint L1 R1)
    (hab0 : a0 ≠ b0) (habL : aL ≠ bL) (hab2 : a2 ≠ b2)
    (p0 : I01 ≃ₜ W0) (pL : I01 ≃ₜ L1) (pR : I01 ≃ₜ R1) (p2 : I01 ≃ₜ W2)
    (hp0 : p0.IsFinitePL) (hpL : pL.IsFinitePL)
    (hpR : pR.IsFinitePL) (hp2 : p2.IsFinitePL)
    (hp00 : (p0 i0 : E0) = a0) (hp01 : (p0 i1 : E0) = b0)
    (hpL0 : (pL i0 : E1) = aL) (hpL1 : (pL i1 : E1) = bL)
    (hpR0 : (pR i0 : E1) = aR) (hpR1 : (pR i1 : E1) = bR)
    (hp20 : (p2 i0 : E2) = a2) (hp21 : (p2 i1 : E2) = b2)
    {f0 : E0 → X} {f1 : E1 → X} {f2 : E2 → X}
    (hf0 : PolyhedralPLInCharts e f0 S0) (hf1 : PolyhedralPLInCharts e f1 S1)
    (hf2 : PolyhedralPLInCharts e f2 S2)
    (hagreeL : ∀ t : I01, f0 (p0 t) = f1 (pL t))
    (hagreeR : ∀ t : I01, f1 (pR t) = f2 (p2 t))
    (Z : Set X)
    (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hQ1 : Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ R1) ∪ L1)
    (hQ2 : Q2 = (S2 ∩ f2 ⁻¹' Z) ∪ W2)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = {a0, b0})
    (hmarkL : L1 ∩ f1 ⁻¹' Z = {aL, bL})
    (hmarkR : R1 ∩ f1 ⁻¹' Z = {aR, bR})
    (hmark2 : W2 ∩ f2 ⁻¹' Z = {a2, b2}) :
    ∃ (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL)
      (m : (TR ∪ TL : Set P2) ≃ₜ TR) (n2 : S2 ≃ₜ TL) (g : P2 → X),
      let j0 : S0 → P2 := fun x ↦ m ⟨n0 x, Or.inl (n0 x).property⟩
      let j1 : S1 → P2 := fun x ↦ m ⟨n1 x, Or.inr (n1 x).property⟩
      let j2 : S2 → P2 := fun x ↦ n2 x
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ m.IsFinitePL ∧ n2.IsFinitePL ∧
      (∀ t : I01, j0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ =
        j1 ⟨pL t, hS1.1 (hL1Q (pL t).property)⟩) ∧
      (∀ t : I01, j1 ⟨pR t, hS1.1 (hR1Q (pR t).property)⟩ =
        j2 ⟨p2 t, hS2.1 (hW2Q (p2 t).property)⟩) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S0, g (j0 x) = f0 x) ∧
      (∀ x : S1, g (j1 x) = f1 x) ∧ (∀ x : S2, g (j2 x) = f2 x) ∧
      g '' (TR ∪ TL) = (f0 '' S0 ∪ f1 '' S1) ∪ f2 '' S2 ∧
      IsFinitePLBallPair P2 (TR ∪ TL) ((TR ∪ TL) ∩ g ⁻¹' Z) ∧
      ∀ U : Set X, (TR ∪ TL) ∩ g ⁻¹' U =
        (j0 '' {x : S0 | f0 x ∈ U} ∪ j1 '' {x : S1 | f1 x ∈ U}) ∪
          j2 '' {x : S2 | f2 x ∈ U} := by
  obtain ⟨n0, n1, p, g01, V, q, hn0, hn1, _, _, _, hn0p, hn1p,
    hg01, hkeep0, hkeep1, him01, hpre01, hball01, _, hV, hq, hqval, hmarkV⟩ :=
    exists_marked_interval_disk_map e hcompat hS0 hS1 hW0 hL1 hW0Q hL1Q
      hab0 habL p0 pL hp0 hpL hp00 hp01 hpL0 hpL1 hf0 hf1 hagreeL
      Z hQ0 hmark0 hmarkL hR1 hR1Q (Set.disjoint_iff_inter_eq_empty.mp hdisj)
      pR hpR hpR0 hpR1 hQ1 hmarkR
  have hVQ : V ⊆ ((TR ∪ TL) ∩ g01 ⁻¹' Z) ∪ V := subset_union_right
  have hends : (q i0 : P2) ≠ (q i1 : P2) := by
    intro heq
    have h01 := congrArg (fun t : I01 ↦ (t : ℝ)) (q.injective (Subtype.ext heq))
    norm_num at h01
  have hagree (t : I01) : g01 (q t) = f2 (p2 t) := by
    rw [hqval]
    exact (hkeep1 ⟨pR t, hS1.1 (hR1Q (pR t).property)⟩).trans (hagreeR t)
  obtain ⟨m, n2, r, g, hm, hn2, _, _, _, hmr, hn2r,
    hg, hkeep01, hkeep2, him, hpre, hball⟩ :=
    exists_terminal_marked_interval_disk_map e hcompat hball01 hS2 hV hW2 hVQ hW2Q
      hends hab2 q p2 hq hp2 rfl rfl hp20 hp21 hg01 hf2 hagree
      Z rfl hmarkV hmark2 hQ2
  have hfinal0 (x : S0) : g (m ⟨n0 x, Or.inl (n0 x).property⟩) = f0 x :=
    (hkeep01 ⟨n0 x, Or.inl (n0 x).property⟩).trans (hkeep0 x)
  have hfinal1 (x : S1) : g (m ⟨n1 x, Or.inr (n1 x).property⟩) = f1 x :=
    (hkeep01 ⟨n1 x, Or.inr (n1 x).property⟩).trans (hkeep1 x)
  refine ⟨n0, n1, m, n2, g, hn0, hn1, hm, hn2, ?_, ?_,
    hg, hfinal0, hfinal1, hkeep2, ?_, hball, ?_⟩
  · intro t
    exact congrArg (fun x : (TR ∪ TL : Set P2) ↦ (m x : P2))
      (Subtype.ext ((hn0p t).trans (hn1p t).symm))
  · intro t
    change (m ⟨n1 ⟨pR t, _⟩, _⟩ : P2) = n2 ⟨p2 t, _⟩
    have heq : (⟨n1 ⟨pR t, hS1.1 (hR1Q (pR t).property)⟩,
        Or.inr (n1 ⟨pR t, hS1.1 (hR1Q (pR t).property)⟩).property⟩ :
        (TR ∪ TL : Set P2)) = ⟨q t, hball01.1 (hVQ (q t).property)⟩ :=
      Subtype.ext (hqval t).symm
    rw [heq]
    exact (hmr t).trans (hn2r t).symm
  · rwa [him01] at him
  · intro U
    ext y
    constructor
    · intro hy
      rcases (hpre U).subset hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · rcases (hpre01 U).subset ⟨x.property, hx⟩ with
          ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
        · refine Or.inl (Or.inl ⟨z, hz, ?_⟩)
          exact congrArg (fun w : (TR ∪ TL : Set P2) ↦ (m w : P2)) (Subtype.ext hzx)
        · refine Or.inl (Or.inr ⟨z, hz, ?_⟩)
          exact congrArg (fun w : (TR ∪ TL : Set P2) ↦ (m w : P2)) (Subtype.ext hzx)
      · exact Or.inr ⟨x, hx, rfl⟩
    · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
      · refine ⟨Or.inl (m ⟨n0 x, Or.inl (n0 x).property⟩).property, ?_⟩
        change g (m ⟨n0 x, Or.inl (n0 x).property⟩) ∈ U
        rw [hfinal0]
        exact hx
      · refine ⟨Or.inl (m ⟨n1 x, Or.inr (n1 x).property⟩).property, ?_⟩
        change g (m ⟨n1 x, Or.inr (n1 x).property⟩) ∈ U
        rw [hfinal1]
        exact hx
      · refine ⟨Or.inr (n2 x).property, ?_⟩
        change g (n2 x) ∈ U
        rw [hkeep2]
        exact hx

end PoincareMT.M76.Dehn
