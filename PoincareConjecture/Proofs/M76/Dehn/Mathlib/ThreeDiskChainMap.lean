import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.PrescribedIntervalSourceFibers

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)

private theorem exists_interval_image_parameter
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S W : Set E} {T : Set F} {a b : E}
    (H : S ≃ₜ T) (hH : H.IsFinitePL)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hWS : W ⊆ S)
    (p : I01 ≃ₜ W) (hp : p.IsFinitePL)
    (hp0 : (p (0 : unitInterval) : E) = a)
    (hp1 : (p (1 : unitInterval) : E) = b) :
    ∃ (V : Set F) (q : I01 ≃ₜ V),
      IsFinitePLBallPair ℝ V {(q (0 : unitInterval) : F), (q (1 : unitInterval) : F)} ∧
      q.IsFinitePL ∧
      (∀ t : I01, (q t : F) = H ⟨p t, hWS (p t).property⟩) ∧
      V = (fun x : S => (H x : F)) '' (Subtype.val ⁻¹' W) := by
  obtain ⟨f, hf, hval⟩ := hH
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    have hsub : (⟨x, hx⟩ : S) = ⟨y, hy⟩ :=
      H.injective (Subtype.ext ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm)))
    exact congrArg (fun z : S => (z : E)) hsub
  have hcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hfW : FinitePiecewiseAffineOn f W := by
    rw [← hKs]
    exact hf.restrict K hK (hKs.subset.trans hWS)
  obtain ⟨j, hj, hjval⟩ := hfW.exists_homeomorph_image (hinj.mono hWS)
  let q := p.trans j
  have hqval (t : I01) : (q t : F) = f (p t) := hjval (p t)
  have hball : IsFinitePLBallPair ℝ (f '' W)
      {(q (0 : unitInterval) : F), (q (1 : unitInterval) : F)} := by
    have h := hW.image hfW (hinj.mono hWS)
    rw [image_pair] at h
    simpa only [hqval, hp0, hp1] using h
  refine ⟨f '' W, q, hball, hp.trans hj, ?_, ?_⟩
  · intro t
    exact (hqval t).trans (hval ⟨p t, hWS (p t).property⟩).symm
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hWS hx⟩, hx, hval ⟨x, hWS hx⟩⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hval x).symm⟩

theorem exists_three_disk_chain_map
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
    (hp00 : (p0 (0 : unitInterval) : E0) = a0)
    (hp01 : (p0 (1 : unitInterval) : E0) = b0)
    (hpL0 : (pL (0 : unitInterval) : E1) = aL)
    (hpL1 : (pL (1 : unitInterval) : E1) = bL)
    (hpR0 : (pR (0 : unitInterval) : E1) = aR)
    (hpR1 : (pR (1 : unitInterval) : E1) = bR)
    (hp20 : (p2 (0 : unitInterval) : E2) = a2)
    (hp21 : (p2 (1 : unitInterval) : E2) = b2)
    {f0 : E0 → X} {f1 : E1 → X} {f2 : E2 → X}
    (hf0 : PolyhedralPLInCharts e f0 S0) (hf1 : PolyhedralPLInCharts e f1 S1)
    (hf2 : PolyhedralPLInCharts e f2 S2)
    (hagreeL : ∀ t : I01, f0 (p0 t) = f1 (pL t))
    (hagreeR : ∀ t : I01, f1 (pR t) = f2 (p2 t)) :
    ∃ (B0 : Set E0) (B1 : Set E1) (V D : Set P2) (B2 : Set E2)
      (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (q : I01 ≃ₜ V)
      (m : (TR ∪ TL : Set P2) ≃ₜ TR) (m2 : S2 ≃ₜ TL) (g : P2 → X),
      IsFinitePLBallPair ℝ B0 {a0, b0} ∧
      IsFinitePLBallPair ℝ B1 {aL, bL} ∧
      W0 ∪ B0 = Q0 ∧ W0 ∩ B0 = {a0, b0} ∧
      L1 ∪ B1 = Q1 ∧ L1 ∩ B1 = {aL, bL} ∧
      V = (fun x : S1 => (n1 x : P2)) '' (Subtype.val ⁻¹' R1) ∧
      q.IsFinitePL ∧
      (∀ t : I01, (q t : P2) = n1 ⟨pR t, hS1.1 (hR1Q (pR t).property)⟩) ∧
      IsFinitePLBallPair ℝ D
        {(q (0 : unitInterval) : P2), (q (1 : unitInterval) : P2)} ∧
      IsFinitePLBallPair ℝ B2 {a2, b2} ∧
      V ∪ D = (fun x : S0 => (n0 x : P2)) '' (Subtype.val ⁻¹' B0) ∪
        (fun x : S1 => (n1 x : P2)) '' (Subtype.val ⁻¹' B1) ∧
      V ∩ D = {(q (0 : unitInterval) : P2), (q (1 : unitInterval) : P2)} ∧
      W2 ∪ B2 = Q2 ∧ W2 ∩ B2 = {a2, b2} ∧
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ m.IsFinitePL ∧ m2.IsFinitePL ∧
      (∀ t : I01,
        (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) =
          n1 ⟨pL t, hS1.1 (hL1Q (pL t).property)⟩) ∧
      (∀ (t : I01) (z : (TR ∪ TL : Set P2)), (z : P2) = q t →
        (m z : P2) = m2 ⟨p2 t, hS2.1 (hW2Q (p2 t).property)⟩) ∧
      (∀ (x : S0) (y : S1), (n0 x : P2) = n1 y ↔
        ∃ t : I01, (x : E0) = p0 t ∧ (y : E1) = pL t) ∧
      (∀ (z : (TR ∪ TL : Set P2)) (y : S2), (m z : P2) = m2 y ↔
        ∃ t : I01, (z : P2) = q t ∧ (y : E2) = p2 t) ∧
      (∀ (x : S0) (y : S2),
        (m ⟨n0 x, Or.inl (n0 x).property⟩ : P2) ≠ m2 y) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S0, g (m ⟨n0 x, Or.inl (n0 x).property⟩) = f0 x) ∧
      (∀ x : S1, g (m ⟨n1 x, Or.inr (n1 x).property⟩) = f1 x) ∧
      (∀ x : S2, g (m2 x) = f2 x) ∧
      g '' (TR ∪ TL) = (f0 '' S0 ∪ f1 '' S1) ∪ f2 '' S2 ∧
      IsFinitePLBallPair P2 (TR ∪ TL)
        ((fun x : (TR ∪ TL : Set P2) => (m x : P2)) '' (Subtype.val ⁻¹' D) ∪
         (fun x : S2 => (m2 x : P2)) '' (Subtype.val ⁻¹' B2)) ∧
      ∀ Z : Set X, (TR ∪ TL) ∩ g ⁻¹' Z =
        ((fun x : S0 => (m ⟨n0 x, Or.inl (n0 x).property⟩ : P2)) ''
          {x : S0 | f0 x ∈ Z} ∪
         (fun x : S1 => (m ⟨n1 x, Or.inr (n1 x).property⟩ : P2)) ''
          {x : S1 | f1 x ∈ Z}) ∪
        (fun x : S2 => (m2 x : P2)) '' {x : S2 | f2 x ∈ Z} := by
  obtain ⟨B0, B1, n0, n1, p, g01, hB0, hB1, hW0B, hL1B, hW0Bi, hL1Bi,
      hn0, hn1, _, _, _, hnp0, hnp1, hg01, hkeep0, hkeep1, him01, hball01, hpre01⟩ :=
    exists_prescribed_interval_disk_map e hcompat hS0 hS1 hW0 hL1 hW0Q hL1Q
      hab0 habL p0 pL hp0 hpL hp00 hp01 hpL0 hpL1 hf0 hf1 hagreeL
  let Q01 := (fun x : S0 => (n0 x : P2)) '' (Subtype.val ⁻¹' B0) ∪
    (fun x : S1 => (n1 x : P2)) '' (Subtype.val ⁻¹' B1)
  have hR1B : R1 ⊆ B1 := by
    intro x hx
    have hxQ : x ∈ L1 ∪ B1 := hL1B.symm.subset (hR1Q hx)
    exact hxQ.resolve_left (fun hxL => Set.disjoint_left.mp hdisj hxL hx)
  obtain ⟨V, q, hV, hq, hqval, hVeq⟩ :=
    exists_interval_image_parameter n1 hn1 hR1 (hR1Q.trans hS1.1) pR hpR hpR0 hpR1
  have hVQ : V ⊆ Q01 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hVeq.subset hy
    exact Or.inr ⟨x, hR1B hx, rfl⟩
  have hends : (q (0 : unitInterval) : P2) ≠ (q (1 : unitInterval) : P2) := by
    intro h
    have h01 := congrArg (fun t : unitInterval => (t : ℝ)) (q.injective (Subtype.ext h))
    norm_num at h01
  have hagree (t : I01) : g01 (q t) = f2 (p2 t) := by
    rw [hqval]
    exact (hkeep1 ⟨pR t, hS1.1 (hR1Q (pR t).property)⟩).trans (hagreeR t)
  obtain ⟨D, B2, m, m2, r, g, hD, hB2, hVD, hW2B, hVDi, hW2Bi,
      hm, hm2, _, _, _, hmr, hm2r, hg, hkeep01, hkeep2, him, hball, hpre⟩ :=
    exists_prescribed_interval_disk_map e hcompat hball01 hS2 hV hW2 hVQ hW2Q
      hends hab2 q p2 hq hp2 rfl rfl hp20 hp21 hg01 hf2 hagree
  have hfinal0 (x : S0) : g (m ⟨n0 x, Or.inl (n0 x).property⟩) = f0 x :=
    (hkeep01 ⟨n0 x, Or.inl (n0 x).property⟩).trans (hkeep0 x)
  have hfinal1 (x : S1) : g (m ⟨n1 x, Or.inr (n1 x).property⟩) = f1 x :=
    (hkeep01 ⟨n1 x, Or.inr (n1 x).property⟩).trans (hkeep1 x)
  refine ⟨B0, B1, V, D, B2, n0, n1, q, m, m2, g,
    hB0, hB1, hW0B, hW0Bi, hL1B, hL1Bi, hVeq, hq, hqval,
    hD, hB2, hVD, hVDi, hW2B, hW2Bi, hn0, hn1, hm, hm2,
    fun t => (hnp0 t).trans (hnp1 t).symm, ?_, ?_, ?_, ?_,
    hg, hfinal0, hfinal1, hkeep2,
    ?_, hball, ?_⟩
  · intro t z hz
    have hzeq : z = ⟨q t, hball01.1 (hVQ (q t).property)⟩ := Subtype.ext hz
    rw [hzeq]
    exact (hmr t).trans (hm2r t).symm
  · exact prescribed_interval_source_eq_iff (hW0Q.trans hS0.1)
      (hL1Q.trans hS1.1) n0 n1 p0 pL p hnp0 hnp1
  · exact prescribed_interval_source_eq_iff (hVQ.trans hball01.1)
      (hW2Q.trans hS2.1) m m2 q p2 r hmr hm2r
  · intro x y hxy
    obtain ⟨t, ht, _⟩ :=
      (prescribed_interval_source_eq_iff (hVQ.trans hball01.1)
        (hW2Q.trans hS2.1) m m2 q p2 r hmr hm2r _ y).mp hxy
    obtain ⟨s, _, hs⟩ :=
      (prescribed_interval_source_eq_iff (hW0Q.trans hS0.1)
        (hL1Q.trans hS1.1) n0 n1 p0 pL p hnp0 hnp1 x
        ⟨pR t, hS1.1 (hR1Q (pR t).property)⟩).mp (ht.trans (hqval t))
    exact Set.disjoint_left.mp hdisj (hs.symm ▸ (pL s).property) (pR t).property
  · rwa [him01] at him
  · intro Z
    ext y
    constructor
    · intro hy
      rcases (hpre Z).subset hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · rcases (hpre01 Z).subset ⟨x.property, hx⟩ with
          ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
        · refine Or.inl (Or.inl ⟨z, hz, ?_⟩)
          exact congrArg (fun w : (TR ∪ TL : Set P2) => (m w : P2)) (Subtype.ext hzx)
        · refine Or.inl (Or.inr ⟨z, hz, ?_⟩)
          exact congrArg (fun w : (TR ∪ TL : Set P2) => (m w : P2)) (Subtype.ext hzx)
      · exact Or.inr ⟨x, hx, rfl⟩
    · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
      · refine ⟨Or.inl (m ⟨n0 x, Or.inl (n0 x).property⟩).property, ?_⟩
        change g (m ⟨n0 x, Or.inl (n0 x).property⟩) ∈ Z
        rw [hfinal0]
        exact hx
      · refine ⟨Or.inl (m ⟨n1 x, Or.inr (n1 x).property⟩).property, ?_⟩
        change g (m ⟨n1 x, Or.inr (n1 x).property⟩) ∈ Z
        rw [hfinal1]
        exact hx
      · refine ⟨Or.inr (m2 x).property, ?_⟩
        change g (m2 x) ∈ Z
        rw [hkeep2]
        exact hx

end PoincareConjecture.M76.Dehn
