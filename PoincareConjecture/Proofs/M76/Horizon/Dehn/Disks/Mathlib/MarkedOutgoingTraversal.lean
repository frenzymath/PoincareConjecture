import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MarkedIntervalDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MarkedAttachmentTraversal










set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)




theorem exists_marked_outgoing_traversal_with_sources
    {E0 E1 F X ι : Type*}
    [NormedAddCommGroup E0] [NormedSpace ℝ E0] [FiniteDimensional ℝ E0]
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S0 Q0 W0 : Set E0} {S1 Q1 W1 V1 : Set E1}
    {a0 b0 : E0} {a1 b1 c1 d1 : E1}
    (hS0 : IsFinitePLBallPair P2 S0 Q0) (hS1 : IsFinitePLBallPair P2 S1 Q1)
    (hW0 : IsFinitePLBallPair ℝ W0 {a0, b0}) (hW1 : IsFinitePLBallPair ℝ W1 {a1, b1})
    (hW0Q : W0 ⊆ Q0) (hW1Q : W1 ⊆ Q1) (hab0 : a0 ≠ b0) (hab1 : a1 ≠ b1)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1)
    (hp0 : p0.IsFinitePL) (hp1 : p1.IsFinitePL)
    (hp00 : (p0 i0 : E0) = a0) (hp01 : (p0 i1 : E0) = b0)
    (hp10 : (p1 i0 : E1) = a1) (hp11 : (p1 i1 : E1) = b1)
    {f0 : E0 → X} {f1 : E1 → X}
    (hf0 : PolyhedralPLInCharts e f0 S0) (hf1 : PolyhedralPLInCharts e f1 S1)
    (hagree : ∀ t : I01, f0 (p0 t) = f1 (p1 t))
    (Z : Set X) (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = {a0, b0})
    (hmark1 : W1 ∩ f1 ⁻¹' Z = {a1, b1})
    (hV1 : IsFinitePLBallPair ℝ V1 {c1, d1}) (hV1Q : V1 ⊆ Q1)
    (hdisj : W1 ∩ V1 = ∅) (pV : I01 ≃ₜ V1) (hpV : pV.IsFinitePL)
    (hpV0 : (pV i0 : E1) = c1) (hpV1 : (pV i1 : E1) = d1)
    (hQ1 : Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ V1) ∪ W1)
    (hmarkV : V1 ∩ f1 ⁻¹' Z = {c1, d1})
    (s t : I01) (α : Path c1 (p1 s : E1)) (β : Path (p0 s : E0) (p0 t : E0))
    (γ : Path (p1 t : E1) d1)
    (hαS : ∀ r : I01, α r ∈ S1) (hβS : ∀ r : I01, β r ∈ S0)
    (hγS : ∀ r : I01, γ r ∈ S1)
    (hαZ : ∀ r : I01, f1 (α r) ∈ Z) (hβZ : ∀ r : I01, f0 (β r) ∈ Z)
    (hγZ : ∀ r : I01, f1 (γ r) ∈ Z)
    {x0 x1 x2 x3 : Z} (A : Path x0 x1) (B : Path x1 x2) (C : Path x2 x3)
    (hA : ∀ r : I01, (A r : X) = f1 (α r))
    (hB : ∀ r : I01, (B r : X) = f0 (β r))
    (hC : ∀ r : I01, (C r : X) = f1 (γ r)) :
    ∃ (g : P2 → X) (V : Set P2) (q : I01 ≃ₜ V)
      (P : Path (q i0 : P2) (q i1 : P2)),
      PolyhedralPLInCharts e g T ∧ g '' T = f0 '' S0 ∪ f1 '' S1 ∧
      IsFinitePLBallPair P2 T ((T ∩ g ⁻¹' Z) ∪ V) ∧
      IsFinitePLBallPair ℝ V {(q i0 : P2), (q i1 : P2)} ∧ q.IsFinitePL ∧
      (q i0 : P2) ≠ q i1 ∧ V ∩ g ⁻¹' Z = {(q i0 : P2), (q i1 : P2)} ∧
      (∀ r : I01, g (q r) = f1 (pV r)) ∧
      (∀ r : I01, P r ∈ T) ∧ (∀ r : I01, g (P r) ∈ Z) ∧
      (∀ r : I01, (((A.trans B).trans C) r : X) = g (P r)) ∧
      ∃ (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (p : I01 ≃ₜ TE),
        n0.IsFinitePL ∧ n1.IsFinitePL ∧ p.IsFinitePL ∧
        (∀ r : I01, (n0 ⟨p0 r, hS0.1 (hW0Q (p0 r).property)⟩ : P2) = p r) ∧
        (∀ r : I01, (n1 ⟨p1 r, hS1.1 (hW1Q (p1 r).property)⟩ : P2) = p r) ∧
        Topology.IsEmbedding (fun x : S0 ↦ (n0 x : P2)) ∧
        Topology.IsEmbedding (fun x : S1 ↦ (n1 x : P2)) ∧
        range (fun x : S0 ↦ (n0 x : P2)) ∪ range (fun x : S1 ↦ (n1 x : P2)) = T ∧
        (∀ x : S0, g (n0 x) = f0 x) ∧ (∀ x : S1, g (n1 x) = f1 x) ∧
        (∀ (x : S0) (y : S1), (n0 x : P2) = n1 y ↔
          ∃! r : I01, (x : E0) = p0 r ∧ (y : E1) = p1 r) ∧
        (∀ U : Set X, T ∩ g ⁻¹' U =
          (fun x : S0 ↦ (n0 x : P2)) '' {x : S0 | f0 x ∈ U} ∪
          (fun x : S1 ↦ (n1 x : P2)) '' {x : S1 | f1 x ∈ U}) ∧
        V = (fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' V1) ∧
        ∀ r : I01, (q r : P2) = n1 ⟨pV r, hS1.1 (hV1Q (pV r).property)⟩ := by
  obtain ⟨n0, n1, p, g, V, q, hn0, hn1, hp, _, _, hn0p, hn1p,
    hg, hg0, hg1, himage, hpre, hball, hVeq, hV, hq, hqval, hcontact⟩ :=
    exists_marked_interval_disk_map e hcompat hS0 hS1 hW0 hW1 hW0Q hW1Q hab0 hab1
      p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree Z hQ0 hmark0 hmark1
      hV1 hV1Q hdisj pV hpV hpV0 hpV1 hQ1 hmarkV
  let a0' : S0 := ⟨p0 s, hS0.1 (hW0Q (p0 s).property)⟩
  let b0' : S0 := ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩
  let a1' : S1 := ⟨p1 s, hS1.1 (hW1Q (p1 s).property)⟩
  let b1' : S1 := ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩
  let u : S1 := ⟨c1, hS1.1 (hV1Q (hV1.1 (Or.inl rfl)))⟩
  let v : S1 := ⟨d1, hS1.1 (hV1Q (hV1.1 (Or.inr rfl)))⟩
  let αS : Path u a1' :=
    { toFun r := ⟨α r, hαS r⟩
      continuous_toFun := α.continuous.subtype_mk _
      source' := Subtype.ext α.source
      target' := Subtype.ext α.target }
  let βS : Path a0' b0' :=
    { toFun r := ⟨β r, hβS r⟩
      continuous_toFun := β.continuous.subtype_mk _
      source' := Subtype.ext β.source
      target' := Subtype.ext β.target }
  let γS : Path b1' v :=
    { toFun r := ⟨γ r, hγS r⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have hq0 : (q i0 : P2) = n1 u := by
    rw [hqval]
    exact congrArg (fun x : S1 ↦ (n1 x : P2)) (Subtype.ext hpV0)
  have hq1 : (q i1 : P2) = n1 v := by
    rw [hqval]
    exact congrArg (fun x : S1 ↦ (n1 x : P2)) (Subtype.ext hpV1)
  have hends : (q i0 : P2) ≠ q i1 := by
    intro heq
    have h01 := congrArg (fun r : I01 ↦ (r : ℝ)) (q.injective (Subtype.ext heq))
    norm_num at h01
  have hV' : IsFinitePLBallPair ℝ V {(n1 u : P2), (n1 v : P2)} := by
    simpa only [hq0, hq1] using hV
  have hends' : (n1 u : P2) ≠ n1 v := by simpa only [hq0, hq1] using hends
  have hcontact' : V ∩ g ⁻¹' Z = {(n1 u : P2), (n1 v : P2)} := by
    simpa only [hq0, hq1] using hcontact
  obtain ⟨_, uB, aB, bB, vB, αB, βB, γB, P, hu, _, _, hv,
    hαlift, hβlift, hγlift, hP, _, _, _, _, _⟩ :=
    exists_marked_attachment_traversal n0 n1 hg.continuousOn hg0 hg1
      ((hn1p s).trans (hn0p s).symm) ((hn0p t).trans (hn1p t).symm)
      αS βS γS hαZ hβZ hγZ hball hV' hends' hcontact'
  let P' := (P.map continuous_subtype_val).cast (hq0.trans hu.symm) (hq1.trans hv.symm)
  refine ⟨g, V, q, P', hg, himage, hball, hV, hq, hends, hcontact,
    ?_, fun r ↦ (P r).property.1, fun r ↦ (P r).property.2, ?_,
    n0, n1, p, hn0, hn1, hp, hn0p, hn1p,
    Topology.IsEmbedding.subtypeVal.comp n0.isEmbedding,
    Topology.IsEmbedding.subtypeVal.comp n1.isEmbedding,
    ?_, hg0, hg1, ?_, hpre, hVeq, hqval⟩
  · intro r
    rw [hqval, hg1]
  · intro r
    change (((A.trans B).trans C) r : X) = g (P r)
    rw [hP]
    simp only [Path.trans_apply]
    split_ifs
    · rw [hαlift, hg1]
      exact hA _
    · rw [hβlift, hg0]
      exact hB _
    · rw [hγlift, hg1]
      exact hC _
  · ext y
    constructor
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact Or.inl (n0 x).property
      · exact Or.inr (n1 x).property
    · rintro (hy | hy)
      · exact Or.inl ⟨n0.symm ⟨y, hy⟩, congrArg Subtype.val (n0.apply_symm_apply ⟨y, hy⟩)⟩
      · exact Or.inr ⟨n1.symm ⟨y, hy⟩, congrArg Subtype.val (n1.apply_symm_apply ⟨y, hy⟩)⟩
  · intro x y
    constructor
    · exact prescribed_interval_source_existsUnique (hW0Q.trans hS0.1) (hW1Q.trans hS1.1)
        n0 n1 p0 p1 p hn0p hn1p x y
    · rintro ⟨r, hr, _⟩
      exact (prescribed_interval_source_eq_iff (hW0Q.trans hS0.1) (hW1Q.trans hS1.1)
        n0 n1 p0 p1 p hn0p hn1p x y).mpr ⟨r, hr⟩




theorem exists_marked_outgoing_traversal
    {E0 E1 F X ι : Type*}
    [NormedAddCommGroup E0] [NormedSpace ℝ E0] [FiniteDimensional ℝ E0]
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S0 Q0 W0 : Set E0} {S1 Q1 W1 V1 : Set E1}
    {a0 b0 : E0} {a1 b1 c1 d1 : E1}
    (hS0 : IsFinitePLBallPair P2 S0 Q0) (hS1 : IsFinitePLBallPair P2 S1 Q1)
    (hW0 : IsFinitePLBallPair ℝ W0 {a0, b0}) (hW1 : IsFinitePLBallPair ℝ W1 {a1, b1})
    (hW0Q : W0 ⊆ Q0) (hW1Q : W1 ⊆ Q1) (hab0 : a0 ≠ b0) (hab1 : a1 ≠ b1)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1)
    (hp0 : p0.IsFinitePL) (hp1 : p1.IsFinitePL)
    (hp00 : (p0 i0 : E0) = a0) (hp01 : (p0 i1 : E0) = b0)
    (hp10 : (p1 i0 : E1) = a1) (hp11 : (p1 i1 : E1) = b1)
    {f0 : E0 → X} {f1 : E1 → X}
    (hf0 : PolyhedralPLInCharts e f0 S0) (hf1 : PolyhedralPLInCharts e f1 S1)
    (hagree : ∀ t : I01, f0 (p0 t) = f1 (p1 t))
    (Z : Set X) (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = {a0, b0})
    (hmark1 : W1 ∩ f1 ⁻¹' Z = {a1, b1})
    (hV1 : IsFinitePLBallPair ℝ V1 {c1, d1}) (hV1Q : V1 ⊆ Q1)
    (hdisj : W1 ∩ V1 = ∅) (pV : I01 ≃ₜ V1) (hpV : pV.IsFinitePL)
    (hpV0 : (pV i0 : E1) = c1) (hpV1 : (pV i1 : E1) = d1)
    (hQ1 : Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ V1) ∪ W1)
    (hmarkV : V1 ∩ f1 ⁻¹' Z = {c1, d1})
    (s t : I01) (α : Path c1 (p1 s : E1)) (β : Path (p0 s : E0) (p0 t : E0))
    (γ : Path (p1 t : E1) d1)
    (hαS : ∀ r : I01, α r ∈ S1) (hβS : ∀ r : I01, β r ∈ S0)
    (hγS : ∀ r : I01, γ r ∈ S1)
    (hαZ : ∀ r : I01, f1 (α r) ∈ Z) (hβZ : ∀ r : I01, f0 (β r) ∈ Z)
    (hγZ : ∀ r : I01, f1 (γ r) ∈ Z)
    {x0 x1 x2 x3 : Z} (A : Path x0 x1) (B : Path x1 x2) (C : Path x2 x3)
    (hA : ∀ r : I01, (A r : X) = f1 (α r))
    (hB : ∀ r : I01, (B r : X) = f0 (β r))
    (hC : ∀ r : I01, (C r : X) = f1 (γ r)) :
    ∃ (g : P2 → X) (V : Set P2) (q : I01 ≃ₜ V)
      (P : Path (q i0 : P2) (q i1 : P2)),
      PolyhedralPLInCharts e g T ∧ g '' T = f0 '' S0 ∪ f1 '' S1 ∧
      IsFinitePLBallPair P2 T ((T ∩ g ⁻¹' Z) ∪ V) ∧
      IsFinitePLBallPair ℝ V {(q i0 : P2), (q i1 : P2)} ∧ q.IsFinitePL ∧
      (q i0 : P2) ≠ q i1 ∧ V ∩ g ⁻¹' Z = {(q i0 : P2), (q i1 : P2)} ∧
      (∀ r : I01, g (q r) = f1 (pV r)) ∧
      (∀ r : I01, P r ∈ T) ∧ (∀ r : I01, g (P r) ∈ Z) ∧
      ∀ r : I01, (((A.trans B).trans C) r : X) = g (P r)  := by
  obtain ⟨g, V, q, P, hg, himage, hball, hV, hq, hends, hcontact,
    hqmap, hPS, hPZ, hPval, _⟩ :=
    exists_marked_outgoing_traversal_with_sources e hcompat hS0 hS1 hW0 hW1 hW0Q hW1Q
      hab0 hab1 p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree Z hQ0 hmark0 hmark1
      hV1 hV1Q hdisj pV hpV hpV0 hpV1 hQ1 hmarkV s t α β γ hαS hβS hγS hαZ hβZ hγZ
      A B C hA hB hC
  exact ⟨g, V, q, P, hg, himage, hball, hV, hq, hends, hcontact, hqmap, hPS, hPZ, hPval⟩

end PoincareConjecture.M76.Dehn
