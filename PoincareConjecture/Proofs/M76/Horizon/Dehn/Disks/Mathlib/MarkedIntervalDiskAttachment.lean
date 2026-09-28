import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.PrescribedAttachmentRim

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)

private theorem complement_eq_of_union_inter {E : Type*} {W B U Q P : Set E}
    (hWB : W ∪ B = Q) (hWiB : W ∩ B = P)
    (hQ : Q = U ∪ W) (hWiU : W ∩ U = P) : B = U := by
  ext x
  have h1 := congrArg (fun A : Set E ↦ x ∈ A) hWB
  have h2 := congrArg (fun A : Set E ↦ x ∈ A) hWiB
  have h3 := congrArg (fun A : Set E ↦ x ∈ A) hQ
  have h4 := congrArg (fun A : Set E ↦ x ∈ A) hWiU
  simp only [mem_union, mem_inter_iff] at h1 h2 h3 h4
  tauto

theorem marked_attachment_rim_eq
    {E0 E1 Y X : Type*} {S0 Q0 W0 B0 P0 : Set E0} {S1 Q1 W1 B1 V1 P1 : Set E1}
    {f0 : E0 → X} {f1 : E1 → X} {g : Y → X} {T : Set Y} {Z : Set X}
    (j0 : S0 → Y) (j1 : S1 → Y)
    (hW0S : W0 ⊆ S0) (hW1S : W1 ⊆ S1)
    (hWB0 : W0 ∪ B0 = Q0) (hWB1 : W1 ∪ B1 = Q1)
    (hi0 : W0 ∩ B0 = P0) (hi1 : W1 ∩ B1 = P1)
    (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hQ1 : Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ V1) ∪ W1)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = P0) (hmark1 : W1 ∩ f1 ⁻¹' Z = P1)
    (hdisj : W1 ∩ V1 = ∅)
    (hpre : T ∩ g ⁻¹' Z = j0 '' {x : S0 | f0 x ∈ Z} ∪
      j1 '' {x : S1 | f1 x ∈ Z}) :
    j0 '' (Subtype.val ⁻¹' B0) ∪ j1 '' (Subtype.val ⁻¹' B1) =
      (T ∩ g ⁻¹' Z) ∪ j1 '' (Subtype.val ⁻¹' V1) := by
  have hWi0 : W0 ∩ (S0 ∩ f0 ⁻¹' Z) = P0 := by
    rw [← hmark0]
    ext x
    simp only [mem_inter_iff]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hW0S h.1, h.2⟩⟩
  have hWi1 : W1 ∩ ((S1 ∩ f1 ⁻¹' Z) ∪ V1) = P1 := by
    rw [inter_union_distrib_left, hdisj, union_empty, ← hmark1]
    ext x
    simp only [mem_inter_iff]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hW1S h.1, h.2⟩⟩
  rw [complement_eq_of_union_inter hWB0 hi0 hQ0 hWi0,
    complement_eq_of_union_inter hWB1 hi1 hQ1 hWi1, hpre, preimage_union, image_union]
  have h0 : (Subtype.val ⁻¹' (S0 ∩ f0 ⁻¹' Z) : Set S0) =
      {x : S0 | f0 x ∈ Z} := by ext x; simp
  have h1 : (Subtype.val ⁻¹' (S1 ∩ f1 ⁻¹' Z) : Set S1) =
      {x : S1 | f1 x ∈ Z} := by ext x; simp
  rw [h0, h1, union_assoc]

section Attachment

variable {E0 E1 F X ι : Type*}
  [NormedAddCommGroup E0] [NormedSpace ℝ E0] [FiniteDimensional ℝ E0]
  [NormedAddCommGroup E1] [NormedSpace ℝ E1] [FiniteDimensional ℝ E1]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
  (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
  {S0 Q0 W0 : Set E0} {S1 Q1 W1 : Set E1} {a0 b0 : E0} {a1 b1 : E1}
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
  (Z : Set X)
  (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
  (hmark0 : W0 ∩ f0 ⁻¹' Z = {a0, b0})
  (hmark1 : W1 ∩ f1 ⁻¹' Z = {a1, b1})

include hcompat hS0 hS1 hW0 hW1 hW0Q hW1Q hab0 hab1 hp0 hp1 hp00 hp01
  hp10 hp11 hf0 hf1 hagree hQ0 hmark0 hmark1

private theorem exists_marked_attachment
    {V1 : Set E1} (hQ1 : Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ V1) ∪ W1)
    (hdisj : W1 ∩ V1 = ∅) :
    ∃ (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (p : I01 ≃ₜ TE) (g : P2 → X),
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ p.IsFinitePL ∧
      (p i0 : P2) = (0, 1) ∧ (p i1 : P2) = (0, 0) ∧
      (∀ t : I01, (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) = p t) ∧
      (∀ t : I01, (n1 ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩ : P2) = p t) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S0, g (n0 x) = f0 x) ∧ (∀ x : S1, g (n1 x) = f1 x) ∧
      g '' (TR ∪ TL) = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ U : Set X, (TR ∪ TL) ∩ g ⁻¹' U =
        (fun x : S0 ↦ (n0 x : P2)) '' {x : S0 | f0 x ∈ U} ∪
        (fun x : S1 ↦ (n1 x : P2)) '' {x : S1 | f1 x ∈ U}) ∧
      IsFinitePLBallPair P2 (TR ∪ TL) (((TR ∪ TL) ∩ g ⁻¹' Z) ∪
        (fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' V1)) := by
  obtain ⟨B0, B1, n0, n1, p, g, hB0, hB1, hWB0, hWB1, hi0, hi1,
    hn0, hn1, hp, hpzero, hpone, hn0p, hn1p, hg, hg0, hg1, hgimage, hball, hpre⟩ :=
    exists_prescribed_interval_disk_map e hcompat hS0 hS1 hW0 hW1 hW0Q hW1Q
      hab0 hab1 p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree
  have hrim := marked_attachment_rim_eq (fun x : S0 ↦ (n0 x : P2))
    (fun x : S1 ↦ (n1 x : P2)) (hW0Q.trans hS0.1) (hW1Q.trans hS1.1)
    hWB0 hWB1 hi0 hi1 hQ0 hQ1 hmark0 hmark1 hdisj (hpre Z)
  exact ⟨n0, n1, p, g, hn0, hn1, hp, hpzero, hpone, hn0p, hn1p,
    hg, hg0, hg1, hgimage, hpre, hrim ▸ hball⟩

theorem exists_marked_interval_disk_map
    {V1 : Set E1} {c1 d1 : E1}
    (hV1 : IsFinitePLBallPair ℝ V1 {c1, d1}) (hV1Q : V1 ⊆ Q1)
    (hdisj : W1 ∩ V1 = ∅) (pV : I01 ≃ₜ V1) (hpV : pV.IsFinitePL)
    (hpV0 : (pV i0 : E1) = c1) (hpV1 : (pV i1 : E1) = d1)
    (hQ1 : Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ V1) ∪ W1)
    (hmarkV : V1 ∩ f1 ⁻¹' Z = {c1, d1}) :
    ∃ (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (p : I01 ≃ₜ TE) (g : P2 → X)
      (V : Set P2) (q : I01 ≃ₜ V),
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ p.IsFinitePL ∧
      (p i0 : P2) = (0, 1) ∧ (p i1 : P2) = (0, 0) ∧
      (∀ t : I01, (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) = p t) ∧
      (∀ t : I01, (n1 ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩ : P2) = p t) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S0, g (n0 x) = f0 x) ∧ (∀ x : S1, g (n1 x) = f1 x) ∧
      g '' (TR ∪ TL) = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ U : Set X, (TR ∪ TL) ∩ g ⁻¹' U =
        (fun x : S0 ↦ (n0 x : P2)) '' {x : S0 | f0 x ∈ U} ∪
        (fun x : S1 ↦ (n1 x : P2)) '' {x : S1 | f1 x ∈ U}) ∧
      IsFinitePLBallPair P2 (TR ∪ TL) (((TR ∪ TL) ∩ g ⁻¹' Z) ∪ V) ∧
      V = (fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' V1) ∧
      IsFinitePLBallPair ℝ V {(q i0 : P2), (q i1 : P2)} ∧ q.IsFinitePL ∧
      (∀ t : I01, (q t : P2) = n1 ⟨pV t, hS1.1 (hV1Q (pV t).property)⟩) ∧
      V ∩ g ⁻¹' Z = {(q i0 : P2), (q i1 : P2)} := by
  obtain ⟨n0, n1, p, g, hn0, hn1, hp, hpzero, hpone, hn0p, hn1p,
    hg, hg0, hg1, hgimage, hpre, hball⟩ :=
    exists_marked_attachment e hcompat hS0 hS1 hW0 hW1 hW0Q hW1Q hab0 hab1
      p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree Z hQ0 hmark0 hmark1 hQ1 hdisj
  let V := (fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' V1)
  obtain ⟨q, hq, hqval⟩ :=
    exists_prescribed_interval_image_chart n1 hn1 hV1 (hV1Q.trans hS1.1) pV hpV
  have hVball : IsFinitePLBallPair ℝ V {(q i0 : P2), (q i1 : P2)} := by
    apply (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).of_homeomorph
      (by intro x hx; rcases hx with rfl | hx; exact (q i0).property
          simpa only [mem_singleton_iff.mp hx] using (q i1).property) q.symm hq.symm
    intro x
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (hx | hx)
      · left
        have heq : x = q i0 := Subtype.ext hx
        simp [heq]
      · right
        have heq : x = q i1 := Subtype.ext hx
        simp [heq]
    · rintro (hx | hx)
      · left
        have heq : q.symm x = i0 := Subtype.ext hx
        exact congrArg Subtype.val ((q.apply_symm_apply x).symm.trans (congrArg q heq))
      · right
        have heq : q.symm x = i1 := Subtype.ext hx
        exact congrArg Subtype.val ((q.apply_symm_apply x).symm.trans (congrArg q heq))
  have hcontact : V ∩ g ⁻¹' Z = {(q i0 : P2), (q i1 : P2)} := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      have hm : (x : E1) ∈ ({c1, d1} : Set E1) := by
        apply hmarkV.subset
        exact ⟨hx, by simpa only [mem_preimage, hg1] using hy⟩
      rcases hm with hx0 | hx1
      · left
        rw [hqval]
        exact congrArg (fun x : S1 ↦ (n1 x : P2)) (Subtype.ext (hx0.trans hpV0.symm))
      · right
        rw [mem_singleton_iff, hqval]
        exact congrArg (fun x : S1 ↦ (n1 x : P2)) (Subtype.ext (hx1.trans hpV1.symm))
    · intro hy
      have hend (t : I01) (ht : (pV t : E1) ∈ ({c1, d1} : Set E1)) :
          (q t : P2) ∈ V ∩ g ⁻¹' Z := by
        refine ⟨(q t).property, ?_⟩
        change g (q t) ∈ Z
        rw [hqval, hg1]
        exact (hmarkV.symm.subset ht).2
      rcases hy with rfl | hy
      · exact hend i0 (by simp [hpV0])
      · rw [mem_singleton_iff] at hy
        subst y
        exact hend i1 (by simp [hpV1])
  exact ⟨n0, n1, p, g, V, q, hn0, hn1, hp, hpzero, hpone, hn0p, hn1p,
    hg, hg0, hg1, hgimage, hpre, hball, rfl, hVball, hq, hqval, hcontact⟩

theorem exists_terminal_marked_interval_disk_map
    (hQ1 : Q1 = (S1 ∩ f1 ⁻¹' Z) ∪ W1) :
    ∃ (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (p : I01 ≃ₜ TE) (g : P2 → X),
      n0.IsFinitePL ∧ n1.IsFinitePL ∧ p.IsFinitePL ∧
      (p i0 : P2) = (0, 1) ∧ (p i1 : P2) = (0, 0) ∧
      (∀ t : I01, (n0 ⟨p0 t, hS0.1 (hW0Q (p0 t).property)⟩ : P2) = p t) ∧
      (∀ t : I01, (n1 ⟨p1 t, hS1.1 (hW1Q (p1 t).property)⟩ : P2) = p t) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S0, g (n0 x) = f0 x) ∧ (∀ x : S1, g (n1 x) = f1 x) ∧
      g '' (TR ∪ TL) = f0 '' S0 ∪ f1 '' S1 ∧
      (∀ U : Set X, (TR ∪ TL) ∩ g ⁻¹' U =
        (fun x : S0 ↦ (n0 x : P2)) '' {x : S0 | f0 x ∈ U} ∪
        (fun x : S1 ↦ (n1 x : P2)) '' {x : S1 | f1 x ∈ U}) ∧
      IsFinitePLBallPair P2 (TR ∪ TL) ((TR ∪ TL) ∩ g ⁻¹' Z) := by
  obtain ⟨n0, n1, p, g, hn0, hn1, hp, hpzero, hpone, hn0p, hn1p,
    hg, hg0, hg1, hgimage, hpre, hball⟩ :=
    exists_marked_attachment e hcompat hS0 hS1 hW0 hW1 hW0Q hW1Q hab0 hab1
      p0 p1 hp0 hp1 hp00 hp01 hp10 hp11 hf0 hf1 hagree Z hQ0 hmark0 hmark1
      (V1 := ∅) (by simpa only [union_empty] using hQ1) (by simp)
  exact ⟨n0, n1, p, g, hn0, hn1, hp, hpzero, hpone, hn0p, hn1p,
    hg, hg0, hg1, hgimage, hpre, by simpa only [preimage_empty, image_empty, union_empty]
      using hball⟩

end Attachment

end PoincareConjecture.M76.Dehn
