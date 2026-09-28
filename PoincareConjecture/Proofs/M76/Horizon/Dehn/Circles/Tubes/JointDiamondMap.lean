import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.JointQuarterMaps

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.SignedJointCross

local notation "P2" => (ℝ × ℝ)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (J : SignedJointCross E)

theorem exists_diamond_map :
    ∃ H : signedTubeDiamond ≃ₜ J.disk, H.IsFinitePL ∧
      (∀ b c (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter b c ↔ (H x : E) ∈ J.quarter b c) ∧
      (∀ j (x : signedTubeDiamond), (x : P2) ∈ signedTubeSheet j ↔ (H x : E) ∈ J.axis j) ∧
      (H ⟨(0, 0), mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨false, signedTube_center_mem⟩⟩⟩ : E) =
        J.center ∧
      ∀ j b, (H ⟨signedTubeCorner j b,
        signedTubeRadius_subset_diamond j b (right_mem_segment ℝ _ _)⟩ : E) = J.endpoint j b := by
  classical
  obtain ⟨er, f, her, hf, herCenter, herEnd, hkeep0, hkeep1⟩ := J.exists_quarter_maps
  have hSrc0 (b c : Bool) : signedTubeRadius 0 c ⊆ signedTubeQuarter b c :=
    fun _ hx => (signedTube_quarter_ball b c).1 (Or.inr (Or.inl hx))
  have hSrc1 (b c : Bool) : signedTubeRadius 1 b ⊆ signedTubeQuarter b c :=
    fun _ hx => (signedTube_quarter_ball b c).1 (Or.inr (Or.inr hx))
  have hTgt0 (b c : Bool) : J.radius 0 c ⊆ J.quarter b c :=
    fun _ hx => (J.quarter_ball b c).1 (Or.inr (Or.inl hx))
  have hTgt1 (b c : Bool) : J.radius 1 b ⊆ J.quarter b c :=
    fun _ hx => (J.quarter_ball b c).1 (Or.inr (Or.inr hx))
  have hRad0 (b c : Bool) (x : signedTubeQuarter b c) :
      (x : P2) ∈ signedTubeRadius 0 c ↔ (f b c x : E) ∈ J.radius 0 c :=
    (f b c).mem_subset_iff_of_extension (er 0 c) (hSrc0 b c) (hTgt0 b c)
      (fun z => Subtype.ext (hkeep0 b c z)) x
  have hRad1 (b c : Bool) (x : signedTubeQuarter b c) :
      (x : P2) ∈ signedTubeRadius 1 b ↔ (f b c x : E) ∈ J.radius 1 b :=
    (f b c).mem_subset_iff_of_extension (er 1 b) (hSrc1 b c) (hTgt1 b c)
      (fun z => Subtype.ext (hkeep1 b c z)) x
  have hZero (b c : Bool) : (0, 0) ∈ signedTubeQuarter b c :=
    hSrc0 b c (left_mem_segment ℝ _ _)
  have hCenter (b c : Bool) : (f b c ⟨(0, 0), hZero b c⟩ : E) = J.center :=
    (hkeep0 b c ⟨(0, 0), left_mem_segment ℝ _ _⟩).trans
      ((herCenter 0 c ⟨(0, 0), left_mem_segment ℝ _ _⟩).mpr rfl)
  have hCenterIff (b c : Bool) (x : signedTubeQuarter b c) :
      (x : P2) = (0, 0) ↔ (f b c x : E) = J.center := by
    constructor
    · intro hx
      exact (congrArg (fun z : signedTubeQuarter b c => (f b c z : E))
        (show x = ⟨(0, 0), hZero b c⟩ from Subtype.ext hx)).trans (hCenter b c)
    · intro hx
      exact congrArg Subtype.val ((f b c).injective (Subtype.ext (hx.trans (hCenter b c).symm)))
  have hoverlap (u v : Bool × Bool) (x : signedTubeQuarter u.1 u.2) :
      (x : P2) ∈ signedTubeQuarter v.1 v.2 ↔ (f u.1 u.2 x : E) ∈ J.quarter v.1 v.2 := by
    rcases u with ⟨b, c⟩
    rcases v with ⟨b', c'⟩
    dsimp only at x ⊢
    by_cases hb : b = b'
    · subst b'
      by_cases hc : c = c'
      · subst c'
        exact iff_of_true x.property (f b c x).property
      · have hn : c' = !c := Bool.eq_not_of_ne (Ne.symm hc)
        subst c'
        have hs : (x : P2) ∈ signedTubeQuarter b (!c) ↔ (x : P2) ∈ signedTubeRadius 1 b := by
          rw [← signedTube_quarter_inter_delta b c]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f b c x : E) ∈ J.quarter b (!c) ↔ (f b c x : E) ∈ J.radius 1 b := by
          rw [← (J.quarter_intersections b c).1]
          simp only [mem_inter_iff, (f b c x).property, true_and]
        exact hs.trans ((hRad1 b c x).trans ht.symm)
    · have hn : b' = !b := Bool.eq_not_of_ne (Ne.symm hb)
      subst b'
      by_cases hc : c = c'
      · subst c'
        have hs : (x : P2) ∈ signedTubeQuarter (!b) c ↔ (x : P2) ∈ signedTubeRadius 0 c := by
          rw [← signedTube_quarter_inter_eps b c]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f b c x : E) ∈ J.quarter (!b) c ↔ (f b c x : E) ∈ J.radius 0 c := by
          rw [← (J.quarter_intersections b c).2.1]
          simp only [mem_inter_iff, (f b c x).property, true_and]
        exact hs.trans ((hRad0 b c x).trans ht.symm)
      · have hn : c' = !c := Bool.eq_not_of_ne (Ne.symm hc)
        subst c'
        have hs : (x : P2) ∈ signedTubeQuarter (!b) (!c) ↔ (x : P2) = (0, 0) := by
          rw [← mem_singleton_iff, ← signedTube_quarter_inter_opposite b c]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f b c x : E) ∈ J.quarter (!b) (!c) ↔ (f b c x : E) = J.center := by
          rw [← mem_singleton_iff, ← (J.quarter_intersections b c).2.2]
          simp only [mem_inter_iff, (f b c x).property, true_and]
        exact hs.trans ((hCenterIff b c x).trans ht.symm)
  have hagree (u v : Bool × Bool) (x : P2)
      (hx : x ∈ signedTubeQuarter u.1 u.2) (hy : x ∈ signedTubeQuarter v.1 v.2) :
      (f u.1 u.2 ⟨x, hx⟩ : E) = f v.1 v.2 ⟨x, hy⟩ := by
    rcases u with ⟨b, c⟩
    rcases v with ⟨b', c'⟩
    dsimp only at hx hy ⊢
    by_cases hb : b = b'
    · subst b'
      by_cases hc : c = c'
      · subst c'
        rfl
      · have hn : c' = !c := Bool.eq_not_of_ne (Ne.symm hc)
        subst c'
        have hr : x ∈ signedTubeRadius 1 b := (signedTube_quarter_inter_delta b c).subset ⟨hx, hy⟩
        exact (hkeep1 b c ⟨x, hr⟩).trans (hkeep1 b (!c) ⟨x, hr⟩).symm
    · have hn : b' = !b := Bool.eq_not_of_ne (Ne.symm hb)
      subst b'
      by_cases hc : c = c'
      · subst c'
        have hr : x ∈ signedTubeRadius 0 c := (signedTube_quarter_inter_eps b c).subset ⟨hx, hy⟩
        exact (hkeep0 b c ⟨x, hr⟩).trans (hkeep0 (!b) c ⟨x, hr⟩).symm
      · have hn : c' = !c := Bool.eq_not_of_ne (Ne.symm hc)
        subst c'
        have hz : x = (0, 0) := (signedTube_quarter_inter_opposite b c).subset ⟨hx, hy⟩
        exact ((hCenterIff b c ⟨x, hx⟩).mp hz).trans
          ((hCenterIff (!b) (!c) ⟨x, hy⟩).mp hz).symm
  obtain ⟨G, hG, hGkeep⟩ := Homeomorph.exists_iUnion_finitePL
    (fun u : Bool × Bool => signedTubeQuarter u.1 u.2)
    (fun u : Bool × Bool => J.quarter u.1 u.2)
    (fun u => f u.1 u.2) (fun u => hf u.1 u.2) hoverlap hagree
  have hSource : (⋃ u : Bool × Bool, signedTubeQuarter u.1 u.2) = signedTubeDiamond := by
    ext x
    simp only [signedTubeDiamond, mem_iUnion, Prod.exists]
  have hTarget : (⋃ u : Bool × Bool, J.quarter u.1 u.2) = J.disk := by
    calc
      (⋃ u : Bool × Bool, J.quarter u.1 u.2) = ⋃ b, ⋃ c, J.quarter b c := by
        ext x
        simp only [mem_iUnion, Prod.exists]
      _ = J.disk := J.quarter_union
  let H : signedTubeDiamond ≃ₜ J.disk :=
    (Homeomorph.setCongr hSource.symm).trans (G.trans (Homeomorph.setCongr hTarget))
  have hH : H.IsFinitePL := hG.setCongr hSource hTarget
  have hKeep (b c : Bool) (x : signedTubeQuarter b c) :
      (H ⟨x, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨c, x.property⟩⟩⟩ : E) = f b c x := hGkeep (b, c) x
  have hRadius (j : Fin 2) (b : Bool) (x : signedTubeRadius j b) :
      (H ⟨x, signedTubeRadius_subset_diamond j b x.property⟩ : E) = er j b x := by
    fin_cases j
    · exact (hKeep false b ⟨x, hSrc0 false b x.property⟩).trans (hkeep0 false b x)
    · exact (hKeep b false ⟨x, hSrc1 b false x.property⟩).trans (hkeep1 b false x)
  have hRadIff (j : Fin 2) (b : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeRadius j b ↔ (H x : E) ∈ J.radius j b :=
    H.mem_subset_iff_of_extension (er j b) (signedTubeRadius_subset_diamond j b)
      (fun _ hz => (J.radius_subset_axis j b hz).1) (fun z => Subtype.ext (hRadius j b z)) x
  refine ⟨H, hH, ?_, ?_, ?_, ?_⟩
  · intro b c x
    exact H.mem_subset_iff_of_extension (f b c)
      (fun _ hz => mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨c, hz⟩⟩)
      (fun _ hz => hz.1) (fun z => Subtype.ext (hKeep b c z)) x
  · intro j x
    change (x : P2) ∈ signedTubeRadius j false ∪ signedTubeRadius j true ↔ (H x : E) ∈ J.axis j
    rw [show J.axis j = J.radius j false ∪ J.radius j true from J.axis_radii j]
    exact or_congr (hRadIff j false x) (hRadIff j true x)
  · exact (hKeep false false ⟨(0, 0), signedTube_center_mem⟩).trans (hCenter false false)
  · intro j b
    exact (hRadius j b ⟨signedTubeCorner j b, right_mem_segment ℝ _ _⟩).trans
      ((herEnd j b ⟨signedTubeCorner j b, right_mem_segment ℝ _ _⟩).mpr rfl)

end PoincareConjecture.M76.Dehn.SignedJointCross
