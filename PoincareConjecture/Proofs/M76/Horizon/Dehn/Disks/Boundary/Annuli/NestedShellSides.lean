import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedShellArc
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem disk_frontier_meets_disk_interior {A ar S sr : Set P2}
    (hA : IsFinitePLBallPair P2 A ar) (hS : IsFinitePLBallPair P2 S sr)
    (hmeet : (A ∩ interior S).Nonempty) (hoff : (A \ S).Nonempty) :
    (interior A ∩ sr).Nonempty := by
  have hmeet' : (interior A ∩ interior S).Nonempty := by
    apply (closure_inter_open_nonempty_iff isOpen_interior).mp
    rwa [hA.closure_interior_of_finrank_eq rfl]
  by_contra hnot
  have hdis : Disjoint (frontier (interior S)) (interior A) := by
    rw [hS.frontier_interior_of_finrank_eq rfl]
    apply Set.disjoint_left.mpr
    exact fun z hzS hzA ↦ hnot ⟨z, hzA, hzS⟩
  have hsub := (hA.isConnected_interior_of_finrank_eq rfl).isPreconnected
    |>.m76_subset_of_disjoint_frontier isOpen_interior hdis hmeet'
  have hclosed := closure_mono hsub
  rw [hA.closure_interior_of_finrank_eq rfl, hS.closure_interior_of_finrank_eq rfl] at hclosed
  obtain ⟨z, hz, hno⟩ := hoff
  exact hno (hclosed hz)

theorem disk_cut_separating_scalar {T A B W : Set P2}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hcover : A ∪ B = T) (hinter : A ∩ B = W) :
    ∃ f : P2 → ℝ, Continuous f ∧
      (∀ z ∈ T, f z ≤ 0 ↔ z ∈ A) ∧
      (∀ z ∈ T, 0 ≤ f z ↔ z ∈ B) ∧
      T ∩ {z | f z = 0} = W ∧
      (∀ z ∈ A \ W, f z < 0) ∧ (∀ z ∈ B \ W, 0 < f z) := by
  let f : P2 → ℝ := fun z ↦ infDist z A - infDist z B
  have hc : Continuous f := (continuous_infDist_pt A).sub (continuous_infDist_pt B)
  have hneg (z : P2) (hz : z ∈ A \ W) : f z < 0 := by
    have hno : z ∉ B := fun h ↦ hz.2 (hinter.subset ⟨hz.1, h⟩)
    have hp := (hB.isClosed.notMem_iff_infDist_pos hneB).mp hno
    dsimp [f]
    rw [infDist_zero_of_mem hz.1]
    linarith
  have hpos (z : P2) (hz : z ∈ B \ W) : 0 < f z := by
    have hno : z ∉ A := fun h ↦ hz.2 (hinter.subset ⟨h, hz.1⟩)
    have hp := (hA.isClosed.notMem_iff_infDist_pos hneA).mp hno
    dsimp [f]
    rw [infDist_zero_of_mem hz.1, sub_zero]
    exact hp
  have hleft (z : P2) (hz : z ∈ T) : f z ≤ 0 ↔ z ∈ A := by
    constructor
    · intro hf
      rcases hcover.symm.subset hz with ha | hb
      · exact ha
      · by_contra hno
        exact (not_lt_of_ge hf) (hpos z ⟨hb, fun hw ↦ hno (hinter.symm.subset hw).1⟩)
    · intro ha
      dsimp [f]
      rw [infDist_zero_of_mem ha]
      exact sub_nonpos.mpr infDist_nonneg
  have hright (z : P2) (hz : z ∈ T) : 0 ≤ f z ↔ z ∈ B := by
    constructor
    · intro hf
      rcases hcover.symm.subset hz with ha | hb
      · by_contra hno
        exact (not_lt_of_ge hf) (hneg z ⟨ha, fun hw ↦ hno (hinter.symm.subset hw).2⟩)
      · exact hb
    · intro hb
      dsimp [f]
      rw [infDist_zero_of_mem hb, sub_zero]
      exact infDist_nonneg
  refine ⟨f, hc, hleft, hright, ?_, hneg, hpos⟩
  ext z
  constructor
  · rintro ⟨hz, hf⟩
    exact hinter.subset ⟨(hleft z hz).mp hf.le, (hright z hz).mp hf.ge⟩
  · intro hz
    have hh := hinter.symm.subset hz
    refine ⟨hcover.subset (Or.inl hh.1), ?_⟩
    exact le_antisymm ((hleft _ (hcover.subset (Or.inl hh.1))).mpr hh.1)
      ((hright _ (hcover.subset (Or.inl hh.1))).mpr hh.2)

theorem exists_nested_disk_cut_halves {S sq T tq W Z : Set P2} {a b x y : P2}
    (hS : IsFinitePLBallPair P2 S sq) (hT : IsFinitePLBallPair P2 T tq)
    (hST : S ⊆ T \ tq) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hZ : IsFinitePLBallPair ℝ Z {x, y}) (hab : a ≠ b) (hxy : x ≠ y)
    (ha : a ∈ sq) (hb : b ∈ sq) (hx : x ∈ tq) (hy : y ∈ tq)
    (hWproper : W \ {a, b} ⊆ S \ sq) (hZproper : Z \ {x, y} ⊆ T \ tq)
    (hWS : W ⊆ S) (hZS : Z ∩ S = W) :
    ∃ A B U V u v : Set P2,
      IsFinitePLBallPair P2 A (U ∪ Z) ∧ IsFinitePLBallPair P2 B (Z ∪ V) ∧
      A ∪ B = T ∧ A ∩ B = Z ∧ A ∩ tq = U ∧ B ∩ tq = V ∧
      IsFinitePLBallPair ℝ U {x, y} ∧ IsFinitePLBallPair ℝ V {x, y} ∧
      U ∪ V = tq ∧ U ∩ V = {x, y} ∧
      IsFinitePLBallPair ℝ u {a, b} ∧ IsFinitePLBallPair ℝ v {a, b} ∧
      u ∪ v = sq ∧ u ∩ v = {a, b} ∧
      u = sq ∩ A ∧ v = sq ∩ B ∧
      IsFinitePLBallPair P2 (S ∩ A) (W ∪ u) ∧
      IsFinitePLBallPair P2 (S ∩ B) (W ∪ v) ∧
      u \ {a, b} ⊆ A \ (U ∪ Z) ∧ v \ {a, b} ⊆ B \ (Z ∪ V) := by
  obtain ⟨U, V, hU, hV, hUV, hIV⟩ := hT.exists_boundary_arcs hx hy hxy
  obtain ⟨A, B, hA, hB, hcover, hinter, hAU, hBV⟩ :=
    hT.exists_proper_arc_cut hU hV hZ hxy hIV.subset hUV hZproper
  have hAT : A ⊆ T := subset_union_left.trans hcover.subset
  have hBT : B ⊆ T := subset_union_right.trans hcover.subset
  have hZA : Z ⊆ A := fun z hz ↦ (hinter.symm.subset hz).1
  have hZB : Z ⊆ B := fun z hz ↦ (hinter.symm.subset hz).2
  have hWZ : W ⊆ Z := fun z hz ↦ (hZS.symm.subset hz).1
  have hWsq : W ∩ sq = {a, b} := by
    apply Subset.antisymm
    · intro z hz
      by_contra hn
      exact (hWproper ⟨hz.1, hn⟩).2 hz.2
    · rintro z (rfl | rfl)
      · exact ⟨hW.1 (Or.inl rfl), ha⟩
      · exact ⟨hW.1 (Or.inr rfl), hb⟩
  obtain ⟨f, hf, hleft, hright, hzero, hneg, hpos⟩ :=
    disk_cut_separating_scalar hA.isCompact hB.isCompact
      (hA.isConnected_sdiff.nonempty.mono sdiff_subset)
      (hB.isConnected_sdiff.nonempty.mono sdiff_subset) hcover hinter
  have hsZero : S ∩ {z | f z = 0} = W := by
    ext z
    constructor
    · intro hz
      exact hZS.subset ⟨hzero.subset ⟨(hST hz.1).1, hz.2⟩, hz.1⟩
    · intro hz
      exact ⟨hWS hz, (hzero.symm.subset (hWZ hz)).2⟩
  have hsqZero : sq ∩ {z | f z = 0} = {a, b} := by
    ext z
    constructor
    · intro hz
      exact hWsq.subset ⟨hsZero.subset ⟨hS.1 hz.1, hz.2⟩, hz.1⟩
    · intro hz
      exact ⟨(hWsq.symm.subset hz).2, (hsZero.symm.subset (hW.1 hz)).2⟩
  obtain ⟨p, hpW, hpends⟩ := hW.isConnected_sdiff.nonempty
  have hpS : p ∈ interior S := by
    rw [hS.interior_eq_sdiff_of_finrank_eq rfl]
    exact hWproper ⟨hpW, hpends⟩
  have hxZ : x ∈ Z := hZ.1 (Or.inl rfl)
  have hxS : x ∉ S := fun hh ↦ (hST hh).2 hx
  obtain ⟨z, hzA, hzsq⟩ := disk_frontier_meets_disk_interior hA hS
    ⟨p, hZA (hWZ hpW), hpS⟩ ⟨x, hZA hxZ, hxS⟩
  have hnegative : ∃ z ∈ sq, f z < 0 := by
    refine ⟨z, hzsq, hneg z ⟨interior_subset hzA, ?_⟩⟩
    intro hzZ
    have hh := hzA
    rw [hA.interior_eq_sdiff_of_finrank_eq rfl] at hh
    exact hh.2 (Or.inr hzZ)
  obtain ⟨z, hzB, hzsq⟩ := disk_frontier_meets_disk_interior hB hS
    ⟨p, hZB (hWZ hpW), hpS⟩ ⟨x, hZB hxZ, hxS⟩
  have hpositive : ∃ z ∈ sq, 0 < f z := by
    refine ⟨z, hzsq, hpos z ⟨interior_subset hzB, ?_⟩⟩
    intro hzZ
    have hh := hzB
    rw [hB.interior_eq_sdiff_of_finrank_eq rfl] at hh
    exact hh.2 (Or.inl hzZ)
  obtain ⟨q₀, q₁, hq₀, hq₁, hqcover, _⟩ := hS.exists_boundary_arcs ha hb hab
  obtain ⟨hu, hv⟩ := isFinitePLBallPair_signed_halves_of_arcs hq₀ hq₁ hqcover f
    hf.continuousOn hsqZero hnegative hpositive
  obtain ⟨hminus, hplus⟩ := hS.isFinitePLBallPair_signed_halves_of_zero_arc f hf.continuousOn
    hW hab hsZero hsqZero hu hv hnegative hpositive
  let u := sq ∩ {z | f z ≤ 0}
  let v := sq ∩ {z | 0 ≤ f z}
  have hminusEq : S ∩ {z | f z ≤ 0} = S ∩ A := by
    ext z
    exact and_congr_right (fun hz ↦ hleft z (hST hz).1)
  have hplusEq : S ∩ {z | 0 ≤ f z} = S ∩ B := by
    ext z
    exact and_congr_right (fun hz ↦ hright z (hST hz).1)
  have hM : IsFinitePLBallPair P2 (S ∩ A) (W ∪ u) := by
    simpa only [hminusEq, union_comm] using hminus
  have hP : IsFinitePLBallPair P2 (S ∩ B) (W ∪ v) := by
    simpa only [hplusEq] using hplus
  refine ⟨A, B, U, V, u, v, hA, hB, hcover, hinter, hAU, hBV,
    hU, hV, hUV, hIV, hu, hv, ?_, ?_, ?_, ?_, hM, hP, ?_, ?_⟩
  · ext z
    change (z ∈ sq ∧ f z ≤ 0) ∨ (z ∈ sq ∧ 0 ≤ f z) ↔ z ∈ sq
    constructor
    · exact fun hh ↦ hh.elim And.left And.left
    · intro hz
      exact (le_total (f z) 0).elim (fun hh ↦ Or.inl ⟨hz, hh⟩) (fun hh ↦ Or.inr ⟨hz, hh⟩)
  · ext z
    change (z ∈ sq ∧ f z ≤ 0) ∧ (z ∈ sq ∧ 0 ≤ f z) ↔ z ∈ ({a, b} : Set P2)
    constructor
    · intro hz
      exact hsqZero.subset ⟨hz.1.1, le_antisymm hz.1.2 hz.2.2⟩
    · intro hz
      have hh := hsqZero.symm.subset hz
      exact ⟨⟨hh.1, hh.2.le⟩, hh.1, hh.2.ge⟩
  · ext z
    exact and_congr_right (fun hz ↦ hleft z (hST (hS.1 hz)).1)
  · ext z
    exact and_congr_right (fun hz ↦ hright z (hST (hS.1 hz)).1)
  · rintro z ⟨hz, hnot⟩
    refine ⟨(hleft z (hST (hS.1 hz.1)).1).mp hz.2, ?_⟩
    rintro (hzU | hzZ)
    · exact (hST (hS.1 hz.1)).2 (hUV.subset (Or.inl hzU))
    · exact hnot (hsqZero.subset ⟨hz.1, (hzero.symm.subset hzZ).2⟩)
  · rintro z ⟨hz, hnot⟩
    refine ⟨(hright z (hST (hS.1 hz.1)).1).mp hz.2, ?_⟩
    rintro (hzZ | hzV)
    · exact hnot (hsqZero.subset ⟨hz.1, (hzero.symm.subset hzZ).2⟩)
    · exact (hST (hS.1 hz.1)).2 (hUV.subset (Or.inr hzV))

end PoincareConjecture.M76.Dehn
