import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ResidualSupport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ProperArcPairConfinement

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_confined_returning_disk_avoiding_lower_complex
    {W B U : Set V} {a b : V} (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0)
    (hup : ∀ x ∈ W, 0 ≤ x.2) (haxis : W ∩ {x : V | x.2 = 0} = {a, b})
    (hB : IsFinitePLBallPair V B (segment ℝ a b ∪ W))
    (hU : IsOpen U) (hBU : B ⊆ U)
    (T : SimplicialComplex ℝ V) (hT : T.faces.Finite)
    (hlower : ∀ x ∈ T.space, x.2 ≤ 0)
    (hTaxis : ∀ x ∈ T.space, x.2 = 0 → x = a ∨ x = b) :
    ∃ D : Set V, IsCompact D ∧ IsFinitePLBallPair V D (frontier D) ∧
      D ⊆ U ∧ B ⊆ D ∧ a ∈ frontier D ∧ b ∈ frontier D ∧
      W ⊆ D ∧ segment ℝ a b ⊆ D ∧
      W \ {a, b} ⊆ interior D ∧ segment ℝ a b \ {a, b} ⊆ interior D ∧
      D ∩ {x : V | x.2 = 0} = segment ℝ a b ∧ D ∩ T.space ⊆ {a, b} := by
  have hab' : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
  have hw : IsFinitePLBallPair ℝ (segment ℝ a b) {a, b} := by
    have hh := isFinitePLBallPair_affine_interval zero_lt_one
      (ContinuousAffineMap.lineMap a b) (AffineMap.lineMap_injective ℝ hab').injOn
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using hh
  obtain ⟨D₀, _, _, hD₀, ha₀, hb₀, _, _, hWint, hwint, hD₀axis, havoid⟩ :=
    exists_returning_disk_avoiding_lower_complex hW hab ha hb hup haxis T hT hlower hTaxis
  have hmeet : segment ℝ a b ∩ W = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxW⟩
      have hx0 := (PlanarSegment.mem_segment_iff hab.ne).mp hx
      have hxz : x.2 = 0 := by simpa [PlanarSegment.height, ha, hb] using hx0.2
      exact haxis.subset ⟨hxW, hxz⟩
    · exact subset_inter hw.1 hW.1
  obtain ⟨F, hF, hFi, hFmap, hFfix, hBD₀⟩ := exists_proper_arc_pair_compression
    hD₀ hB hw hW hab' ha₀ hb₀
    (hwint.trans (hD₀.interior_eq_sdiff_of_finrank_eq rfl).subset)
    (hWint.trans (hD₀.interior_eq_sdiff_of_finrank_eq rfl).subset) hmeet hU hBU
  have himage := hD₀.image hF hFi
  have hfront := himage.frontier_eq_of_finrank_eq rfl
  have hWB : W ⊆ B := subset_union_right.trans hB.1
  have hwB : segment ℝ a b ⊆ B := subset_union_left.trans hB.1
  have hBD : B ⊆ F '' D₀ := by
    intro x hx
    exact ⟨x, hBD₀ hx, hFfix hx⟩
  have hDsub : F '' D₀ ⊆ D₀ ∩ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hFmap hy
  refine ⟨F '' D₀, himage.isCompact, hfront.symm ▸ himage,
    hDsub.trans inter_subset_right, hBD, ?_, ?_, hWB.trans hBD, hwB.trans hBD,
    ?_, ?_, ?_, ?_⟩
  · rw [hfront]
    exact ⟨a, ha₀, hFfix (hwB (left_mem_segment ℝ a b))⟩
  · rw [hfront]
    exact ⟨b, hb₀, hFfix (hwB (right_mem_segment ℝ a b))⟩
  · intro x hx
    have hh := hF.mem_interior_image rfl hFi (hWint hx)
    rwa [hFfix (hWB hx.1)] at hh
  · intro x hx
    have hh := hF.mem_interior_image rfl hFi (hwint hx)
    rwa [hFfix (hwB hx.1)] at hh
  · apply Subset.antisymm
    · exact fun x hx => hD₀axis.subset ⟨(hDsub hx.1).1, hx.2⟩
    · intro x hx
      exact ⟨hBD (hwB hx), (hD₀axis.symm.subset hx).2⟩
  · exact fun x hx => havoid ⟨(hDsub hx.1).1, hx.2⟩

theorem exists_returning_disk_avoiding_endpoint_and_distant_residual
    {W B U E : Set V} {a b : V} (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0)
    (hup : ∀ x ∈ W, 0 ≤ x.2) (haxis : W ∩ {x : V | x.2 = 0} = {a, b})
    (hB : IsFinitePLBallPair V B (segment ℝ a b ∪ W))
    (hU : IsOpen U) (hBU : B ⊆ U) (hE : IsClosed E) (hBE : Disjoint B E)
    (T : SimplicialComplex ℝ V) (hT : T.faces.Finite)
    (hlower : ∀ x ∈ T.space, x.2 ≤ 0)
    (hTaxis : ∀ x ∈ T.space, x.2 = 0 → x = a ∨ x = b) :
    ∃ D : Set V, IsCompact D ∧ IsFinitePLBallPair V D (frontier D) ∧
      D ⊆ U ∧ B ⊆ D ∧ a ∈ frontier D ∧ b ∈ frontier D ∧
      W ⊆ D ∧ segment ℝ a b ⊆ D ∧
      W \ {a, b} ⊆ interior D ∧ segment ℝ a b \ {a, b} ⊆ interior D ∧
      D ∩ {x : V | x.2 = 0} = segment ℝ a b ∧
      D ∩ T.space ⊆ {a, b} ∧ Disjoint D E := by
  have hBO : B ⊆ U ∩ Eᶜ := fun x hx =>
    ⟨hBU hx, fun hxE => disjoint_left.mp hBE hx hxE⟩
  obtain ⟨D, hD, hball, hDU, hBD, haD, hbD, hWD, hwD, hWi, hwi, haxisD, havoid⟩ :=
    exists_confined_returning_disk_avoiding_lower_complex hW hab ha hb hup haxis
      hB (hU.inter hE.isOpen_compl) hBO T hT hlower hTaxis
  exact ⟨D, hD, hball, hDU.trans inter_subset_left, hBD, haD, hbD, hWD, hwD,
    hWi, hwi, haxisD, havoid, disjoint_left.mpr (fun x hx hxE => (hDU hx).2 hxE)⟩

end PoincareConjecture.M76.Dehn
