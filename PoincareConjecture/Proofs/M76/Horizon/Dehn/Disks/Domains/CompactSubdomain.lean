import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCoreCutoffs
import PoincareConjecture.Proofs.M76.Mathlib.RelativePLSuperlevelFrontier

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_compact_subdomain_near
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R A W : Set X}
    (hR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ R)
    (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ K V : Set X, IsCompact K ∧ PLDomain e K ∧ A ⊆ K ∧ K ⊆ R ∩ W ∧
      IsOpen V ∧ A ⊆ V ∧ V ⊆ W ∧ K ∩ V = R ∩ V ∧
      frontier K ∩ V = frontier R ∩ V ∧
      (Subtype.val : R → X) ⁻¹' A ⊆ interior ((Subtype.val : R → X) ⁻¹' K) := by
  let := ChartedSpace.ofChartCover e hR.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  obtain ⟨w, C, O, hC, hCW, hO, hAO, hw, _, hone, hzero, hwPL⟩ :=
    OpenPartialHomeomorph.exists_compactly_supported_PL_core_cutoff
      e hR.compatible hR.cover hA hW hAW
  obtain ⟨t, ht, _, hK, hlevel, hcorner⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_relative_regular_level
      e hR.compatible hR.cover hw hwPL hC hzero hR.closed hR.halfspace
      (a := (1 / 3 : ℝ)) (b := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
  have ht0 : 0 < t := lt_trans (by norm_num) ht.1
  have ht1 : t < 1 := lt_trans ht.2 (by norm_num)
  let K : Set X := {x | x ∈ R ∧ t ≤ w x}
  let V : Set X := O ∩ W
  have hV : IsOpen V := hO.inter hW
  have hAV : A ⊆ V := fun x hx => ⟨hAO hx, hAW hx⟩
  have hKV : K ∩ V = R ∩ V := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, (hone hx.2.1).symm ▸ ht1.le⟩, hx.2⟩
  have hKhalf := OpenPartialHomeomorph.relative_superlevel_frontier_charts
    e hw hR.closed hR.halfspace hlevel (fun x hx hxt => by
      obtain ⟨psi, ell, u, v, B, hpu, _, _, hxB, hpx, _, hB, hhalf, _, _⟩ :=
        hcorner x hx hxt
      exact ⟨psi, u, B, hpu, hxB, hpx, hB, hhalf⟩)
  refine ⟨K, V, hK, ⟨hR.cover, hR.compatible, hK.isClosed, hKhalf⟩,
    ?_, ?_, hV, hAV, inter_subset_right, hKV, ?_, ?_⟩
  · intro x hx
    exact ⟨hAR hx, (hone (hAO hx)).symm ▸ ht1.le⟩
  · intro x hx
    refine ⟨hx.1, hCW ?_⟩
    by_contra hxC
    have hxw : t ≤ w x := hx.2
    rw [hzero x hxC] at hxw
    exact (not_le_of_gt ht0) hxw
  · calc
      frontier K ∩ V = frontier (K ∩ V) ∩ V := (frontier_inter_open_inter hV).symm
      _ = frontier (R ∩ V) ∩ V := congrArg (fun S => frontier S ∩ V) hKV
      _ = frontier R ∩ V := frontier_inter_open_inter hV
  · have hpre : (Subtype.val : R → X) ⁻¹' V ⊆ (Subtype.val : R → X) ⁻¹' K := by
      intro x hx
      exact ((hKV.symm ▸ (show (x : X) ∈ R ∩ V from ⟨x.property, hx⟩))).1
    intro x hx
    exact interior_maximal hpre (hV.preimage continuous_subtype_val) (hAV hx)

end PoincareConjecture.M76
