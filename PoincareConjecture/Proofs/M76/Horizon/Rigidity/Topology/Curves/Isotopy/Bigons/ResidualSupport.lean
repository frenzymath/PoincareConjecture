import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ResidualWedges
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDomination

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_returning_disk_avoiding_lower_complex
    {W : Set V} {a b : V} (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0)
    (hup : ∀ x ∈ W, 0 ≤ x.2) (haxis : W ∩ {x : V | x.2 = 0} = {a, b})
    (T : SimplicialComplex ℝ V) (hT : T.faces.Finite)
    (hlower : ∀ x ∈ T.space, x.2 ≤ 0)
    (hTaxis : ∀ x ∈ T.space, x.2 = 0 → x = a ∨ x = b) :
    ∃ D : Set V, IsCompact D ∧ Convex ℝ D ∧ IsFinitePLBallPair V D (frontier D) ∧
      a ∈ frontier D ∧ b ∈ frontier D ∧ W ⊆ D ∧ segment ℝ a b ⊆ D ∧
      W \ {a, b} ⊆ interior D ∧ segment ℝ a b \ {a, b} ⊆ interior D ∧
      D ∩ {x : V | x.2 = 0} = segment ℝ a b ∧ D ∩ T.space ⊆ {a, b} := by
  classical
  obtain ⟨D₀, hcompact, hconvex, hD₀, ha₀, hb₀, hWD₀, hwD₀, hWint, hwint, hD₀axis⟩ :=
    exists_convex_proper_arc_pair_disk hW hab ha hb hup haxis
  obtain ⟨C₀, _, havoid⟩ := exists_lower_residual_wedge_bound T hT hab ha hb hlower hTaxis
  have hWcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hWcopy
  let L : ContinuousAffineMap ℝ V ℝ := ContinuousAffineMap.const ℝ V a.1 -
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let R : ContinuousAffineMap ℝ V ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap -
    ContinuousAffineMap.const ℝ V b.1
  let Y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hL : FinitePiecewiseAffineOn L W := hKs ▸ (K.affineOnFaces_affine L).finitePiecewiseAffineOn hK
  have hR : FinitePiecewiseAffineOn R W := hKs ▸ (K.affineOnFaces_affine R).finitePiecewiseAffineOn hK
  have hY : FinitePiecewiseAffineOn Y W := hKs ▸ (K.affineOnFaces_affine Y).finitePiecewiseAffineOn hK
  have hzero (x : V) (hx : x ∈ W) (hy : Y x = 0) : L x ≤ 0 ∧ R x ≤ 0 := by
    have he : x = a ∨ x = b := by simpa using haxis.subset ⟨hx, hy⟩
    change a.1 - x.1 ≤ 0 ∧ x.1 - b.1 ≤ 0
    rcases he with he | he <;> rw [he] <;> constructor <;> linarith
  obtain ⟨CL, _, hCL⟩ := hL.exists_le_pos_mul hY hup (fun x hx hz => (hzero x hx hz).1)
  obtain ⟨CR, _, hCR⟩ := hR.exists_le_pos_mul hY hup (fun x hx hz => (hzero x hx hz).2)
  let C := max C₀ (max CL CR) + 1
  have hC₀ : C₀ ≤ C := by dsimp [C]; linarith [le_max_left C₀ (max CL CR)]
  have hCLt : CL < C := by dsimp [C]; linarith [le_max_right C₀ (max CL CR), le_max_left CL CR]
  have hCRt : CR < C := by dsimp [C]; linarith [le_max_right C₀ (max CL CR), le_max_right CL CR]
  let A : V →ᵃ[ℝ] ℝ := L.toAffineMap - C • Y.toAffineMap
  let B : V →ᵃ[ℝ] ℝ := R.toAffineMap - C • Y.toAffineMap
  let U : Set V := {x | A x ≤ 0 ∧ B x ≤ 0}
  let D := D₀ ∩ U
  have hUclosed : IsClosed U :=
    (isClosed_le A.continuous_of_finiteDimensional continuous_const).inter
      (isClosed_le B.continuous_of_finiteDimensional continuous_const)
  have hUconvex : Convex ℝ U := ((convex_Iic (0 : ℝ)).affine_preimage A).inter
    ((convex_Iic (0 : ℝ)).affine_preimage B)
  have hstrict {x : V} (hAx : A x < 0) (hBx : B x < 0) : x ∈ interior U := by
    exact mem_interior.mpr ⟨{y | A y < 0 ∧ B y < 0},
      (fun _ h => ⟨h.1.le, h.2.le⟩),
      ((isOpen_lt A.continuous_of_finiteDimensional continuous_const).inter
        (isOpen_lt B.continuous_of_finiteDimensional continuous_const)), ⟨hAx, hBx⟩⟩
  have hWU : W ⊆ U := by
    intro x hx
    have hl := hCL x hx
    have hr := hCR x hx
    have hy := hup x hx
    change a.1 - x.1 ≤ CL * x.2 at hl
    change x.1 - b.1 ≤ CR * x.2 at hr
    change a.1 - x.1 - C * x.2 ≤ 0 ∧ x.1 - b.1 - C * x.2 ≤ 0
    constructor <;> nlinarith
  have hWUint : W \ {a, b} ⊆ interior U := by
    intro x hx
    have hy : 0 < x.2 := lt_of_le_of_ne (hup x hx.1) (by
      intro hz
      exact hx.2 (haxis.subset ⟨hx.1, hz.symm⟩))
    have hl := hCL x hx.1
    have hr := hCR x hx.1
    change a.1 - x.1 ≤ CL * x.2 at hl
    change x.1 - b.1 ≤ CR * x.2 at hr
    apply hstrict
    · change a.1 - x.1 - C * x.2 < 0
      nlinarith
    · change x.1 - b.1 - C * x.2 < 0
      nlinarith
  have hwU : segment ℝ a b ⊆ U := hUconvex.segment_subset
    (hWU (hW.1 (by simp))) (hWU (hW.1 (by simp)))
  have hwUint : segment ℝ a b \ {a, b} ⊆ interior U := by
    intro x hx
    have hseg := (PlanarSegment.mem_segment_iff hab.ne).mp hx.1
    rw [uIcc_of_le hab.le] at hseg
    have hy : x.2 = 0 := by simpa [PlanarSegment.height, ha, hb] using hseg.2
    have hxa : a.1 < x.1 := lt_of_le_of_ne hseg.1.1 (by
      intro he
      exact hx.2 (by left; exact Prod.ext he.symm (hy.trans ha.symm)))
    have hxb : x.1 < b.1 := lt_of_le_of_ne hseg.1.2 (by
      intro he
      exact hx.2 (by right; exact Prod.ext he (hy.trans hb.symm)))
    apply hstrict
    · change a.1 - x.1 - C * x.2 < 0
      rw [hy, mul_zero]
      linarith
    · change x.1 - b.1 - C * x.2 < 0
      rw [hy, mul_zero]
      linarith
  have hWintD : W \ {a, b} ⊆ interior D := by
    intro x hx
    change x ∈ interior (D₀ ∩ U)
    rw [interior_inter]
    exact ⟨hWint hx, hWUint hx⟩
  have hwintD : segment ℝ a b \ {a, b} ⊆ interior D := by
    intro x hx
    change x ∈ interior (D₀ ∩ U)
    rw [interior_inter]
    exact ⟨hwint hx, hwUint hx⟩
  have hDcopy := hD₀
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hDcopy
  obtain ⟨M, hM, hMs⟩ := J.exists_finite_triangulation_inter_halfspaces hJ {A, B}
  have hMD : M.space = D := by simpa only [Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, hJs] using hMs
  have hDcompact : IsCompact D := hcompact.inter_right hUclosed
  have hDconvex : Convex ℝ D := hconvex.inter hUconvex
  have hDball : IsFinitePLBallPair V D (frontier D) :=
    isFinitePLBallPair_of_compact_convex hDcompact hDconvex
      (hW.sdiff_nonempty.mono hWintD) M hM hMD
  have hWD : W ⊆ D := subset_inter hWD₀ hWU
  have hwD : segment ℝ a b ⊆ D := subset_inter hwD₀ hwU
  have hfront {x : V} (hx : x ∈ frontier D₀) (hxD : x ∈ D) : x ∈ frontier D := by
    rw [frontier, hDcompact.isClosed.closure_eq]
    exact ⟨hxD, fun hi => hx.2 (interior_mono inter_subset_left hi)⟩
  refine ⟨D, hDcompact, hDconvex, hDball,
    hfront ha₀ (hwD (left_mem_segment ℝ a b)),
    hfront hb₀ (hwD (right_mem_segment ℝ a b)), hWD, hwD, hWintD, hwintD, ?_, ?_⟩
  · apply Subset.antisymm
    · exact fun x hx => hD₀axis.subset ⟨hx.1.1, hx.2⟩
    · intro x hx
      exact ⟨hwD hx, (hD₀axis.symm.subset hx).2⟩
  · intro x hx
    apply havoid C hC₀ x hx.2
    have hh := hx.1.2
    change a.1 - x.1 - C * x.2 ≤ 0 ∧ x.1 - b.1 - C * x.2 ≤ 0 at hh
    constructor <;> linarith [hh.1, hh.2]

end PoincareConjecture.M76.Dehn
