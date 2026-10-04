import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Concrete.ArcBandChain

/-! Exact original lower endpoints of the bands in a concrete chain.
Source: MT Claim 19.40, pp. 470-471; three-arc cap/patch seed derivation,
Section 6. -/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT.M64IntrinsicArcBandChain

/-- The actual endpoint edge starts at the original arc's subdivision point. Source: MT
Claim 19.40; three-arc cap/patch seed, Section 6. Source:
`proof-work/tasks/M64/derivations/2026-09-27-three-arc-cap-patch-seed.md`, Section 6. -/
theorem endpoint_zero {gamma : ℝ → AnnulusCoordinates} {a b : ℝ}
    {U : Set AnnulusCoordinates} (C : M64IntrinsicArcBandChain gamma a b U)
    (i : Fin C.count) (right : Bool) :
    ((C.band i).endpointEdge right).map 0 =
      gamma (C.cut (if right then i.succ else i.castSucc)) := by
  have hstep : C.cut i.castSucc ≤ C.cut i.succ :=
    (C.cut_strictMono (Fin.castSucc_lt_succ (i := i))).le
  have hlower : gamma (C.cut (if right then i.succ else i.castSucc)) ∈
      (C.band i).lowerArc := by
    rw [C.lower_arc]
    refine ⟨C.cut (if right then i.succ else i.castSucc), ?_, rfl⟩
    cases right
    · exact ⟨le_rfl, hstep⟩
    · exact ⟨hstep, le_rfl⟩
  have hcut : gamma (C.cut (if right then i.succ else i.castSucc)) ∈
      (if right then (C.band i).rightCut else (C.band i).leftCut) := by
    cases right
    · change gamma (C.cut i.castSucc) ∈ (C.band i).leftCut
      rw [C.left_cut]
      exact left_mem_segment ℝ _ _
    · change gamma (C.cut i.succ) ∈ (C.band i).rightCut
      rw [C.right_cut]
      exact left_mem_segment ℝ _ _
  rw [← (C.band i).endpointEdge_image right] at hcut
  obtain ⟨t, ht, he⟩ := hcut
  have ht0 := (m64Intrinsic_band_endpoint_mem_lower_iff (C.band i) right ht).mp
    (he.symm ▸ hlower)
  simpa only [ht0] using he

end PoincareMT.M64IntrinsicArcBandChain
