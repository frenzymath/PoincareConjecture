import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.SourceAnnuli.OriginalIdentity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.PairedOrientedCollars

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)



theorem ComponentIdentityAnnuliData.exists_oriented_collars
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    {M : SourceCircleDecomposition f S} {i : M.Index} {l d : ℝ}
    (D : ComponentIdentityAnnuliData (e := e) (R := R) M i l d) :
    ∃ (B : ∀ k, OrientedPolygonCollar l d (D.source k))
      (τ : P2 × ℝ → X) (idx : Fin 2 → M.Index),
      PolyhedralPLInCharts e τ (identityTube l d) ∧
      τ '' identityTube l d ⊆ interior R ∧
      (∀ z ∈ identityTube l d, ∀ w ∈ identityTube l d,
        τ z = τ w ↔ z.1 = w.1 ∧
          (z.2 : AddCircle (4 * l)) = (w.2 : AddCircle (4 * l))) ∧
      (∀ k t, t ∈ Icc 0 (4 * l) → ∀ u : Icc (-d) d,
        f ((B k).chart ⟨annulusMap l (by linarith [D.depth_pos, D.width_small])
          ((t : AddCircle (4 * l)), u), annulus_period_point_mem D.depth_pos D.width_small _ u⟩) =
          τ (sourceTubeDiagonal k u, t)) ∧
      S ∩ f ⁻¹' (τ '' identityTube l d) = D.source 0 ∪ D.source 1 ∧
      (∀ k, (fun p : squareAnnulus l d ↦ ((B k).chart p : P2)) ''
        {p | depth l p = 0} = M.pieces (idx k)) ∧
      ∀ k x, x ∈ D.source k → x ∈ doubleLocusOn f S → x ∈ M.pieces (idx k) := by
  classical
  obtain ⟨B, τ, hτ, himage, hfib, hzero, hvalue⟩ :=
    exists_paired_oriented_polygon_collars (ContinuousLinearEquiv.refl ℝ P2) e
      D.depth_pos D.width_small D.source D.chart D.chart_PL f D.tube
      D.tube_PL D.tube_fibers D.period_value
  let idx : Fin 2 → M.Index := fun k ↦ if D.label k = 0 then i else M.mate i
  have hpiece (k) : (if D.label k = 0 then M.pieces i else M.pieces (M.mate i)) =
      M.pieces (idx k) := by dsimp [idx]; split_ifs <;> rfl
  have hmiddle (k) (p : squareAnnulus l d) :
      ((B k).chart p : P2) ∈ M.pieces (idx k) ↔ depth l p = 0 := by
    rw [← hpiece k]
    have hh := D.middle k ((D.chart k).symm ((B k).chart p))
    simpa only [Homeomorph.apply_symm_apply] using hh.trans (hzero k p)
  have hsource (k) : M.pieces (idx k) ⊆ D.source k := by
    rw [← hpiece k, ← D.middle_image k]
    rintro x ⟨p, _, rfl⟩
    exact (D.chart k p).property
  refine ⟨B, τ, idx, hτ, himage.subset.trans D.tube_interior, hfib, hvalue, ?_, ?_, ?_⟩
  · rw [himage, D.full_preimage]
    ext x
    simp only [mem_iUnion, Fin.exists_fin_two, mem_union]
  · intro k
    apply Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact (hmiddle k p).mpr hp
    · intro x hx
      let p := (B k).chart.symm ⟨x, hsource k hx⟩
      have hv : ((B k).chart p : P2) = x := congrArg Subtype.val ((B k).chart.apply_symm_apply _)
      exact ⟨p, (hmiddle k p).mp (hv.symm ▸ hx), hv⟩
  · intro k x hx hdbl
    rw [← hpiece k]
    exact (D.source_double_trace k).subset ⟨hx, hdbl⟩

end PoincareConjecture.M76.Dehn.Annuli
