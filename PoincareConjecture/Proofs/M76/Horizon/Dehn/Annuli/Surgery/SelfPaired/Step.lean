import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.SelfPaired.Ordinary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.SourceAnnuli.OriginalReflection









set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem SourceCircleDecomposition.exists_selfpaired_step
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {R : Set X}
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    (M : SourceCircleDecomposition f J.space)
    (hf : PolyhedralPLInCharts e f J.space) (he : PLDomain e R)
    (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (hcollision : Disjoint (doubleLocusOn f J.space) (frontier J.space))
    (hcross : ∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f J.space R x y))
    (i : M.Index) (hself : M.mate i = i) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g J.space ∧ MapsTo g J.space R ∧
      EqOn g f (frontier J.space) ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      Disjoint (doubleLocusOn g J.space) (frontier J.space) ∧
      IsCompact (doubleLocusOn g J.space) ∧
      (∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → g x = g y →
        Nonempty (RawSourceCrossing e g J.space R x y)) ∧
      IsLocallyInjective (fun x : J.space ↦ g x) ∧
      Nonempty (SourceCircleDecomposition g J.space) ∧
      Nat.card (ConnectedComponents (doubleLocusOn g J.space)) <
        Nat.card (ConnectedComponents (doubleLocusOn f J.space)) := by
  obtain ⟨D⟩ := M.nonempty_reflection_annulus J hJ rfl hf he hcross
    (double_image_interior_of_proper_rim hin hfront hcollision) hfront i hself
    (L := 1) (d := 1 / 8) (by norm_num) (by norm_num)
  have hmiddle : (fun p : squareAnnulus 1 (1 / 8 : ℝ) ↦ (D.chart p : P2)) ''
      {p | depth 1 p = 0} = M.pieces i := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact (D.middle p).mpr hp
    · intro x hx
      have hxT := (D.double_trace.symm.subset hx).1
      let p := D.chart.symm ⟨x, hxT⟩
      have hp : (D.chart p : P2) = x := congrArg Subtype.val (D.chart.apply_symm_apply _)
      exact ⟨p, (D.middle p).mp (hp.symm ▸ hx), hp⟩
  have htrace : doubleLocusOn f J.space ∩ D.source = M.pieces i := by
    rw [inter_comm, D.double_trace]
  exact exists_reflection_ordinary_map J hJ hf he hin hfront hcollision hcross
    (b := 1 / 16) D.depth_pos D.width_small (by norm_num) (by norm_num)
    D.tube D.tube_PL D.tube_fibers D.tube_interior D.source_interior D.chart D.chart_PL
    D.period_value D.full_preimage M i hmiddle htrace

end PoincareConjecture.M76.Dehn.Annuli
