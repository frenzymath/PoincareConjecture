import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.TerminalSupport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.DiskReplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.SupportedAnnularDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates









set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry PLAnnularStrip Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "p₀" => ((-1, 0) : P2)
local notation "p₁" => ((1, 0) : P2)

theorem annularLiftProjection_axis_eq_radial :
    annularLiftProjection '' segment ℝ p₀ p₁ =
      range (fun t : I => (annulusCylinderHomeomorph (t, 0) : P2)) := by
  have hval (t : I) : annularLiftProjection (AffineMap.lineMap p₀ p₁ (t : ℝ)) =
      (annulusCylinderHomeomorph (t, 0) : P2) := by
    rw [annulusCylinderHomeomorph_apply]
    have hline : AffineMap.lineMap p₀ p₁ (t : ℝ) = (2 * (t : ℝ) - 1, 0) := by
      ext <;> simp [AffineMap.lineMap_apply_module', smul_eq_mul]
      ring
    rw [hline]
    rfl
  rw [segment_eq_image_lineMap]
  apply Subset.antisymm
  · rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨⟨t, ht⟩, (hval ⟨t, ht⟩).symm⟩
  · rintro x ⟨t, rfl⟩
    exact ⟨AffineMap.lineMap p₀ p₁ (t : ℝ),
      ⟨t, t.property, rfl⟩, hval t⟩

theorem exists_joint_PL_annular_terminal_arc_isotopy
    {W : Set P2} {a b : ℝ}
    (hW : IsFinitePLBallPair ℝ W {p₀, p₁}) (hwidth : b - a < 32)
    (hstrip : W ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (hproper : W \ {p₀, p₁} ⊆ Ioo (-1 : ℝ) 1 ×ˢ univ) :
    ∃ (H : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
      H 0 = Homeomorph.refl Ann ∧
      (∀ t : I, ∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → H t x = x) ∧
      Continuous (fun z : I × Ann => H z.1 z.2) ∧
      Continuous (fun z : I × Ann => (H z.1).symm z.2) ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, F ((t : ℝ), x) = (H t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, Fi ((t : ℝ), x) = ((H t).symm x : P2)) ∧
      ∀ x : Ann, (x : P2) ∈ annularLiftProjection '' W ↔
        (H 1 x : P2) ∈ annularLiftProjection '' segment ℝ p₀ p₁ := by
  obtain ⟨S, hS, hSAnn, hp₀, hp₁, hpne, hU, hV, hproperU, hproperV, hrimS⟩ :=
    exists_annular_terminal_strip_support hW hwidth hstrip hproper
  let U := annularLiftProjection '' W
  let V := annularLiftProjection '' segment ℝ p₀ p₁
  have hUS : U ⊆ S := by
    intro x hx
    by_cases he : x ∈ ({annularLiftProjection p₀, annularLiftProjection p₁} : Set P2)
    · rcases he with rfl | rfl
      · exact hS.1 hp₀
      · exact hS.1 hp₁
    · exact (hproperU ⟨hx, he⟩).1
  have hVS : V ⊆ S := by
    intro x hx
    by_cases he : x ∈ ({annularLiftProjection p₀, annularLiftProjection p₁} : Set P2)
    · rcases he with rfl | rfl
      · exact hS.1 hp₀
      · exact hS.1 hp₁
    · exact (hproperV ⟨hx, he⟩).1
  obtain ⟨u, hu, hu0, hu1⟩ := hU.exists_unitInterval_chart_with_endpoints hpne
  obtain ⟨v, hv, hv0, hv1⟩ := hV.exists_unitInterval_chart_with_endpoints hpne
  let q : U ≃ₜ V := u.symm.trans v
  have hq : q.IsFinitePL := hu.symm.trans hv
  have hqends (x : U)
      (hx : (x : P2) ∈ ({annularLiftProjection p₀, annularLiftProjection p₁} : Set P2)) :
      (q x : P2) = x := by
    rcases hx with hx | hx
    · have hxu : x = u 0 := Subtype.ext (hx.trans hu0.symm)
      rw [hxu]
      change (v (u.symm (u 0)) : P2) = u 0
      rw [u.symm_apply_apply]
      exact hv0.trans hu0.symm
    · have hxu : x = u 1 := Subtype.ext (hx.trans hu1.symm)
      rw [hxu]
      change (v (u.symm (u 1)) : P2) = u 1
      rw [u.symm_apply_apply]
      exact hv1.trans hu1.symm
  obtain ⟨e, he, _, hefix, _, hemem⟩ :=
    exists_finitePL_proper_arc_replacement_fix_rim hS hU hV hp₀ hp₁ hpne
      hproperU hproperV q hq hqends
  obtain ⟨H, F, Fi, hzero, hfixed, hfixoff, hc, hci, hF, hFi, hFv, hFiv, hHe⟩ :=
    exists_joint_PL_supported_annular_disk_isotopy hS hSAnn hrimS e he hefix
  refine ⟨H, F, Fi, hzero, hfixed, hc, hci, hF, hFi, hFv, hFiv, ?_⟩
  intro x
  by_cases hx : (x : P2) ∈ S
  · have hv := congrArg (fun y : Ann => (y : P2)) (hHe ⟨x, hx⟩)
    change (H 1 x : P2) = (e ⟨x, hx⟩ : P2) at hv
    rw [hv]
    exact hemem ⟨x, hx⟩
  · rw [hfixoff 1 x (fun h => hx (interior_subset h))]
    exact iff_of_false (fun h => hx (hUS h)) (fun h => hx (hVS h))

end PoincareConjecture.M76.Dehn
