import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.PairedGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.PairedStep
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.SelfPaired.Step
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Circles.SourceCases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Circles.NestedSurgery

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_decreasing_planar_region_annulus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (period : Circle ≃ₜ Q) {R : Set X} (he : PLDomain e R)
    (f₀ : P2 → X) (hf : PolyhedralPLInCharts e f₀ Ann)
    (hin : MapsTo f₀ Ann R)
    (hproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (rim : C(Q, R)) (hessential : ¬ rim.Nullhomotopic)
    (hrim : ∀ u : Q, f₀ (annulusRimPoint false (period.symm u)) = (rim u : X))
    (M : Annuli.SourceCircleDecomposition f₀ Ann)
    (hinterior : MapsTo f₀ (doubleLocusOn f₀ Ann) (interior R))
    (hcross : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → f₀ x = f₀ y →
      Nonempty (Annuli.RawSourceCrossing e f₀ Ann R x y))
    (hpos : 0 < Nat.card (ConnectedComponents (doubleLocusOn f₀ Ann))) :
    ∃ (g : P2 → X) (q : Bool → Circle ≃ₜ Circle),
      PolyhedralPLInCharts e g Ann ∧ MapsTo g Ann R ∧
      (∀ x ∈ Ann, g x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      (∀ b z, g (annulusRimPoint b z) = f₀ (annulusRimPoint b (q b z))) ∧
      MapsTo g (doubleLocusOn g Ann) (interior R) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → g x = g y →
        Nonempty (Annuli.RawSourceCrossing e g Ann R x y)) ∧
      Nonempty (Annuli.SourceCircleDecomposition g Ann) ∧
      Nat.card (ConnectedComponents (doubleLocusOn g Ann)) <
        Nat.card (ConnectedComponents (doubleLocusOn f₀ Ann)) := by
  classical
  obtain ⟨J, hJ, hJS⟩ := Annuli.exists_planar_annulus_complex
  have hfront : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ x ∈ frontier Ann := by
    intro x hx
    rw [hproper x hx, Annuli.mem_frontier_planar_annulus_iff]
  have hcollision := Annuli.planar_annulus_collision_free_of_double_interior hproper hinterior
  obtain ⟨i⟩ := M.exists_component_of_count_pos hpos
  by_cases hself : M.mate i = i
  · have hsurgery := Annuli.SourceCircleDecomposition.exists_selfpaired_step
      (e := e) (f := f₀) (R := R) J hJ
    rw [hJS] at hsurgery
    obtain ⟨g, hg, hgin, hgb, hgfront, hgcollision, _, hgraw, _, hgM, hgcount⟩ :=
      hsurgery M hf he hin hfront hcollision hcross i hself
    refine ⟨g, fun _ ↦ Homeomorph.refl _, hg, hgin, ?_, ?_,
      Annuli.double_image_interior_of_proper_rim hgin hgfront hgcollision, hgraw, hgM, hgcount⟩
    · intro x hx
      rw [hgfront x hx, Annuli.mem_frontier_planar_annulus_iff]
    · intro b z
      exact hgb (Annuli.annulusRimPoint_mem_frontier b z)
  obtain ⟨D⟩ := M.nonempty_identity_annuli J hJ hJS hf he hcross hinterior hfront i hself
    (L := 1) (d := 1 / 8) (by norm_num) (by norm_num)
  obtain ⟨B, τ, idx, hτ, hτR, hfib, hvalue, hpre, hmiddle, htrace⟩ := D.exists_oriented_collars
  have hA : ∀ k, D.source k ⊆ {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1} := by
    intro k x hx
    have hh := D.source_interior k hx
    rwa [interior_squareAnnulus (by norm_num : 2 * (1 : ℝ) < 8)] at hh
  rcases paired_collar_source_cases_of_essential e hcompat period D.depth_pos D.width_small
      D.source B hA D.disjoint f₀ hf hin rim hessential hrim τ hτ
      (fun _ hx ↦ interior_subset (hτR ⟨_, hx, rfl⟩)) hfib hvalue with
      hcontract | ⟨j, henclosing, hnested⟩
  · have hsurgery := Annuli.exists_contractible_paired_ordinary_map e hcompat
      J hJ (b := 1 / 16) B
    rw [hJS] at hsurgery
    have hcontract' : ∀ k, closure (B k).outer.inside ⊆ interior Ann := by
      intro k x hx
      rw [interior_squareAnnulus (by norm_num : 2 * (1 : ℝ) < 8)]
      exact hcontract k hx
    obtain ⟨g, hg, hgin, hgb, hgfront, hgcollision, _, hgraw, _, hgM, hgcount⟩ :=
      hsurgery hcontract' D.disjoint D.depth_pos D.width_small
        (by norm_num) (by norm_num) f₀ hf R hin hfront hcollision hcross
        τ hτ hτR hfib hvalue hpre M (idx 0) (idx 1)
        (hmiddle 0) (hmiddle 1) (htrace 0) (htrace 1)
    refine ⟨g, fun _ ↦ Homeomorph.refl _, hg, hgin, ?_, ?_,
      Annuli.double_image_interior_of_proper_rim hgin hgfront hgcollision, hgraw, hgM, hgcount⟩
    · intro x hx
      rw [hgfront x hx, Annuli.mem_frontier_planar_annulus_iff]
    · intro b z
      exact hgb (Annuli.annulusRimPoint_mem_frontier b z)
  · have hpre' : ∀ x ∈ Ann, f₀ x ∈ τ '' identityTube 1 (1 / 8) ↔
        x ∈ D.source j ∪ D.source j.rev := by
      intro x hx
      have hh : x ∈ Ann ∩ f₀ ⁻¹' (τ '' identityTube 1 (1 / 8)) ↔
          x ∈ D.source 0 ∪ D.source 1 := Set.ext_iff.mp hpre x
      simp only [mem_inter_iff, mem_preimage, hx, true_and] at hh
      fin_cases j
      · exact hh
      · change f₀ x ∈ τ '' identityTube 1 (1 / 8) ↔ x ∈ D.source 1 ∪ D.source 0
        rw [union_comm]
        exact hh
    obtain ⟨g, q, hg, hgin, hgfront, hgwhole, _, _, hginterior, hgraw, _, hgM, hgcount⟩ :=
      exists_essential_paired_region_surgery e hcompat f₀ hf hin
        hproper M hinterior hcross D.depth_pos D.width_small
        D.source B j hA henclosing hnested idx hmiddle htrace τ hτ
        (fun _ hx ↦ hτR ⟨_, hx, rfl⟩) hfib hvalue hpre'
    exact ⟨g, q, hg, hgin, hgfront, hgwhole, hginterior, hgraw, hgM, hgcount⟩

end PoincareConjecture.M76.Dehn.Annuli
