import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.Gluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn

open _root_.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_finitePL_annular_straightening
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (f : V2 → P2) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ H : Ann ≃ₜ Ann, H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ (b : Bool) (z : Circle), H (annulusRimPoint b z) = annulusRimPoint b z) ∧
      H '' range gamma = range annulusCoreCircle ∧
      ∃ q : Q2 ≃ₜ Circle, ∀ x : Q2, H (gamma x) = annulusCoreCircle (q x) := by
  classical
  let ambient : C(Q2, P2) := ⟨fun x => gamma x, continuous_subtype_val.comp gamma.continuous⟩
  have hamb : Function.Injective ambient := fun x y h => hinj (Subtype.ext h)
  obtain ⟨n, P, hP, hi, hPb⟩ :=
    exists_polygon_of_finitePL_embedded_square_rim ambient hamb f hf hvalue
  have hboundary : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hPb.subset hx
    exact hdepth z
  have hgamma : ∀ x, (gamma x : P2) ∈ P.boundary ℝ := fun x =>
    hPb.symm.subset (mem_range_self x)
  obtain ⟨henclosing, _⟩ := essential_polygon_in_square_annulus
    P hP hi hboundary gamma hgamma hessential
  obtain ⟨outer, inner, houter, hinner, hoo, hoi, hio, hii, hcover, hinter⟩ :=
    Annuli.exists_enclosing_polygon_complementary_annuli P hP hi
      (L := 8) (d := 1) (by norm_num) (by norm_num) hboundary henclosing
  have hout : annulusSquare 8 (-1) \ P.inside ⊆ Ann :=
    subset_union_left.trans hcover.subset
  have hin : closure P.inside \ interior (annulusSquare 8 1) ⊆ Ann :=
    subset_union_right.trans hcover.subset
  have hC₀ : P.boundary ℝ ⊆ annulusSquare 8 (-1) \ P.inside :=
    hinter.symm.subset.trans inter_subset_left
  have hC₁ : P.boundary ℝ ⊆ closure P.inside \ interior (annulusSquare 8 1) :=
    hinter.symm.subset.trans inter_subset_right
  have hB₀ : range (fun z => (annulusRimPoint false z : P2)) ⊆
      annulusSquare 8 (-1) \ P.inside := by
    rintro _ ⟨z, rfl⟩
    have hd := depth_annulusRimPoint false z
    simp only [Bool.false_eq_true, ↓reduceIte] at hd
    refine ⟨(mem_annulusSquare_iff _ _ _).mpr hd.ge, ?_⟩
    intro hz
    have hs := (Annuli.source_polygon_disk_or_enclosing P hP hi hboundary).2.1
      (subset_closure hz)
    have hh := (mem_interior_annulusSquare_iff _ _ _).mp hs
    linarith
  have hB₁ : range (fun z => (annulusRimPoint true z : P2)) ⊆
      closure P.inside \ interior (annulusSquare 8 1) := by
    rintro _ ⟨z, rfl⟩
    have hd := depth_annulusRimPoint true z
    simp only [↓reduceIte] at hd
    refine ⟨subset_closure (henclosing ((mem_annulusSquare_iff _ _ _).mpr hd.ge)), ?_⟩
    intro hz
    have hh := (mem_interior_annulusSquare_iff _ _ _).mp hz
    linarith
  obtain ⟨O, J, parameter, hO, hJ, hOzero, hOone, hJzero, hJone⟩ :=
    exists_matched_annular_complements outer inner houter hinner hout hin hC₀ hC₁
      hB₀ hB₁ hoo hoi hio hii
  obtain ⟨G, hG, hGrim, hGcore⟩ := exists_annular_gluing_fixing_rims
    O J parameter hO hJ hcover hinter hOzero hOone hJzero hJone
  let toPolygon : Q2 → P.boundary ℝ := fun x => ⟨gamma x, hgamma x⟩
  have htoPolygon : Continuous toPolygon := ambient.continuous.subtype_mk _
  have htoPolygonI : Function.Injective toPolygon := by
    intro x y h
    exact hinj (Subtype.ext (congrArg (fun z : P.boundary ℝ => (z : P2)) h))
  have htoPolygonS : Function.Surjective toPolygon := by
    intro y
    obtain ⟨x, hx⟩ := hPb.subset y.property
    exact ⟨x, Subtype.ext hx⟩
  let Q : Q2 ≃ₜ P.boundary ℝ := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective toPolygon ⟨htoPolygonI, htoPolygonS⟩) htoPolygon
  let q : Q2 ≃ₜ Circle := Q.trans parameter.symm
  have hstraight (x : Q2) : G.symm (gamma x) = annulusCoreCircle (q x) := by
    apply G.injective
    rw [G.apply_symm_apply]
    apply Subtype.ext
    rw [hGcore]
    change (gamma x : P2) = (parameter (parameter.symm (Q x)) : P2)
    rw [parameter.apply_symm_apply]
    rfl
  refine ⟨G.symm, hG.symm, hG, ?_, ?_, q, hstraight⟩
  · intro b z
    apply G.injective
    rw [G.apply_symm_apply, hGrim]
  · apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨q x, (hstraight x).symm⟩
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := q.surjective z
      exact ⟨gamma x, mem_range_self x, hstraight x⟩

end PoincareConjecture.M76.Dehn
