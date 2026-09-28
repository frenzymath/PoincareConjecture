import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.EssentialRegions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.BoundaryComparisons
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Geometry PLAnnularStrip

namespace AddCircle



theorem exists_signed_period_lift_of_homotopic_homeomorph
    {p : ℝ} [Fact (0 < p)] (f : C(AddCircle p, AddCircle p))
    (q : AddCircle p ≃ₜ AddCircle p)
    (H : f.Homotopy ⟨q, q.continuous⟩) :
    ∃ L : C(ℝ, ℝ),
      (∀ t, (L t : AddCircle p) = f (t : AddCircle p)) ∧
      ((∀ t, L (t + p) = L t + p) ∨ (∀ t, L (t + p) = L t - p)) := by
  have hcoe (r : ℝ) : ((r + p : ℝ) : AddCircle p) = (r : AddCircle p) := by
    rw [coe_add, coe_period, add_zero]
  let cov := isCoveringMap_coe p
  let b : ℝ := equivIco p 0 (f 0)
  obtain ⟨L, ⟨_, hL⟩, _⟩ := cov.existsUnique_continuousMap_lifts
    ⟨fun t : ℝ => f (t : AddCircle p), f.continuous.comp (AddCircle.continuous_mk' p)⟩
    0 b (show (b : AddCircle p) = f (0 : AddCircle p) from coe_equivIco)
  have hLt (t : ℝ) : (L t : AddCircle p) = f (t : AddCircle p) := congrFun hL t
  let c : ℝ := equivIco p 0 (q 0)
  obtain ⟨Q, _, hQ⟩ := exists_real_homeomorph_lift q c coe_equivIco
  have hd := lift_period_displacement_eq_of_homotopy f ⟨q, q.continuous⟩ H
    L ⟨Q, Q.continuous⟩ hLt hQ
  have hperiod (t : ℝ) : L (t + p) - L t = L p - L 0 := by
    have hsame (s t : ℝ) :
        ((L (s + p) - L s : ℝ) : AddCircle p) =
          ((L (t + p) - L t : ℝ) : AddCircle p) := by
      rw [coe_sub, coe_sub, hLt (s + p), hLt s, hLt (t + p), hLt t]
      rw [hcoe s, hcoe t, sub_self, sub_self]
    have h := cov.const_of_comp (g := fun t : ℝ => L (t + p) - L t)
      (by fun_prop) hsame t 0
    simpa only [zero_add] using h
  refine ⟨L, hLt, ?_⟩
  rcases real_homeomorph_lift_orientation q Q hQ with ⟨_, hpos⟩ | ⟨_, hneg⟩
  · left
    intro t
    have h := hpos 0
    dsimp only [ContinuousMap.coe_mk] at hd
    simp only [zero_add] at h
    linarith [hperiod t]
  · right
    intro t
    have h := hneg 0
    dsimp only [ContinuousMap.coe_mk] at hd
    simp only [zero_add] at h
    linarith [hperiod t]

end AddCircle

namespace PoincareConjecture.M76.Dehn

open _root_.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1

private theorem exists_outer_rim_homeomorph :
    ∃ H : Circle ≃ₜ frontier (annulusSquare 8 (-1)),
      ∀ z, (H z : P2) = (annulusRimPoint false z : P2) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let f : Circle → frontier (annulusSquare 8 (-1)) := fun z =>
    ⟨annulusRimPoint false z, (mem_frontier_annulusSquare_iff _ _ _).mpr
      (depth_annulusRimPoint false z)⟩
  have hf : Continuous f :=
    (continuous_subtype_val.comp (continuous_annulusRimPoint false)).subtype_mk _
  have hfi : Function.Injective f := by
    intro z w h
    exact injective_annulusRimPoint false
      (Subtype.ext (congrArg (fun x : frontier (annulusSquare 8 (-1)) => (x : P2)) h))
  have hfs : Function.Surjective f := by
    intro x
    have hd : depth 8 (x : P2) = -1 :=
      (mem_frontier_annulusSquare_iff _ _ _).mp x.property
    have hx : (x : P2) ∈ Ann := mem_squareAnnulus_iff_depth.mpr
      ⟨hd.ge, by linarith⟩
    obtain ⟨z, hz⟩ := (range_annulusRimPoint false).symm.subset
      (show depth 8 ((⟨x, hx⟩ : Ann) : P2) = -1 from hd)
    exact ⟨z, Subtype.ext (congrArg (fun x : Ann => (x : P2)) hz)⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hfi, hfs⟩) hf, fun _ => rfl⟩





theorem exists_essential_polygon_rim_homotopy
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hboundary : ∀ p ∈ P.boundary ℝ, -1 < depth 8 p ∧ depth 8 p < 1)
    (gamma : C(Q2, Ann))
    (hgamma : ∀ x, (gamma x : P2) ∈ P.boundary ℝ)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1)
    (j : C(Circle, Ann)) (hji : Function.Injective j)
    (hj : range (fun z => (j z : P2)) = P.boundary ℝ) :
    ∃ q : Circle ≃ₜ Circle,
      Nonempty (j.Homotopy
        ⟨fun z => annulusRimPoint false (q z),
          (continuous_annulusRimPoint false).comp q.continuous⟩) := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨henclosing, _⟩ := essential_polygon_in_square_annulus P hP hi
    hboundary gamma hgamma hessential
  obtain ⟨outer, inner, _, _, hoo, hoi, _, _, hcover, _⟩ :=
    Annuli.exists_enclosing_polygon_complementary_annuli P hP hi
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (2 : ℝ) * 1 < 8)
      hboundary henclosing
  have hout : annulusSquare 8 (-1) \ P.inside ⊆ Ann := by
    intro x hx
    rw [← hcover]
    exact Or.inl hx
  obtain ⟨H0, hH0⟩ := exists_outer_rim_homeomorph
  let jp : Circle → P.boundary ℝ := fun z => ⟨j z, hj ▸ mem_range_self z⟩
  have hjpc : Continuous jp := (continuous_subtype_val.comp j.continuous).subtype_mk _
  have hjpi : Function.Injective jp := by
    intro z w h
    exact hji (Subtype.ext (congrArg (fun x : P.boundary ℝ => (x : P2)) h))
  have hjps : Function.Surjective jp := by
    intro x
    obtain ⟨z, hz⟩ := hj.symm.subset x.property
    exact ⟨z, Subtype.ext hz⟩
  let H1 : Circle ≃ₜ P.boundary ℝ := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective jp ⟨hjpi, hjps⟩) hjpc
  let B : Bool → Set P2 := fun b => if b then P.boundary ℝ
    else frontier (annulusSquare 8 (-1))
  let H : ∀ b, Circle ≃ₜ B b := fun b => by cases b; exact H0; exact H1
  have hB : ∀ b, B b ⊆ annulusSquare 8 (-1) \ P.inside := by
    intro b x hx
    cases b
    · change x ∈ frontier (annulusSquare 8 (-1)) at hx
      have hd := (mem_frontier_annulusSquare_iff _ _ _).mp hx
      refine ⟨(mem_annulusSquare_iff _ _ _).mpr hd.ge, ?_⟩
      intro hp
      have hs := (Annuli.source_polygon_disk_or_enclosing P hP hi hboundary).2.1
        (subset_closure hp)
      have hh := (mem_interior_annulusSquare_iff _ _ _).mp hs
      linarith
    · change x ∈ P.boundary ℝ at hx
      have hc : x ∈ closure P.inside := by
        rw [← P.frontier_inside hP hi] at hx
        exact frontier_subset_closure hx
      refine ⟨interior_subset
        ((Annuli.source_polygon_disk_or_enclosing P hP hi hboundary).2.1 hc), ?_⟩
      rw [← P.frontier_inside hP hi, frontier,
        (P.isOpen_inside hP hi).interior_eq] at hx
      exact hx.2
  have hmark : ∀ b (z : Ann),
      depth 8 (z : P2) = (if b then 1 else -1) ↔ (outer z : P2) ∈ B b := by
    intro b z
    cases b
    · exact (hoo z).trans (mem_frontier_annulusSquare_iff _ _ _).symm
    · exact hoi z
  obtain ⟨q, hq⟩ := exists_annulus_boundary_comparisons outer B hB H hmark
  let r : Circle ≃ₜ Circle := (q true).trans (q false).symm
  let rim : C(Circle, Ann) := ⟨fun z => annulusRimPoint false (r z),
    (continuous_annulusRimPoint false).comp r.continuous⟩
  have hhom : Nonempty (rim.Homotopy j) := by
    refine ⟨{
    toFun := fun z => ⟨outer (annulusRimCylinder (z.1, q true z.2)),
      hout (outer _).property⟩
    continuous_toFun := (continuous_subtype_val.comp (outer.continuous.comp
      (annulusRimCylinder.continuous.comp
        (continuous_fst.prodMk ((q true).continuous.comp continuous_snd))))).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_
    }⟩
    · intro z
      apply Subtype.ext
      dsimp only
      rw [annulusRimCylinder_zero]
      have hr : q false (r z) = q true z := (q false).apply_symm_apply _
      rw [← hr, hq false]
      exact hH0 (r z)
    · intro z
      apply Subtype.ext
      dsimp only
      rw [annulusRimCylinder_one, hq true]
      rfl
  exact ⟨r, ⟨hhom.some.symm⟩⟩




theorem exists_essential_polygon_signed_radial_lift
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hboundary : ∀ p ∈ P.boundary ℝ, -1 < depth 8 p ∧ depth 8 p < 1)
    (gamma : C(Q2, Ann))
    (hgamma : ∀ x, (gamma x : P2) ∈ P.boundary ℝ)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1)
    (j : C(Circle, Ann)) (hji : Function.Injective j)
    (hj : range (fun z => (j z : P2)) = P.boundary ℝ) :
    ∃ L : C(ℝ, ℝ),
      (∀ t, (L t : Circle) = (annulusCylinderHomeomorph.symm (j (t : Circle))).2) ∧
      ((∀ t, L (t + 32) = L t + 32) ∨ (∀ t, L (t + 32) = L t - 32)) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨q, ⟨H⟩⟩ := exists_essential_polygon_rim_homotopy P hP hi
    hboundary gamma hgamma hessential j hji hj
  let f : C(Circle, Circle) :=
    ⟨fun z => (annulusCylinderHomeomorph.symm (j z)).2,
      (annulusCylinderHomeomorph.symm.continuous.comp j.continuous).snd⟩
  have Hradial : f.Homotopy ⟨q, q.continuous⟩ := {
    toFun := fun z => (annulusCylinderHomeomorph.symm (H z)).2
    continuous_toFun := (annulusCylinderHomeomorph.symm.continuous.comp H.continuous).snd
    map_zero_left := fun z => congrArg
      (fun x => (annulusCylinderHomeomorph.symm x).2) (H.apply_zero z)
    map_one_left := by
      intro z
      rw [H.apply_one]
      change (annulusCylinderHomeomorph.symm (annulusRimPoint false (q z))).2 = q z
      rw [← annulusCylinderHomeomorph_zero, annulusCylinderHomeomorph.symm_apply_apply]
  }
  obtain ⟨L, hL, hperiod⟩ :=
    AddCircle.exists_signed_period_lift_of_homotopic_homeomorph f q Hradial
  refine ⟨L, hL, ?_⟩
  simpa only [show (4 : ℝ) * 8 = 32 by norm_num] using hperiod

end PoincareConjecture.M76.Dehn
