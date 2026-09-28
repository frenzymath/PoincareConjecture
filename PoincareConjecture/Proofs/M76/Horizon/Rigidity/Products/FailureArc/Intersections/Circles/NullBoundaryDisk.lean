import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.State
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.EssentialRegions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem enclosing_polygon_null_boundary_forces_null_rim
    {X : Type*} [TopologicalSpace X] (f : C(Ann, X))
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hboundary : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1)
    (henclosing : annulusSquare 8 1 ⊆ P.inside)
    (boundary : C(P.boundary ℝ, X))
    (hvalue : ∀ x : P.boundary ℝ, boundary x =
      f ⟨x, mem_squareAnnulus_iff_depth.mpr
        ⟨(hboundary x x.property).1.le, (hboundary x x.property).2.le⟩⟩)
    (hnull : boundary.Nullhomotopic) :
    (planarAnnulusRim f false).Nullhomotopic := by
  obtain ⟨outer, _, _, _, ho0, ho1, _, _, hcover, _⟩ :=
    exists_enclosing_polygon_complementary_annuli P hP hi
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (2 : ℝ) * 1 < 8)
      hboundary henclosing
  have hout : annulusSquare 8 (-1) \ P.inside ⊆ Ann := by
    intro x hx
    rw [← hcover]
    exact Or.inl hx
  let inclusion : C((annulusSquare 8 (-1) \ P.inside : Set P2), Ann) :=
    ContinuousMap.inclusion hout
  let F : C(Ann, X) := f.comp (inclusion.comp ⟨outer, outer.continuous⟩)
  let inner : C(Circle, P.boundary ℝ) :=
    ⟨fun z => ⟨outer (annulusRimPoint true z), (ho1 _).mp (depth_annulusRimPoint true z)⟩,
      (continuous_subtype_val.comp (outer.continuous.comp
        (continuous_annulusRimPoint true))).subtype_mk _⟩
  have hinner : boundary.comp inner = planarAnnulusRim F true := by
    apply ContinuousMap.ext
    intro z
    exact hvalue (inner z)
  have hinnerNull : (planarAnnulusRim F true).Nullhomotopic :=
    hinner ▸ hnull.comp_left inner
  have hom : (planarAnnulusRim F false).Homotopy (planarAnnulusRim F true) := {
    toFun := fun z => F (annulusRimCylinder z)
    continuous_toFun := F.continuous.comp annulusRimCylinder.continuous
    map_zero_left := fun z => by rw [annulusRimCylinder_zero]; rfl
    map_one_left := fun z => by rw [annulusRimCylinder_one]; rfl }
  have houterNull : (planarAnnulusRim F false).Nullhomotopic := by
    obtain ⟨x, hx⟩ := hinnerNull
    exact ⟨x, (show (planarAnnulusRim F false).Homotopic
      (planarAnnulusRim F true) from ⟨hom⟩).trans hx⟩
  have hrim (z : Circle) : (annulusRimPoint false z : P2) ∈
      annulusSquare 8 (-1) \ P.inside := by
    have hd : depth 8 (annulusRimPoint false z : P2) = -1 := depth_annulusRimPoint false z
    refine ⟨(mem_annulusSquare_iff _ _ _).mpr hd.ge, ?_⟩
    intro hp
    have hh := (mem_interior_annulusSquare_iff _ _ _).mp
      ((source_polygon_disk_or_enclosing P hP hi hboundary).2.1 (subset_closure hp))
    change -1 < depth 8 (annulusRimPoint false z : P2) at hh
    linarith
  let oldRim : C(Circle, (annulusSquare 8 (-1) \ P.inside : Set P2)) :=
    ⟨fun z => ⟨annulusRimPoint false z, hrim z⟩,
      (continuous_subtype_val.comp (continuous_annulusRimPoint false)).subtype_mk _⟩
  obtain ⟨rimHomeo, hrv⟩ := exists_annulus_rim_circle_homeomorph false
  let pullback : C(Circle, {x : Ann | depth 8 (x : P2) = -1}) :=
    ⟨fun z => ⟨outer.symm (oldRim z), (ho0 _).mpr (by
        rw [outer.apply_symm_apply]
        exact depth_annulusRimPoint false z)⟩,
      (outer.symm.continuous.comp oldRim.continuous).subtype_mk _⟩
  let q : C(Circle, Circle) :=
    (⟨rimHomeo.symm, rimHomeo.symm.continuous⟩ : C(_, Circle)).comp pullback
  have hq (z : Circle) : annulusRimPoint false (q z) = outer.symm (oldRim z) :=
    (hrv (q z)).symm.trans (congrArg Subtype.val (rimHomeo.apply_symm_apply (pullback z)))
  have heq : (planarAnnulusRim F false).comp q = planarAnnulusRim f false := by
    apply ContinuousMap.ext
    intro z
    change f (inclusion (outer (annulusRimPoint false (q z)))) = f (annulusRimPoint false z)
    rw [hq, outer.apply_symm_apply]
    rfl
  exact heq ▸ houterNull.comp_left q

theorem polygon_disk_in_essential_annulus_of_null_boundary
    {X : Type*} [TopologicalSpace X] (f : C(Ann, X))
    (hessential : ¬ (planarAnnulusRim f false).Nullhomotopic)
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hboundary : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1)
    (boundary : C(P.boundary ℝ, X))
    (hvalue : ∀ x : P.boundary ℝ, boundary x =
      f ⟨x, mem_squareAnnulus_iff_depth.mpr
        ⟨(hboundary x x.property).1.le, (hboundary x x.property).2.le⟩⟩)
    (hnull : boundary.Nullhomotopic) :
    IsFinitePLBallPair P2 (closure P.inside) (P.boundary ℝ) ∧
      closure P.inside ⊆ {x : P2 | -1 < depth 8 x ∧ depth 8 x < 1} := by
  obtain ⟨hball, _, henclosing | hinside⟩ := source_polygon_disk_or_enclosing P hP hi hboundary
  · exact (hessential (enclosing_polygon_null_boundary_forces_null_rim f P hP hi
      hboundary henclosing boundary hvalue hnull)).elim
  · exact ⟨hball, hinside⟩

end PoincareConjecture.M76.Dehn.Annuli
