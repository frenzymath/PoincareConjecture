import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Resolution.MarkedArcStep










set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}


theorem OrdinaryDoubleCurveModel.double_locus_disjoint_rim_of_boundary_count_zero
    (old : OrdinaryDoubleCurveModel e f R)
    (hzero : doubleBoundaryComponentCount f D2 Q2 = 0) :
    Disjoint (doubleLocusOn f D2) Q2 := by
  have : Finite old.Index := old.finiteIndex
  have hempty : {i | (old.pieces i ∩ Q2).Nonempty} = ∅ := by
    apply (Set.ncard_eq_zero (Set.toFinite _)).mp
    rwa [← old.component_counts.1]
  apply disjoint_left.mpr
  intro x hx hq
  obtain ⟨i, hi⟩ := mem_iUnion.mp (old.cover.symm ▸ hx)
  exact Set.notMem_empty i (hempty ▸ (show (old.pieces i ∩ Q2).Nonempty from ⟨x, hi, hq⟩))


theorem OrdinaryDoubleCurveModel.isEmbedding_rim_of_boundary_count_zero [T2Space X]
    (old : OrdinaryDoubleCurveModel e f R) (hf : ContinuousOn f D2)
    (hzero : doubleBoundaryComponentCount f D2 Q2 = 0) :
    IsEmbedding (fun x : Q2 ↦ f x) := by
  have hd := old.double_locus_disjoint_rim_of_boundary_count_zero hzero
  apply ((hf.mono sphere_subset_closedBall).domRestrict.isClosedEmbedding ?_).isEmbedding
  intro x y hxy
  by_contra hne
  exact disjoint_left.mp hd
    ⟨sphere_subset_closedBall x.property, y, sphere_subset_closedBall y.property,
      hxy, fun h ↦ hne (Subtype.ext h)⟩ x.property



theorem OrdinaryDoubleCurveModel.exists_marked_disk_without_boundary_double_curves
    [T2Space X] {F : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    {base : F} {J : Subgroup (FundamentalGroup F base)} [J.Normal]
    (rim : C(Q2, F)) (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase))
    (houtside : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J)
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2) :
    ∃ (g : V2 → X) (rim' : C(Q2, F)) (basepath' : Path base (rim' squareRimBase)),
      PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧
      (∀ x : Q2, g x = (rim' x : X)) ∧
      (∀ x ∈ D2, g x ∈ F ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      basepath'.whiskeredLoopClass (squareRimLoop.map rim'.continuous) ∉ J ∧
      doubleBoundaryComponentCount g D2 Q2 = 0 ∧
      doubleInteriorComponentCount g D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) ∧ IsEmbedding (fun x : Q2 ↦ g x) := by
  generalize hn : doubleBoundaryComponentCount f D2 Q2 = n
  induction n using Nat.strong_induction_on generalizing f rim with
  | h n ih =>
    by_cases hzero : doubleBoundaryComponentCount f D2 Q2 = 0
    · have hfF (x : V2) (hx : x ∈ D2) : f x ∈ F ↔ x ∈ Q2 := by
        constructor
        · exact fun h ↦ (hfront x hx).mp (hF h)
        · intro hq
          rw [hboundary ⟨x, hq⟩]
          exact (rim ⟨x, hq⟩).property
      exact ⟨f, rim, basepath, hf, hin, hboundary, hfF, hfront, houtside,
        hzero, le_rfl, ⟨old⟩, old.isEmbedding_rim_of_boundary_count_zero hf.continuousOn hzero⟩
    · obtain ⟨g, rim', path', hg, hgR, hgr, hgF, hgfront, hgout, hless, hcircle, ⟨model⟩⟩ :=
        old.exists_marked_arc_resolution hf he hF hFopen rim hboundary basepath houtside
          hin hfront (Nat.pos_of_ne_zero hzero)
      obtain ⟨g', rim'', path'', hg', hg'R, hg'r, hg'F, hg'front, hg'out, hzero',
        hcircle', model', hemb⟩ := ih (doubleBoundaryComponentCount g D2 Q2)
          (hn ▸ hless) model hg rim' hgr path' hgout hgR hgfront rfl
      exact ⟨g', rim'', path'', hg', hg'R, hg'r, hg'F, hg'front, hg'out, hzero',
        hcircle'.trans hcircle, model', hemb⟩

end PoincareConjecture.M76.Dehn
