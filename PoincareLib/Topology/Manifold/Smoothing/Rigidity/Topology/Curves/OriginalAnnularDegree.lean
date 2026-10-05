import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.OriginalAnnulusMark
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.SignedAnnularDegree
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.SquareRimFilling
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.SourceAnnularMark
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.IteratedCoreDegree

/-!
# Primitive degree comparison in an original annular mark

The actual core retraction transports the constructed original-PL curve
homotopy to a circle homeomorphism. A homotopy in the source boundary to a
positive multiple of the same core then forces multiplicity one.
-/

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

/-- The actual marked curve in the boundary, with the fixed whole circle
parameter and its original pointwise values. -/
noncomputable def originalAnnularMarkedCircle
    {X : Type*} [TopologicalSpace X] {B S : Set X}
    (A : Ann ≃ₜ B) (hBS : B ⊆ S)
    (gamma : C(Q2, originalAnnulusOpenMark A)) : C(Circle, S) :=
  (ContinuousMap.inclusion ((originalAnnulusOpenMark_subset A).trans hBS)).comp
    (gamma.comp ⟨annulusSquareRimParameter, annulusSquareRimParameter.continuous⟩)

/-- The actual core retraction of an original boundary annulus sends every
essential embedded original-PL curve in its open mark to the homotopy class
of a circle homeomorphism. Essentiality is tested in the retained region. -/
theorem exists_original_annular_projection_homeomorph_homotopy
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {B S R : Set X} (A : Ann ≃ₜ B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ x : Ann, j x = (A x : X))
    (hBS : B ⊆ S) (hSR : S ⊆ R)
    (c : C(S, Circle)) (hcore : ∀ z, c (PeriodicSquare.sourceAnnularCore A hBS z) = z)
    (gamma : C(Q2, originalAnnulusOpenMark A)) (hinj : Function.Injective gamma)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma x : X))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map
        (((ContinuousMap.inclusion ((originalAnnulusOpenMark_subset A).trans
          (hBS.trans hSR))).comp gamma).continuous))) ≠ 1) :
    ∃ q : Circle ≃ₜ Circle,
      Nonempty ((c.comp (originalAnnularMarkedCircle A hBS gamma)).Homotopy
        ⟨q, q.continuous⟩) := by
  have hdepth (x : originalAnnulusOpenMark A) :
      -1 < depth 8 (A.symm ⟨x, originalAnnulusOpenMark_subset A x.property⟩ : ℝ × ℝ) ∧
      depth 8 (A.symm ⟨x, originalAnnulusOpenMark_subset A x.property⟩ : ℝ × ℝ) < 1 :=
    (mem_originalAnnulusOpenMark_iff A _).mp x.property
  obtain ⟨q, ⟨H⟩⟩ := exists_originalPL_annular_mark_core_homotopy
    e hcompat A j hj hjval (originalAnnulusOpenMark_subset A) (hBS.trans hSR)
    hdepth gamma hinj g hg hgval hessential
  let i : C(B, S) := ContinuousMap.inclusion hBS
  refine ⟨annulusSquareRimParameter.trans q, ⟨{
    toFun := fun z => c (i (H (z.1, annulusSquareRimParameter z.2)))
    continuous_toFun := c.continuous.comp (i.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk
        (annulusSquareRimParameter.continuous.comp continuous_snd))))
    map_zero_left := ?_
    map_one_left := ?_
  }⟩⟩
  · intro z
    rw [H.apply_zero]
    rfl
  · intro z
    rw [H.apply_one]
    exact hcore (q (annulusSquareRimParameter z))

/-- A homotopy in the actual source boundary from the embedded marked curve
to a positive multiple of its own core forces that multiplicity to be one.
The projected circle homotopy is constructed from the given boundary
homotopy and the actual core retraction. -/
theorem original_annular_positive_degree_eq_one
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {B S R : Set X} (A : Ann ≃ₜ B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ x : Ann, j x = (A x : X))
    (hBS : B ⊆ S) (hSR : S ⊆ R)
    (c : C(S, Circle)) (hcore : ∀ z, c (PeriodicSquare.sourceAnnularCore A hBS z) = z)
    (gamma : C(Q2, originalAnnulusOpenMark A)) (hinj : Function.Injective gamma)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma x : X))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map
        (((ContinuousMap.inclusion ((originalAnnulusOpenMark_subset A).trans
          (hBS.trans hSR))).comp gamma).continuous))) ≠ 1)
    (n : ℕ) (hn : 0 < n)
    (Hn : (originalAnnularMarkedCircle A hBS gamma).Homotopy
      ((PeriodicSquare.sourceAnnularCore A hBS).comp ⟨fun z => n • z, by fun_prop⟩)) :
    n = 1 := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨q, ⟨Hq⟩⟩ := exists_original_annular_projection_homeomorph_homotopy
    e hcompat A j hj hjval hBS hSR c hcore gamma hinj g hg hgval hessential
  have Hp : (c.comp (originalAnnularMarkedCircle A hBS gamma)).Homotopy
      ⟨fun z => n • z, by fun_prop⟩ := {
    toFun := fun z => c (Hn z)
    continuous_toFun := c.continuous.comp Hn.continuous
    map_zero_left := fun z => congrArg c (Hn.apply_zero z)
    map_one_left := by
      intro z
      rw [Hn.apply_one]
      exact hcore (n • z) }
  exact AddCircle.nat_eq_one_of_homotopic_homeomorph
    (c.comp (originalAnnularMarkedCircle A hBS gamma)) q Hq n hn Hp

/-- The terminal-rim non-nullhomotopy predicate implies nontriviality of
its actual complete based square-rim traversal. -/
theorem squareRimLoop_class_ne_one_of_not_nullhomotopic
    {Y : Type*} [TopologicalSpace Y] (gamma : C(Q2, Y))
    (hgamma : ¬ gamma.Nullhomotopic) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1 := by
  intro hn
  exact hgamma (nullhomotopic_of_squareRimLoop gamma (Path.Homotopic.Quotient.eq.mp hn))

/-- Caller-facing degree comparison from the actual terminal rim's
non-nullhomotopy in the retained region and its actual boundary homotopy
to a positive multiple core. -/
theorem original_annular_positive_degree_eq_one_of_not_nullhomotopic
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {B S R : Set X} (A : Ann ≃ₜ B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ x : Ann, j x = (A x : X))
    (hBS : B ⊆ S) (hSR : S ⊆ R)
    (c : C(S, Circle)) (hcore : ∀ z, c (PeriodicSquare.sourceAnnularCore A hBS z) = z)
    (gamma : C(Q2, originalAnnulusOpenMark A)) (hinj : Function.Injective gamma)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma x : X))
    (hessential : ¬ (((ContinuousMap.inclusion
      ((originalAnnulusOpenMark_subset A).trans (hBS.trans hSR))).comp gamma)).Nullhomotopic)
    (n : ℕ) (hn : 0 < n)
    (Hn : (originalAnnularMarkedCircle A hBS gamma).Homotopy
      ((PeriodicSquare.sourceAnnularCore A hBS).comp ⟨fun z => n • z, by fun_prop⟩)) :
    n = 1 :=
  original_annular_positive_degree_eq_one e hcompat A j hj hjval hBS hSR c hcore
    gamma hinj g hg hgval
    (squareRimLoop_class_ne_one_of_not_nullhomotopic _ hessential) n hn Hn

private theorem boundaryLoopIterate_retract_apply
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (i : C(Y, Z)) (r : C(Z, Y)) (h : ∀ y, r (i y) = y)
    {y : Y} (alpha : Path y y) (n : ℕ) (t : unitInterval) :
    r (boundaryLoopIterate (alpha.map i.continuous) n t) =
      boundaryLoopIterate alpha n t := by
  induction n generalizing t with
  | zero => exact h y
  | succ n ih =>
    rw [boundaryLoopIterate, boundaryLoopIterate, Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact h _
    · exact ih _

/-- The literal positive core iterate supplied by the marked singular
annulus has multiplicity one if its marked homotopy ends at an essential
embedded original-PL circle. The circle degree homotopy is constructed
from the exact traversal formula; it is not supplied separately. -/
theorem original_annular_iterated_core_degree_eq_one
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {B S R : Set X} (A : Ann ≃ₜ B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ x : Ann, j x = (A x : X))
    (hBS : B ⊆ S) (hSR : S ⊆ R)
    (c : C(S, Circle)) (hcore : ∀ z, c (PeriodicSquare.sourceAnnularCore A hBS z) = z)
    (gamma gamma₀ : C(Q2, originalAnnulusOpenMark A))
    (H : gamma.Homotopy gamma₀) (hinj : Function.Injective gamma₀)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma₀ x : X))
    (hessential : ¬ (((ContinuousMap.inclusion
      ((originalAnnulusOpenMark_subset A).trans (hBS.trans hSR))).comp gamma₀)).Nullhomotopic)
    (n : ℕ) (hn : 0 < n)
    (htraversal : ∀ t : unitInterval, (gamma (squareRimLoop t) : X) =
      (boundaryLoopIterate ((AddCircle.periodLoop (4 * (8 : ℝ))).map
        (PeriodicSquare.sourceAnnularCore A hBS).continuous) n t : X)) :
    n = 1 := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let inc : C(originalAnnulusOpenMark A, S) :=
    ContinuousMap.inclusion ((originalAnnulusOpenMark_subset A).trans hBS)
  let radial : C(Q2, Circle) := c.comp (inc.comp gamma)
  have hr (t : unitInterval) : radial (squareRimLoop t) =
      boundaryLoopIterate (AddCircle.periodLoop (4 * (8 : ℝ))) n t := by
    have heq : inc (gamma (squareRimLoop t)) =
        boundaryLoopIterate ((AddCircle.periodLoop (4 * (8 : ℝ))).map
          (PeriodicSquare.sourceAnnularCore A hBS).continuous) n t :=
      Subtype.ext (htraversal t)
    change c (inc (gamma (squareRimLoop t))) = _
    rw [heq]
    exact boundaryLoopIterate_retract_apply
      (PeriodicSquare.sourceAnnularCore A hBS) c hcore _ n t
  obtain ⟨Hn⟩ := homotopic_nsmul_of_squareRimLoop_iterate radial n hr
  obtain ⟨q, ⟨Hq₀⟩⟩ := exists_original_annular_projection_homeomorph_homotopy
    e hcompat A j hj hjval hBS hSR c hcore gamma₀ hinj g hg hgval
    (squareRimLoop_class_ne_one_of_not_nullhomotopic _ hessential)
  have Hp : (radial.comp
      ⟨annulusSquareRimParameter, annulusSquareRimParameter.continuous⟩).Homotopy
      (c.comp (originalAnnularMarkedCircle A hBS gamma₀)) := {
    toFun := fun z => c (inc (H (z.1, annulusSquareRimParameter z.2)))
    continuous_toFun := c.continuous.comp (inc.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk
        (annulusSquareRimParameter.continuous.comp continuous_snd))))
    map_zero_left := fun z => congrArg (fun x => c (inc x))
      (H.apply_zero (annulusSquareRimParameter z))
    map_one_left := fun z => congrArg (fun x => c (inc x))
      (H.apply_one (annulusSquareRimParameter z)) }
  exact AddCircle.nat_eq_one_of_homotopic_homeomorph _ q (Hp.trans Hq₀) n hn Hn

end PoincareMT.M76.Dehn
