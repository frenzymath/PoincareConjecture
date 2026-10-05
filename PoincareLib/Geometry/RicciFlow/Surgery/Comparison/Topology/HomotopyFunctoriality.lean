import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Topology.HomotopyExtension
import PoincareLib.Topology.Homotopy.Groups.HomotopyPostcomposition
/-!
# The actual induced map of a homotopy equivalence

This file proves bijectivity of cubical postcomposition between simply
connected spaces. The inverse map may move the basepoint: disk homotopy
extension supplies the correction, and the boundary trace is then removed.
Sources: Hatcher, Section 4.1, pp. 341--342; Morgan--Tian, pp. 430--431.
-/

set_option autoImplicit false

open scoped Topology unitInterval

universe u v

namespace PoincareMT.SurgeryComparison.Topology

noncomputable section

open Poincare.Topology

/-- A homotopy whose entire cube boundary follows one specified path.
This records Hatcher's moving-basepoint homotopies, Section 4.1, p. 341. -/
structure GenLoopBoundaryHomotopy
    {X : Type u} [TopologicalSpace X] {n : ℕ} {x y : X}
    (a : GenLoop (Fin n) X x) (b : GenLoop (Fin n) X y)
    extends a.val.Homotopy b.val where
  /-- The common value on the whole boundary at each time. -/
  trace : Path x y
  /-- Every spatial boundary point follows the trace. -/
  boundary_eq : ∀ (t : unitInterval) (z : Cube.boundary (Fin n)),
    toHomotopy (t, z.val) = trace t

namespace GenLoopBoundaryHomotopy

variable {X : Type u} [TopologicalSpace X] {n : ℕ} {x y z : X}
variable {a : GenLoop (Fin n) X x} {b : GenLoop (Fin n) X y}
variable {c : GenLoop (Fin n) X z}

/-- Reverse a moving-basepoint homotopy; Hatcher, Section 4.1, p. 341. -/
def symm (H : GenLoopBoundaryHomotopy a b) : GenLoopBoundaryHomotopy b a where
  toHomotopy := H.toHomotopy.symm
  trace := H.trace.symm
  boundary_eq _t q := H.boundary_eq _ q

/-- Concatenate moving-basepoint homotopies; Hatcher, Section 4.1, p. 341. -/
def trans (H : GenLoopBoundaryHomotopy a b) (K : GenLoopBoundaryHomotopy b c) :
    GenLoopBoundaryHomotopy a c where
  toHomotopy := H.toHomotopy.trans K.toHomotopy
  trace := H.trace.trans K.trace
  boundary_eq t q := by
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · exact H.boundary_eq _ q
    · exact K.boundary_eq _ q

/-- A relative homotopy has constant boundary trace; Hatcher, Section 4.1,
p. 340. -/
def ofHomotopyRel {b : GenLoop (Fin n) X x} (H : a.val.HomotopyRel b.val
    (Cube.boundary (Fin n))) : GenLoopBoundaryHomotopy a b where
  toHomotopy := H.toHomotopy
  trace := Path.refl x
  boundary_eq t q := (H.eq_fst t q.property).trans (a.property q.val q.property)

/-- A moving-basepoint homotopy in a simply connected space determines a
relative homotopy when its endpoint basepoints agree; Hatcher, p. 342. -/
theorem homotopic [SimplyConnectedSpace X] {b : GenLoop (Fin n) X x}
    (H : GenLoopBoundaryHomotopy a b) : GenLoop.Homotopic a b :=
  homotopicRel_of_uniform_boundary_trace a b H.toHomotopy H.trace H.boundary_eq

/-- Applying a continuous map also applies it to the boundary trace;
Hatcher, Section 4.1, pp. 341--342. -/
def postcomp {Y : Type v} [TopologicalSpace Y]
    {a : GenLoop (Fin (n + 1)) X x} {b : GenLoop (Fin (n + 1)) X y}
    (H : GenLoopBoundaryHomotopy a b) (f : C(X, Y)) :
    GenLoopBoundaryHomotopy (genLoopPostcomp n f x a) (genLoopPostcomp n f y b) where
  toHomotopy := (ContinuousMap.Homotopy.refl f).comp H.toHomotopy
  trace := H.trace.map f.continuous
  boundary_eq t q := congrArg f (H.boundary_eq t q)

/-- A homotopy of maps induces a moving-basepoint homotopy of each cube;
Hatcher, Section 4.1, p. 342. -/
def ofMapHomotopy {Y : Type v} [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
    (a : GenLoop (Fin (n + 1)) X x) :
    GenLoopBoundaryHomotopy (genLoopPostcomp n f x a) (genLoopPostcomp n g x a) where
  toHomotopy := H.compContinuousMap a.val
  trace :=
    { toFun := fun t => H (t, x)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := H.apply_zero x
      target' := H.apply_one x }
  boundary_eq t q := congrArg (fun w => H (t, w)) (a.property q.val q.property)

/-- Move the basepoint of a generalized loop along a specified path by
homotopy extension; Hatcher, Section 4.1, p. 341. -/
theorem exists_of_path (a : GenLoop (Fin n) X x) (p : Path x y) :
    ∃ b : GenLoop (Fin n) X y, Nonempty (GenLoopBoundaryHomotopy a b) := by
  let B : C(unitInterval × Cube.boundary (Fin n), X) :=
    p.toContinuousMap.comp ⟨Prod.fst, continuous_fst⟩
  obtain ⟨F, hF0, hFs⟩ := exists_cube_boundary_homotopy_extension n a.val B (by
    intro q
    exact p.source.trans (a.property q.val q.property).symm)
  let b : GenLoop (Fin n) X y :=
    ⟨F.comp ⟨fun q => (1, q), continuous_const.prodMk continuous_id⟩, by
      intro q hq
      exact (hFs 1 ⟨q, hq⟩).trans p.target⟩
  refine ⟨b, ⟨{
    toContinuousMap := F
    map_zero_left := hF0
    map_one_left := fun _ => rfl
    trace := p
    boundary_eq := hFs }⟩⟩

end GenLoopBoundaryHomotopy

/-- The literal cubical postcomposition induced by a homotopy equivalence
of simply connected spaces is bijective. The inverse need not preserve
the chosen basepoint. Hatcher, p. 342; Morgan--Tian, pp. 430--431. -/
theorem homotopyGroupPostcomp_bijective_of_homotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (n : ℕ) (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (homotopyGroupPostcomp n e.toFun x) := by
  obtain ⟨L⟩ := e.left_inv
  obtain ⟨R⟩ := e.right_inv
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        obtain ⟨H⟩ := Quotient.exact hab
        let A := GenLoopBoundaryHomotopy.ofMapHomotopy L x a
        let B := GenLoopBoundaryHomotopy.ofMapHomotopy L x b
        let J := (GenLoopBoundaryHomotopy.ofHomotopyRel H).postcomp e.invFun
        exact Quotient.sound ((A.symm.trans J).trans B).homotopic
  · intro q
    induction q using Quotient.inductionOn with | h q =>
      let p : Path (e.invFun (e.toFun x)) x :=
        { toFun := fun t => L (t, x)
          continuous_toFun := L.continuous.comp (continuous_id.prodMk continuous_const)
          source' := L.apply_zero x
          target' := L.apply_one x }
      obtain ⟨a, ⟨A⟩⟩ := GenLoopBoundaryHomotopy.exists_of_path
        (genLoopPostcomp n e.invFun (e.toFun x) q) p
      let B := GenLoopBoundaryHomotopy.ofMapHomotopy R (e.toFun x) q
      exact ⟨Quotient.mk _ a, Quotient.sound (B.symm.trans (A.postcomp e.toFun)).homotopic.symm⟩

end

end PoincareMT.SurgeryComparison.Topology
