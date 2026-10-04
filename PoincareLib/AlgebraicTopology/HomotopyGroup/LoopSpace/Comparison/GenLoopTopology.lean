import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Paths in spaces of cubical loops

The compact-open topology identifies paths of based cubes with homotopies
relative to their boundary. This makes the loop-space adjunction compatible
with the actual representatives. Source: Hatcher, Section 4.1, pp. 340-342.
-/

set_option autoImplicit false

open scoped Topology unitInterval

namespace GenLoop

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- A homotopy relative to the cube boundary is a path of based cubes.
Source: Hatcher, Section 4.1, pp. 340-342. -/
def pathOfHomotopy {f g : GenLoop N X x}
    (H : f.val.HomotopyRel g.val (Cube.boundary N)) : Path f g where
  toFun t := ⟨H.toContinuousMap.curry t, fun v hv =>
    (H.eq_fst t hv).trans (GenLoop.boundary f v hv)⟩
  continuous_toFun := H.toContinuousMap.curry.continuous.subtype_mk _
  source' := by ext v; exact H.apply_zero v
  target' := by ext v; exact H.apply_one v

/-- A path of based cubes gives a homotopy relative to their boundary.
Source: Hatcher, Section 4.1, pp. 340-342. -/
def homotopyOfPath {f g : GenLoop N X x} (p : Path f g) :
    f.val.HomotopyRel g.val (Cube.boundary N) where
  toFun q := p q.1 q.2
  continuous_toFun := by fun_prop
  map_zero_left := by intro v; rw [p.source]; rfl
  map_one_left := by intro v; rw [p.target]; rfl
  prop' := fun t v hv =>
    (GenLoop.boundary (p t) v hv).trans (GenLoop.boundary f v hv).symm

/-- Based cube homotopy is precisely path connectedness in the cube space.
Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem homotopic_iff_nonempty_path {f g : GenLoop N X x} :
    Homotopic f g ↔ Nonempty (Path f g) :=
  ⟨Nonempty.map pathOfHomotopy, Nonempty.map homotopyOfPath⟩

/-- Vanishing of the cubical homotopy set makes its representative space
path connected. Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem pathConnectedSpace_of_subsingleton
    (h : Subsingleton (HomotopyGroup N X x)) : PathConnectedSpace (GenLoop N X x) where
  nonempty := inferInstance
  joined f g := homotopic_iff_nonempty_path.mp (Quotient.exact (h.elim ⟦f⟧ ⟦g⟧))

end GenLoop

namespace HomotopyGroup

/-- A homeomorphism of spaces of based cubes descends to their homotopy sets.
Source: Hatcher, Section 4.1, pp. 340-342. -/
def equivOfGenLoopHomeomorph {N P X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (e : GenLoop N X x ≃ₜ GenLoop P Y y) :
    HomotopyGroup N X x ≃ HomotopyGroup P Y y :=
  Quotient.congr e.toEquiv fun f g => by
    change GenLoop.Homotopic f g ↔ GenLoop.Homotopic (e f) (e g)
    rw [GenLoop.homotopic_iff_nonempty_path, GenLoop.homotopic_iff_nonempty_path]
    constructor
    · exact Nonempty.map (fun p => p.map e.continuous)
    · exact Nonempty.map (fun p =>
        (p.map e.symm.continuous).cast (e.symm_apply_apply f).symm
          (e.symm_apply_apply g).symm)

end HomotopyGroup
