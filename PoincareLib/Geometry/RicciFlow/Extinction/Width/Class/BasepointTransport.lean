import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Identification
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Basic

/-!
# Path-aware higher homotopy transport

The ancestry and surgery interfaces select arbitrary points in the relevant
components.  A diffeomorphism therefore supplies a path from the transported
point to the selected target point, not generally an equality.  This file
records the missing higher basepoint service without introducing an abstract
equivalence as an oracle: the induced map is always the quotient map of an
explicit `GenLoop` whiskering operation, together with its quotient-respect,
path-coherence, group, and continuous-map naturality laws.

M59's complete theorem exports existence of this service; its single
admission owns the whiskering construction and laws. Keeping it
as a named service makes that obligation visible to M57/M67/M69 and prevents
point equalities or algebraically twisted transports from being smuggled into
their contracts.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology unitInterval

universe u

namespace PoincareMT

structure M59GenLoopWhisker (X : Type u) [TopologicalSpace X] (n : ℕ) where
  whisker : ∀ {x y : X}, Path x y →
    GenLoop (Fin n) X x → GenLoop (Fin n) X y
  respects_homotopy : ∀ {x y : X} (p : Path x y)
    {a b : GenLoop (Fin n) X x},
    GenLoop.Homotopic a b →
      GenLoop.Homotopic (whisker p a) (whisker p b)

namespace M59GenLoopWhisker

def map {X : Type u} [TopologicalSpace X] {n : ℕ}
    (W : M59GenLoopWhisker X n) {x y : X} (p : Path x y) :
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n X y :=
  Quotient.map (W.whisker p) (by
    intro a b h
    exact W.respects_homotopy p h)

end M59GenLoopWhisker

/--
The path transport laws required by the later width and surgery nodes. The map
is definitionally induced by `M59GenLoopWhisker.map`; no free `MulEquiv` or
arbitrary homotopy-group function is accepted here. The identity and
multiplication fields make the map a group homomorphism at the dimensions used
later, while the reverse-path field supplies its inverse.
-/
structure M59HigherBasepointTransport (X : Type u) [TopologicalSpace X]
    (n : ℕ) where
  whisker : M59GenLoopWhisker X n
  map_refl : ∀ {x : X} (a : HomotopyGroup.Pi n X x),
    M59GenLoopWhisker.map whisker (Path.refl x) a = a
  map_trans : ∀ {x y z : X} (p : Path x y) (q : Path y z)
    (a : HomotopyGroup.Pi n X x),
    M59GenLoopWhisker.map whisker (p.trans q) a =
      M59GenLoopWhisker.map whisker q
        (M59GenLoopWhisker.map whisker p a)
  map_left_inverse : ∀ {x y : X} (p : Path x y)
    (a : HomotopyGroup.Pi n X x),
    M59GenLoopWhisker.map whisker p.symm
      (M59GenLoopWhisker.map whisker p a) = a
  map_one : ∀ {x y : X} (p : Path x y) [Nonempty (Fin n)],
    M59GenLoopWhisker.map whisker p (1 : HomotopyGroup.Pi n X x) = 1
  map_mul : ∀ {x y : X} (p : Path x y) [Nonempty (Fin n)]
    (a b : HomotopyGroup.Pi n X x),
    M59GenLoopWhisker.map whisker p (a * b) =
      M59GenLoopWhisker.map whisker p a *
        M59GenLoopWhisker.map whisker p b

namespace M59HigherBasepointTransport

abbrev map {X : Type u} [TopologicalSpace X] {n : ℕ}
    (B : M59HigherBasepointTransport X n) {x y : X}
    (p : Path x y) : HomotopyGroup.Pi n X x → HomotopyGroup.Pi n X y :=
  M59GenLoopWhisker.map B.whisker p

end M59HigherBasepointTransport

/-- One coherent higher-basepoint service, usable at both pi2 and pi3. -/
structure M59HigherBasepointTransportService where
  transport : ∀ (n : ℕ) {X : Type u} [TopologicalSpace X],
    M59HigherBasepointTransport X n
  naturality :
    ∀ (n : ℕ) {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (f : ContinuousMap X Y) {x y : X} (p : Path x y)
      (a : HomotopyGroup.Pi n X x),
      M59HigherBasepointTransport.map
          (transport n (X := Y)) (p.map f.continuous)
          (surgeryHomotopyMap (n := n) f (rfl : f x = f x) a) =
        surgeryHomotopyMap (n := n) f (rfl : f y = f y)
          (M59HigherBasepointTransport.map
            (transport n (X := X)) p a)

/-! A path of constant C1 loops must be tied pointwise to the original point
path.  This keeps the loop-space basepoint change semantic rather than letting
the caller provide an unrelated path between constant loops. -/
structure M59ConstantLoopPath {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {x y : M} (p : Path x y) where
  loop : Path (constantC1Loop x) (constantC1Loop y)
  pointwise : ∀ (t : I) (z : LoopCircle), loop t z = p t

end PoincareMT
