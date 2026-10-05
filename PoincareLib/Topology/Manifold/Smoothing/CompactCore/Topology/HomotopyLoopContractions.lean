import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Topology.LoopClassTransport
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.HomotopyLoopWhisker

/-!
# Transport loop contractions through an actual map homotopy

The basepoint trace of the given homotopy identifies the initial mapped
loop class with the final class conjugated by that trace. In particular,
a contraction of the final mapped loop contracts the initial mapped loop.
See Dehn derivation 023, section 4, for the basepoint-trace identity.
-/

set_option autoImplicit false

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}

/-- Transport a contraction of one actual mapped loop backwards through
the actual map homotopy, including its moving basepoint. -/
theorem map_loop_homotopic_refl (H : f.Homotopy g) {x : X} (p : Path x x)
    (hp : (p.map g.continuous).Homotopic (Path.refl (g x))) :
    (p.map f.continuous).Homotopic (Path.refl (f x)) := by
  have hg : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.map g.continuous)) = 1 :=
    Path.Homotopic.Quotient.eq.mpr hp
  have htrace := ((H.evalAt x).whiskeredLoopClass_eq_one_iff (p.map g.continuous)).mpr hg
  apply Path.Homotopic.Quotient.exact
  rw [H.loop_quotient_eq_whisker p]
  exact htrace

/-- An actual homotopy transports the property that every mapped loop
contracts, without imposing a fixed-basepoint condition on the homotopy. -/
theorem all_map_loops_homotopic_refl (H : f.Homotopy g)
    (hg : ∀ (x : X) (p : Path x x), (p.map g.continuous).Homotopic (Path.refl (g x))) :
    ∀ (x : X) (p : Path x x), (p.map f.continuous).Homotopic (Path.refl (f x)) :=
  fun x p => H.map_loop_homotopic_refl p (hg x p)

end ContinuousMap.Homotopy
