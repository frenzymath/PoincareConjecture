import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.LoopClassTransport
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HomotopyLoopWhisker










set_option autoImplicit false

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}



theorem map_loop_homotopic_refl (H : f.Homotopy g) {x : X} (p : Path x x)
    (hp : (p.map g.continuous).Homotopic (Path.refl (g x))) :
    (p.map f.continuous).Homotopic (Path.refl (f x)) := by
  have hg : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.map g.continuous)) = 1 :=
    Path.Homotopic.Quotient.eq.mpr hp
  have htrace := ((H.evalAt x).whiskeredLoopClass_eq_one_iff (p.map g.continuous)).mpr hg
  apply Path.Homotopic.Quotient.exact
  rw [H.loop_quotient_eq_whisker p]
  exact htrace



theorem all_map_loops_homotopic_refl (H : f.Homotopy g)
    (hg : ∀ (x : X) (p : Path x x), (p.map g.continuous).Homotopic (Path.refl (g x))) :
    ∀ (x : X) (p : Path x x), (p.map f.continuous).Homotopic (Path.refl (f x)) :=
  fun x p => H.map_loop_homotopic_refl p (hg x p)

end ContinuousMap.Homotopy
