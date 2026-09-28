import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.TerminalData

noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def includeGeometry (d : SaddleLevel.TerminalSaddleGeometry M P p e) :
    TerminalSaddleGeometry M P p e :=
  { d with model_kind := d.model_kind.elim Or.inl (fun h => Or.inr (Or.inl h)) }

def includeData (d : SaddleLevel.TerminalSaddleData M P p e) :
    TerminalSaddleData M P p e :=
  { d with toTerminalSaddleGeometry := includeGeometry d.toTerminalSaddleGeometry }

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
