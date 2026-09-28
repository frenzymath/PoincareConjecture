import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Matching
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Levels.Terminal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Matching
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Filling
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Decomposition







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies











noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1


def terminalEndCap {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (ends : SphereSurgeryCoreCap.AnnularEndFamily v g B C)
    (i : ends.EndIndex) : Set S2 :=
  ends.endRegion i ∪ match i with
    | .inl d => d.1.1.chart '' closedBall 0 1
    | .inr d => d.1.1.chart '' closedBall 0 1


structure TerminalSaddleGeometry
    {f : S2 → E3} (M : SphereMorseReduction f) {g : S2 → E3}
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (p : S2) (e : OpenPartialHomeomorph E2 S2) where
  D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞
  frame : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞
  frame_height : ∀ y, frame y 2 = inner Real (M.v : E3) y
  frame_isometry : Isometry frame
  frame_zero : frame 0 = 0
  r : Real
  delta : Real
  r_pos : 0 < r
  square_source : closedSquare r ⊆ e.source
  delta_pos : 0 < delta
  delta_lt : delta < r ^ 2
  D_height : ∀ y, inner Real (M.v : E3) (D y) = inner Real (M.v : E3) y
  strips : Fin 2 → OpenPartialHomeomorph (Real × Real) S2
  a : Fin 2 → Real
  b : Fin 2 → Real
  leftContact : Fin 2 → Real → Real
  rightContact : Fin 2 → Real → Real
  flattened_levels : ∀ t ∈ Icc (-delta) delta,
    (∀ i, ContinuousAt (leftContact i) t ∧ ContinuousAt (rightContact i) t ∧
      a i < leftContact i t ∧ leftContact i t < rightContact i t ∧
      rightContact i t < b i) ∧
    (D ∘ g) '' {q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p) + t} =
      (D ∘ g ∘ e) '' (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ∪
      (⋃ i, (fun s => g (strips i (s, 0)) + t • (M.v : E3)) '' Icc (a i) (b i)) ∧
    (D ∘ g) '' ({q | inner Real (M.v : E3) (g q) =
      inner Real (M.v : E3) (g p) + t} \ e '' openSquare r) =
      ⋃ i, (fun s => g (strips i (s, 0)) + t • (M.v : E3)) ''
        Icc (leftContact i t) (rightContact i t)
  model : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞
  model_kind : model = Saddle.shear ∨ model = Saddle.Nested.shear (3/10)
  transport : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞
  scale : Real
  scale_pos : 0 < scale
  modelChart : OpenPartialHomeomorph E2 S2
  modelChart_zero : 0 ∈ modelChart.source
  modelChart_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ modelChart modelChart.source
  modelChart_symm_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ modelChart.symm modelChart.target
  matchingRadius : Real
  matchingRadius_pos : 0 < matchingRadius
  matching_source : closedBall 0 matchingRadius ⊆ modelChart.source
  matching_actual_source : ∀ x ∈ closedBall 0 matchingRadius,
    Real.sqrt scale • x ∈ e.source
  transport_height : ∀ y, inner Real (M.v : E3) (transport y) =
    inner Real (M.v : E3) (g p) + scale * (y 2 - model (modelChart 0) 2)
  matching : ∀ x ∈ closedBall 0 matchingRadius,
    transport (model (modelChart x)) = g (e (Real.sqrt scale • x))
  ends : SphereSurgeryCoreCap.AnnularEndFamily (M.v : E3) g
    ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}) P.core
  eta : Real
  eta_pos : 0 < eta
  eta_lt : eta < delta
  lowerCut_eq : ends.lowerCut = inner Real (M.v : E3) (g p) - eta
  upperCut_eq : ends.upperCut = inner Real (M.v : E3) (g p) + eta
  labels : Fin 3 ≃ ends.EndIndex
  modelSeed : Fin 3 → S2
  modelSeed_outside : ∀ i, inner Real (M.v : E3)
    (transport (model (modelSeed i))) ∉ Icc ends.lowerCut ends.upperCut

namespace TerminalSaddleGeometry
variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}
def flatten (d : TerminalSaddleGeometry M P p e) := d.D.trans d.frame
def filledModel (d : TerminalSaddleGeometry M P p e) := d.model.trans d.transport
def I (d : TerminalSaddleGeometry M P p e) := Icc d.ends.lowerCut d.ends.upperCut
def A (d : TerminalSaddleGeometry M P p e) (z : Real) : Set E2 :=
  {x | Saddle.toE3 x z ∈ d.flatten '' range g}
def B (d : TerminalSaddleGeometry M P p e) (z : Real) : Set E2 :=
  {x | Saddle.toE3 x z ∈ d.flatten '' (d.filledModel '' sphere (0 : E3) 1)}
def C (d : TerminalSaddleGeometry M P p e) (i : Fin 3) : Set E3 :=
  (d.flatten ∘ g) '' terminalEndCap d.ends (d.labels i)
def modelDomain (d : TerminalSaddleGeometry M P p e) (i : Fin 3) : Set S2 :=
  closure (connectedComponentIn
    {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I} (d.modelSeed i))
def modelCaps (d : TerminalSaddleGeometry M P p e) (i : Fin 3) : Set E3 :=
  (fun q : S2 => d.flatten (d.filledModel q)) '' d.modelDomain i
def actualBand (d : TerminalSaddleGeometry M P p e) : Set E3 :=
  ⋃ z ∈ d.I, Saddle.slice (d.A z) z
def modelBand (d : TerminalSaddleGeometry M P p e) : Set E3 :=
  ⋃ z ∈ d.I, Saddle.slice (d.B z) z
end TerminalSaddleGeometry


structure TerminalSaddleData
    {f : S2 → E3} (M : SphereMorseReduction f) {g : S2 → E3}
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (p : S2) (e : OpenPartialHomeomorph E2 S2)
    extends TerminalSaddleGeometry M P p e where
  actualDisk : Fin 3 → OpenPartialHomeomorph E2 S2
  actualDisk_source : ∀ i, closedBall 0 1 ⊆ (actualDisk i).source
  actualDisk_smooth : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (actualDisk i) (actualDisk i).source
  actualDisk_symm_smooth : ∀ i,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (actualDisk i).symm (actualDisk i).target
  actualDisk_image : ∀ i, actualDisk i '' closedBall 0 1 = terminalEndCap ends (labels i)
  modelDisk : Fin 3 → OpenPartialHomeomorph E2 S2
  modelDisk_source : ∀ i, closedBall 0 1 ⊆ (modelDisk i).source
  modelDisk_smooth : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (modelDisk i) (modelDisk i).source
  modelDisk_symm_smooth : ∀ i,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (modelDisk i).symm (modelDisk i).target
  modelDisk_image : ∀ i, modelDisk i '' closedBall 0 1 = toTerminalSaddleGeometry.modelDomain i
  actual_decomposition : toTerminalSaddleGeometry.flatten '' range g =
    toTerminalSaddleGeometry.actualBand ∪ ⋃ i, toTerminalSaddleGeometry.C i
  model_decomposition : toTerminalSaddleGeometry.flatten ''
    (toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) =
      toTerminalSaddleGeometry.modelBand ∪ ⋃ i, toTerminalSaddleGeometry.modelCaps i
  actual_boundary : ∀ i, toTerminalSaddleGeometry.C i ∩ toTerminalSaddleGeometry.actualBand =
    (toTerminalSaddleGeometry.flatten ∘ g ∘ actualDisk i) '' sphere (0 : E2) 1
  model_boundary : ∀ i,
    toTerminalSaddleGeometry.modelCaps i ∩ toTerminalSaddleGeometry.modelBand =
      (fun x => toTerminalSaddleGeometry.flatten
        (toTerminalSaddleGeometry.filledModel (modelDisk i x))) '' sphere (0 : E2) 1
  actual_disjoint : Pairwise (fun i j =>
    Disjoint (toTerminalSaddleGeometry.C i) (toTerminalSaddleGeometry.C j))
  model_disjoint : Pairwise (fun i j =>
    Disjoint (toTerminalSaddleGeometry.modelCaps i) (toTerminalSaddleGeometry.modelCaps j))

def planarHeightMap
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (t : Real) (y : E3) : E3 :=
  Saddle.toE3 (Φ t (y 2) (Saddle.toE2 y)) (y 2)


end Poincare.Manifold.Schoenflies.SaddleLevel

end

end M38Schoenflies
