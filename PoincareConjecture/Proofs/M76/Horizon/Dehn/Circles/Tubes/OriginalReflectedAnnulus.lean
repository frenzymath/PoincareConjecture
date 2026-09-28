import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentReflectedAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentCyclicTube

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem ComponentBranchModel.nonempty_original_reflected_annulus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) (hcore : D.core ⊆ interior R)
    (hf : PolyhedralPLInCharts e f (closedBall (0 : V2) 1))
    (hin : MapsTo f (closedBall (0 : V2) 1) R)
    (hfront : ∀ x ∈ closedBall (0 : V2) 1, f x ∈ frontier R ↔ x ∈ sphere (0 : V2) 1)
    (hself : old.mate i = i) {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    Nonempty (ComponentReflectionAnnulusData old i L d) := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨m, P, hPi, hP, hPs, _⟩ : ∃ (m : ℕ) (P : Polygon V2 (m + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ = old.pieces i ∧
      Disjoint (old.pieces i) (sphere (0 : V2) 1) := by
    rcases old.models i with hball | hcircle
    · exact ((old.exists_interval_arc_parameters hf hin hfront i hball).1 hself).elim
    · exact hcircle
  obtain ⟨n, p, hpi, _hP, hpv, _hpbd, hpf, ⟨C⟩⟩ :=
    D.exists_selfpaired_circle_blocks hcore hf hin hfront hself
  obtain ⟨frame, closing, sigma, _hframe, _hclosing, _hPL, _himage,
      hlocalPL, hlocalMaps, _hblock, hcoords, _hdisk, haxis, haxisImage, hfib⟩ :=
    C.exists_cyclic_map D hcore p hpi hpv hpf
  let t : Fin (n + 4) → ℝ := fun k => k.val
  have ht : StrictMono t := fun _ _ h => Nat.cast_lt.mpr h
  let K := fun k : Fin (n + 3) => D.complex.barycentricDualBlock {p k}
  have hgeometry := C.local_source_geometry D p hpv
  refine D.nonempty_reflected_annulus_of_cyclic_map hself hcore hfront t ht K
    (fun k => (hgeometry k).1) (fun k => (hgeometry k).2.1) C.x C.y C.chart
    (fun k => (hgeometry k).2.2) sigma
    (fun k => by
      simpa only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hlocalPL k)
    (fun k => by
      simpa only [t, K, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hlocalMaps k)
    (fun k => (frame k).sheetPermutation)
    (fun k j z hz => by
      apply hcoords k j z
      simpa only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hz)
    closing ?_ ?_ ?_ P hP hPi hPs hd hwidth
  · simpa [t, Nat.add_assoc, add_assoc] using hfib
  · simpa [t, Nat.add_assoc, add_assoc] using haxis
  · simpa [t, Nat.add_assoc, add_assoc] using haxisImage

end PoincareConjecture.M76.Dehn
