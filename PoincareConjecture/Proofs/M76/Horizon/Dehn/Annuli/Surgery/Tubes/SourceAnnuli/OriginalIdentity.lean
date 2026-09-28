import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.SourceAnnuli.Identity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.ComponentCyclicTube
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.CircleBlocks

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem ComponentBranchModel.nonempty_original_identity_annuli
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hcore : D.core ⊆ interior R)
    (hfront : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ frontier S)
    (hmate : old.mate i ≠ i) {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    Nonempty (ComponentIdentityAnnuliData (e := e) (R := R) old i L d) := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨n, p, hpi, _hP, hpv, _hpbd, hpf, ⟨C⟩⟩ :=
    D.exists_circle_blocks hcore
  obtain ⟨frame, closing, sigma, _hframe, _hclosing, _hPL, _himage,
      hlocalPL, hlocalMaps, _hblock, hcoords, _hdisk, haxis, haxisImage, hfib⟩ :=
    C.exists_cyclic_map D hcore p hpi hpv hpf
  let t : Fin (n + 4) → ℝ := fun k => k.val
  have ht : StrictMono t := fun _ _ h => Nat.cast_lt.mpr h
  let K := fun k : Fin (n + 3) => D.complex.barycentricDualBlock {p k}
  have hgeometry := C.local_source_geometry D p hpv
  refine D.nonempty_identity_annuli_of_cyclic_map hmate hcore t ht K
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
    closing ?_ ?_ ?_ hfront hd hwidth
  · simpa [t, Nat.add_assoc, add_assoc] using hfib
  · simpa [t, Nat.add_assoc, add_assoc] using haxis
  · simpa [t, Nat.add_assoc, add_assoc] using haxisImage

theorem SourceCircleDecomposition.nonempty_identity_annuli
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    (Q : SimplicialComplex ℝ P2) (hQ : Q.faces.Finite) (hQS : Q.space = S)
    (old : SourceCircleDecomposition f S) (hf : PolyhedralPLInCharts e f S)
    (he : PLDomain e R)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y))
    (hinterior : MapsTo f (doubleLocusOn f S) (interior R))
    (hfront : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ frontier S)
    (i : old.Index) (hmate : old.mate i ≠ i)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    Nonempty (ComponentIdentityAnnuliData (e := e) (R := R) old i L d) := by
  obtain ⟨D, hcore, _⟩ :=
    old.exists_interior_circle_model Q hQ hQS hf he hcross hinterior i
  exact D.nonempty_original_identity_annuli hcore hfront hmate hd hwidth

end PoincareConjecture.M76.Dehn.Annuli
