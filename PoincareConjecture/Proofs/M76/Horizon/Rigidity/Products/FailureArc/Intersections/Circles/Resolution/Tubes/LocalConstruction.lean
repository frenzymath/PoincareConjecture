import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.LocalIdentity

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem nonempty_local_identity_annuli
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hcore : D.core ⊆ interior R)
    (hsourceCore : ∀ x ∈ S, f x ∈ D.core → x ∈ interior S)
    (hmate : old.mate i ≠ i) {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ T : ComponentIdentityAnnuliData (e := e) (R := R) old i L d,
      T.tube '' _root_.Dehn.identityTube L d ⊆ D.core := by
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
  refine nonempty_local_identity_annuli_of_cyclic_map D hmate hcore t ht K
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
    closing ?_ ?_ ?_ hsourceCore hd hwidth
  · simpa [t, Nat.add_assoc, add_assoc] using hfib
  · simpa [t, Nat.add_assoc, add_assoc] using haxis
  · simpa [t, Nat.add_assoc, add_assoc] using haxisImage

theorem exists_identity_annuli_away_source_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    (Q : SimplicialComplex ℝ P2) (hQ : Q.faces.Finite) (hQS : Q.space = S)
    (old : SourceCircleDecomposition f S) (hf : PolyhedralPLInCharts e f S)
    (he : PLDomain e R)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y))
    (i : old.Index) (hmate : old.mate i ≠ i)
    (hselectedR : f '' old.pieces i ⊆ interior R)
    (hselectedFrontier : Disjoint (f '' old.pieces i) (f '' frontier S))
    (O : Set X) (hO : IsOpen O) (hselectedO : f '' old.pieces i ⊆ O)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ T : ComponentIdentityAnnuliData (e := e) (R := R) old i L d,
      T.tube '' _root_.Dehn.identityTube L d ⊆ O := by
  have hS : IsCompact S := hQS ▸ Q.isCompact_space_of_finite hQ
  have hfrontS : frontier S ⊆ S := hS.isClosed.frontier_subset
  have hfront : IsClosed (f '' frontier S) :=
    ((hS.of_isClosed_subset isClosed_frontier hfrontS).image_of_continuousOn
      (hf.continuousOn.mono hfrontS)).isClosed
  let W := (interior R \ f '' frontier S) ∩ O
  have hW : IsOpen W := (isOpen_interior.sdiff hfront).inter hO
  have hselectedW : f '' old.pieces i ⊆ W := fun y hy =>
    ⟨⟨hselectedR hy, fun hh => disjoint_left.mp hselectedFrontier hy hh⟩,hselectedO hy⟩
  obtain ⟨D,hDW,_⟩ := old.exists_component_branch_model Q hQ hQS hf he hcross i hW hselectedW
  obtain ⟨T,hT⟩ := nonempty_local_identity_annuli D (fun _ hx => (hDW hx).1.1)
    (fun x hx hfx => by
      rw [← self_sdiff_frontier]
      exact ⟨hx,fun h => (hDW hfx).1.2 ⟨x,h,rfl⟩⟩) hmate hd hwidth
  exact ⟨T,fun _ hz => (hDW (hT hz)).2⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
