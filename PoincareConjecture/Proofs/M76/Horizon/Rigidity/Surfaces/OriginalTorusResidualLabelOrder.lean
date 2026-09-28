import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualOrientation
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.VertexFibers











set_option autoImplicit false

open AbstractSimplicialComplex

namespace PoincareConjecture.M76

open PreAbstractSimplicialComplex.ModTwoCochains

open Classical in
noncomputable def residualLabelEquiv
    {V : Type*} [Fintype V]
    {A : PreAbstractSimplicialComplex V}
    (L : Finset (Edge A)) (hL : L.card = 2) : Fin 2 ≃ {e : Edge A // e ∈ L} :=
  (Finset.equivFinOfCardEq hL).symm

open Classical in
theorem residualLabelEquiv_apply_mem
    {V : Type*} [Fintype V]
    {A : PreAbstractSimplicialComplex V}
    (L : Finset (Edge A)) (hL : L.card = 2) (i : Fin 2) :
    (residualLabelEquiv L hL i).val ∈ L :=
  (residualLabelEquiv L hL i).property

open Classical in
structure ResidualDartOrientationData
    {V : Type*} [Fintype V]
    (A : PreAbstractSimplicialComplex V)
    (L : Finset (Edge A)) where
  label : Fin 2 → Edge A
  label_mem : ∀ i, label i ∈ L
  label_injective : Function.Injective label
  sideEdge : Fin 2 → Bool → Edge A
  sideEdge_eq : ∀ i b, sideEdge i b = label i
  opposite : Fin 2 → Bool → Fin 2 × Bool
  opposite_eq : ∀ i b, opposite i b = (i, !b)
  dart : Fin 2 → SurfaceDart A
  dart_edge : ∀ i, (dart i).1 = label i

open Classical in
theorem exists_residual_dart_orientation_data
    {V : Type*} [Fintype V]
    (A : PreAbstractSimplicialComplex V)
    (L : Finset (Edge A)) (hL : L.card = 2)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (number : V ↪ ℕ)
    (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (hordered : ∀ t, StrictMono (number ∘ p t))
    (sigma : Triangle A → ZMod 2)
    (hcancel : ∀ t u : Triangle A, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1) :
    ∃ d : ResidualDartOrientationData A L,
      (∀ i, (d.dart i).1 = d.label i) ∧
      (∀ i,
        surfaceDartStart A p hp himage sigma
            (surfaceEdgePairing A hcofaces (d.dart i)) =
          surfaceDartEnd A p hp himage sigma (d.dart i)) ∧
      (∀ i,
        surfaceDartEnd A p hp himage sigma
            (surfaceEdgePairing A hcofaces (d.dart i)) =
          surfaceDartStart A p hp himage sigma (d.dart i)) := by
  classical
  let q := residualLabelEquiv L hL
  let label : Fin 2 → Edge A := fun i => (q i).val
  have hlabel_mem : ∀ i, label i ∈ L := by
    intro i
    exact (q i).property
  have hlabel_injective : Function.Injective label := by
    intro i j hij
    apply q.injective
    apply Subtype.ext
    exact hij
  have hdata (i : Fin 2) := exists_residual_dart_endpoint_reversal A hcofaces
    number p hp himage hordered sigma hcancel (label i)
  choose d hd hstart hend using hdata
  let data : ResidualDartOrientationData A L :=
    ⟨label, hlabel_mem, hlabel_injective,
      (fun i b => label i), (fun i b => rfl),
      (fun i b => (i, !b)), (fun i b => rfl), d, hd⟩
  refine ⟨data, ?_, ?_, ?_⟩
  · exact hd
  · exact hstart
  · exact hend

open Classical in
theorem residual_dart_orientation_endpoint_sets
    {V : Type*} [Fintype V]
    (A : PreAbstractSimplicialComplex V)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (number : V ↪ ℕ)
    (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (hordered : ∀ t, StrictMono (number ∘ p t))
    (sigma : Triangle A → ZMod 2)
    (hcancel : ∀ t u : Triangle A, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (d : SurfaceDart A) :
    d.1.val = {surfaceDartStart A p hp himage sigma d,
      surfaceDartEnd A p hp himage sigma d} ∧
    (surfaceEdgePairing A hcofaces d).1.val =
      {surfaceDartStart A p hp himage sigma d,
        surfaceDartEnd A p hp himage sigma d} := by
  constructor
  · exact surfaceDart_edge_eq_endpoints A p hp himage sigma d
  · rw [surfaceEdgePairing_edge A hcofaces d]
    obtain ⟨hstart, hend⟩ := surfaceEdgePairing_reverses_endpoints A number p hp
      himage hordered sigma hcancel hcofaces d
    rw [surfaceDart_edge_eq_endpoints A p hp himage sigma d]

end PoincareConjecture.M76
