import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1




structure ActualStripData
    {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
    {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (d : TerminalSaddleGeometry M P p e) where
  width : Real
  bandHeight : Real
  ambientBound : Real
  centralLeft : Fin 2 → Real
  centralRight : Fin 2 → Real
  contactLabels : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)
  support : Set E3
  fixedNeighborhood : Set E3
  width_pos : 0 < width
  bandHeight_pos : 0 < bandHeight
  bandHeight_lt_width : bandHeight < width
  bandHeight_lt_bound : bandHeight < ambientBound
  radius_lt_bound : d.r < ambientBound
  delta_lt_bandHeight : d.delta < bandHeight
  interval_nonempty : ∀ i, d.a i < d.b i
  source_eq : ∀ i,
    (d.strips i).source = Ioo (d.a i - width) (d.b i + width) ×ˢ Ioo (-width) width
  smooth : ∀ i,
    ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ (d.strips i) (d.strips i).source
  symm_smooth : ∀ i,
    ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞ (d.strips i).symm (d.strips i).target
  height : ∀ i z, z ∈ (d.strips i).source →
    inner Real (M.v : E3) (g (d.strips i z)) = inner Real (M.v : E3) (g p) + z.2
  disjoint : Pairwise (fun i j => Disjoint (d.strips i).target (d.strips j).target)
  band_in_core : (fun q => inner Real (M.v : E3) (g q)) ⁻¹'
    Icc (inner Real (M.v : E3) (g p) - bandHeight)
      (inner Real (M.v : E3) (g p) + bandHeight) ⊆ interior P.core
  band_cover : (fun q => inner Real (M.v : E3) (g q)) ⁻¹'
    Icc (inner Real (M.v : E3) (g p) - bandHeight)
      (inner Real (M.v : E3) (g p) + bandHeight) ⊆ e '' openSquare d.r ∪
    ⋃ i, d.strips i '' (Icc (d.a i) (d.b i) ×ˢ Icc (-bandHeight) bandHeight)
  central_chain : ∀ i,
    d.a i < centralLeft i ∧ centralLeft i < centralRight i ∧ centralRight i < d.b i
  central_cover : (⋃ i, d.strips i ''
    (Icc (centralLeft i) (centralRight i) ×ˢ ({0} : Set Real))) =
    {q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} \ e '' openSquare d.r
  central_endpoints : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact d.r j)) ∩
    (d.strips i '' (Icc (centralLeft i) (centralRight i) ×ˢ ({0} : Set Real))) =
    {d.strips i (centralLeft i, 0), d.strips i (centralRight i, 0)}
  contact_pairing :
    (∀ i j : Fin 2 × Fin 2, e (contact d.r i) ∈ connectedComponentIn
      ({q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} \
        e '' openSquare d.r) (e (contact d.r j)) ↔ i.1 = j.1) ∨
    (∀ i j : Fin 2 × Fin 2, e (contact d.r i) ∈ connectedComponentIn
      ({q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} \
        e '' openSquare d.r) (e (contact d.r j)) ↔ i.2 = j.2)
  support_compact : IsCompact support
  support_height : support ⊆
    {x | |inner Real (M.v : E3) x - inner Real (M.v : E3) (g p)| ≤ ambientBound}
  fixedNeighborhood_open : IsOpen fixedNeighborhood
  center_mem_fixedNeighborhood : g p ∈ fixedNeighborhood
  fixed_on_neighborhood : EqOn d.D id fixedNeighborhood
  fixed_off_support : ∀ x ∉ support, d.D x = x
  fixed_critical_plane : ∀ x,
    inner Real (M.v : E3) x = inner Real (M.v : E3) (g p) → d.D x = x
  flattening : ∀ i t, t ∈ Icc (-bandHeight) bandHeight → ∀ s ∈ Icc (d.a i) (d.b i),
    d.D (g (d.strips i (s, t))) = g (d.strips i (s, 0)) + t • (M.v : E3)
  endpoint_labels : ∀ k,
    d.strips k.1 (stripEndpoint centralLeft centralRight k, 0) =
      e (contact d.r (contactLabels k))
  contacts_zero : ∀ i, d.leftContact i 0 = centralLeft i ∧ d.rightContact i 0 = centralRight i
  recut_geometry : ∀ t ∈ Icc (-d.delta) d.delta,
    (∀ i, ContinuousAt (d.leftContact i) t ∧ ContinuousAt (d.rightContact i) t ∧
      d.a i < d.leftContact i t ∧ d.leftContact i t < d.rightContact i t ∧
      d.rightContact i t < d.b i ∧
      (Icc (d.leftContact i t) (d.rightContact i t) ×ˢ ({t} : Set Real) ⊆ (d.strips i).source) ∧
      d.strips i (d.leftContact i t, t) = e (movingContact d.r t (contactLabels (i, 0))) ∧
      d.strips i (d.rightContact i t, t) = e (movingContact d.r t (contactLabels (i, 1))) ∧
      (∀ s ∈ Icc (d.a i) (d.b i),
        d.strips i (s, t) ∉ e '' openSquare d.r ↔
          s ∈ Icc (d.leftContact i t) (d.rightContact i t))) ∧
    ({q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p) + t} \
      e '' openSquare d.r) =
      ⋃ i, d.strips i '' (Icc (d.leftContact i t) (d.rightContact i t) ×ˢ ({t} : Set Real))

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
