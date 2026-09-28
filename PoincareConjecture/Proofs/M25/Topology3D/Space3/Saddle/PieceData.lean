import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood

set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

structure SaddlePieceData (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere) where
  capCount : ℕ
  cap : Fin capCount → SurgeryCapTag ψ u
  sourceCore : Set UnitTwoSphere
  sourceCore_compact : IsCompact sourceCore
  sourceCore_connected : IsConnected sourceCore
  source_cover : sourceCore ∪ (⋃ i, (cap i).sourceCap) = univ
  source_incidence : ∀ i, sourceCore ∩ (cap i).sourceCap = (cap i).sourceSeam
  sourceCap_disjoint : ∀ i k, i ≠ k → Disjoint (cap i).sourceCap (cap k).sourceCap
  point : UnitTwoSphere
  slabLower : ℝ
  slabUpper : ℝ
  core_in_slab : (fun q : UnitTwoSphere => ⟪(u : E3), ψ (q, 0)⟫_ℝ) '' sourceCore ⊆
    Icc slabLower slabUpper
  point_in_slab : slabLower < ⟪(u : E3), ψ (point, 0)⟫_ℝ ∧
    ⟪(u : E3), ψ (point, 0)⟫_ℝ < slabUpper
  unique_critical : ∀ q ∈ sourceCore,
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0 ↔
      q = point
  morse : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ)
  morse_smooth : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ morse morse.source
  morse_inverse : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ morse.symm morse.target
  morse_point : morse point = 0
  morseSign1 : ℝ
  morseSign2 : ℝ
  morseSign1_sq : morseSign1 * morseSign1 = 1
  morseSigns_opposite : morseSign2 = -morseSign1
  morse_height : ∀ q ∈ morse.source,
    ⟪(u : E3), ψ (q, 0)⟫_ℝ = ⟪(u : E3), ψ (point, 0)⟫_ℝ +
      morseSign1 * (morse q).1 ^ 2 + morseSign2 * (morse q).2 ^ 2
  protectedSet : Set UnitTwoSphere
  protected_open : IsOpen protectedSet
  point_mem_protected : point ∈ protectedSet
  protected_closure : closure protectedSet ⊆ morse.source ∩ interior sourceCore
  cutRadius : Fin capCount → ℝ
  removal_lt_cutRadius : ∀ i, (cap i).removal < cutRadius i
  cutRadius_lt_gap : ∀ i, cutRadius i < |(cap i).cutHeight - ⟪(u : E3), ψ (point, 0)⟫_ℝ|
  cut_side : ∀ i,
    ((cap i).sign = 1 ∧ (cap i).cutHeight < ⟪(u : E3), ψ (point, 0)⟫_ℝ) ∨
      ((cap i).sign = -1 ∧ ⟪(u : E3), ψ (point, 0)⟫_ℝ < (cap i).cutHeight)

structure SaddleLowerLevelData {ψ : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData ψ u) where
  level : ℝ
  level_lt_critical : level < ⟪(u : E3), ψ (D.point, 0)⟫_ℝ
  lower_seams_lt_level : ∀ i, (D.cap i).sign = 1 →
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal < level
  label : Fin 2 → Fin D.capCount
  label_injective : Function.Injective label
  label_lower : ∀ b, (D.cap (label b)).sign = 1
  leg : Fin 2 → OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere
  leg_source : ∀ b, univ ×ˢ Icc
    ((D.cap (label b)).cutHeight + (D.cap (label b)).sign * (D.cap (label b)).removal)
    level ⊆ (leg b).source
  leg_smooth : ∀ b, ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (leg b) (leg b).source
  leg_inverse : ∀ b,
    ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ (leg b).symm (leg b).target
  leg_height : ∀ b p, p ∈ (leg b).source → ⟪(u : E3), ψ (leg b p, 0)⟫_ℝ = p.2
  leg_bottom : ∀ b, range (fun θ => leg b (θ,
    (D.cap (label b)).cutHeight + (D.cap (label b)).sign * (D.cap (label b)).removal)) =
      (D.cap (label b)).sourceSeam
  leg_disjoint : Disjoint
    ((leg 0) '' (univ ×ˢ Icc
      ((D.cap (label 0)).cutHeight + (D.cap (label 0)).sign * (D.cap (label 0)).removal)
      level))
    ((leg 1) '' (univ ×ˢ Icc
      ((D.cap (label 1)).cutHeight + (D.cap (label 1)).sign * (D.cap (label 1)).removal)
      level))
  leg_cover : (⋃ b, (leg b) '' (univ ×ˢ Icc
    ((D.cap (label b)).cutHeight + (D.cap (label b)).sign * (D.cap (label b)).removal)
    level)) = D.sourceCore ∩ {q | ⟪(u : E3), ψ (q, 0)⟫_ℝ ≤ level}
  disc : Fin 2 → BallNeighborhoodChart E2 E2
  disc_boundary : ∀ b,
    (fun x => (heightPlaneCoordinates u).symm (x, level)) '' (disc b).boundary =
      range (fun θ => ψ (leg b (θ, level), 0))

def SaddlePieceData.nonnested {ψ : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData ψ u) : Prop :=
  ∃ W : SaddleLowerLevelData D, Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion

def SaddlePieceData.nested {ψ : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData ψ u) : Prop :=
  ∃ W : SaddleLowerLevelData D,
    (W.disc 0).closedRegion ⊆ (W.disc 1).inside ∨
      (W.disc 1).closedRegion ⊆ (W.disc 0).inside

end PoincareConjecture.M25.Topology3D
