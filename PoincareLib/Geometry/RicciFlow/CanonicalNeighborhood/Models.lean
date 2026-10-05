import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth models of canonical neighborhoods

Adapted from Mapher, `PoincareMT/Definitions/Ch09/NeckCapTopology.lean`, commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Declaration bodies are retained; only the required definition closure is imported.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

abbrev UnitThreeSphere :=
  {x : EuclideanSpace ℝ (Fin 4) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}

instance realProjectiveThreeSetoid : Setoid UnitThreeSphere where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp)
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (by simpa [hxy] using hyz)
      · exact Or.inr (by simpa [hyz] using hxy)
      · exact Or.inl (by rw [hxy, hyz]; simp)

abbrev RealProjectiveThree := Quotient realProjectiveThreeSetoid

abbrev PuncturedRealProjectiveThree (p : RealProjectiveThree) :=
  {q : RealProjectiveThree // q ≠ p}

structure StandardProjectiveSmoothCover (Q : Type u) [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] where
  cover : UnitThreeSphere → Q
  surjective : Function.Surjective cover
  fibers : ∀ x y, cover x = cover y ↔ x = y ∨ x = -y
  local_diffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ cover

structure StandardPuncturedProjectiveCover (Q : Type u) [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    (p : RealProjectiveThree) (U : Set Q) where
  cover : UnitThreeSphere → Q
  image_eq : cover '' {x | Quotient.mk' x ≠ p} = U
  fibers : ∀ x y : UnitThreeSphere, Quotient.mk' x ≠ p → Quotient.mk' y ≠ p →
    (cover x = cover y ↔ x = y ∨ x = -y)
  local_diffeomorph : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ cover
    {x | Quotient.mk' x ≠ p}

structure SmoothProjectiveDoubleModel (Q : Type u) [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] where
  compact : IsCompact (Set.univ : Set Q)
  connected : IsConnected (Set.univ : Set Q)
  sphere : Set Q
  first_region : Set Q
  second_region : Set Q
  first_open : IsOpen first_region
  second_open : IsOpen second_region
  disjoint : Disjoint first_region second_region
  sphere_disjoint : Disjoint sphere (first_region ∪ second_region)
  cover : first_region ∪ second_region ∪ sphere = Set.univ
  first_puncture : RealProjectiveThree
  second_puncture : RealProjectiveThree
  first_model : StandardPuncturedProjectiveCover Q first_puncture first_region
  second_model : StandardPuncturedProjectiveCover Q second_puncture second_region
  collar : RoundCylinderSpace → Q
  collar_local_diffeomorph : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (𝓡 3) ∞ collar (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  collar_injective : Set.InjOn collar (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  collar_open : IsOpen (collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
  collar_sphere : collar '' (Set.univ ×ˢ ({0} : Set ℝ)) = sphere
  collar_negative : collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) ⊆ first_region
  collar_positive : collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) ⊆ second_region

inductive CapModelKind
  | euclidean
  | puncturedProjective
deriving DecidableEq

structure CapModelEquivalence (kind : CapModelKind) (p : RealProjectiveThree)
    (carrier : Set M) where
  model : Type u
  model_topology : TopologicalSpace model
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model
  model_manifold : IsManifold (𝓡 3) ∞ model
  standard_model :
    letI : TopologicalSpace model := model_topology
    match kind with
    | .euclidean => model ≃ₜ ULift.{u} (EuclideanSpace ℝ (Fin 3))
    | .puncturedProjective =>
        model ≃ₜ ULift.{u} (PuncturedRealProjectiveThree p)
  standard_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    match kind with
    | .euclidean => Nonempty (Diffeomorph (𝓡 3) (𝓡 3) model
        (EuclideanSpace ℝ (Fin 3)) ∞)
    | .puncturedProjective =>
        Nonempty (StandardPuncturedProjectiveCover model p Set.univ)
  forward : M → model
  inverse : model → M
  inverse_mem : ∀ y, inverse y ∈ carrier
  left_inverse : ∀ x ∈ carrier, inverse (forward x) = x
  right_inverse : ∀ y, forward (inverse y) = y
  forward_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    letI : IsManifold (𝓡 3) ∞ model := model_manifold
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ forward carrier
  inverse_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    letI : IsManifold (𝓡 3) ∞ model := model_manifold
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse Set.univ

inductive ClosedComponentKind
  | threeSphere
  | realProjectiveThree
  | realProjectiveThreeConnectedSum
deriving DecidableEq

structure RealProjectiveThreeConnectedSumModel (Y : Type u)
    (τ : TopologicalSpace Y) where
  sphere : Set Y
  sphere_model : sphere ≃ₜ UnitTwoSphere
  first_piece : Set Y
  second_piece : Set Y
  union_eq : first_piece ∪ second_piece = Set.univ
  intersection_eq : first_piece ∩ second_piece = sphere
  first_puncture : RealProjectiveThree
  second_puncture : RealProjectiveThree
  first_piece_model :
    letI : TopologicalSpace Y := τ
    (first_piece \ sphere : Set Y) ≃ₜ PuncturedRealProjectiveThree first_puncture
  second_piece_model :
    letI : TopologicalSpace Y := τ
    (second_piece \ sphere : Set Y) ≃ₜ PuncturedRealProjectiveThree second_puncture

structure ClosedComponentModel (kind : ClosedComponentKind) where
  carrier : Type u
  carrier_topology : TopologicalSpace carrier
  compact : CompactSpace carrier
  connected : IsConnected (Set.univ : Set carrier)
  standard_model :
    match kind with
    | .threeSphere => carrier ≃ₜ UnitThreeSphere
    | .realProjectiveThree => carrier ≃ₜ RealProjectiveThree
    | .realProjectiveThreeConnectedSum =>
        RealProjectiveThreeConnectedSumModel carrier carrier_topology

structure SmoothClosedComponentModel (kind : ClosedComponentKind) (Y : Set M) where
  model : Type u
  model_topology : TopologicalSpace model
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model
  model_manifold : IsManifold (𝓡 3) ∞ model
  standard_model :
    letI : TopologicalSpace model := model_topology
    match kind with
    | .threeSphere => model ≃ₜ UnitThreeSphere
    | .realProjectiveThree => model ≃ₜ RealProjectiveThree
    | .realProjectiveThreeConnectedSum =>
        RealProjectiveThreeConnectedSumModel model model_topology
  standard_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    match kind with
    | .threeSphere => Nonempty (Diffeomorph (𝓡 3) (𝓡 3) model UnitThreeSphere ∞)
    | .realProjectiveThree => Nonempty (StandardProjectiveSmoothCover model)
    | .realProjectiveThreeConnectedSum => Nonempty (SmoothProjectiveDoubleModel model)
  forward : model → M
  inverse : M → model
  forward_mem : ∀ y, forward y ∈ Y
  left_inverse : ∀ x ∈ Y, forward (inverse x) = x
  right_inverse : ∀ y, inverse (forward y) = y
  forward_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ forward
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse Y

structure ClosedComponentCertificate (kind : ClosedComponentKind) (Y : Set M) where
  model : ClosedComponentModel.{u} kind
  homeomorph :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    Y ≃ₜ model.carrier
  connected : IsConnected Y
  compact : IsCompact Y
  component : ∃ x : M, Y = connectedComponent x
  smooth_model : SmoothClosedComponentModel kind Y
  model_transport :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    letI : TopologicalSpace smooth_model.model := smooth_model.model_topology
    ∃ e : model.carrier ≃ₜ smooth_model.model,
      ∀ x : Y, e (homeomorph x) = smooth_model.inverse x.1

end PoincareMT

