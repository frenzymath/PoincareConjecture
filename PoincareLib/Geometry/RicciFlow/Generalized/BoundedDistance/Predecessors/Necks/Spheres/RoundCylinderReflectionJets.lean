import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Spheres.RoundCylinderTensorReflection
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Full neck jet comparison under axial reflection

The exact all-rank identities transport Definition 2.16's full covariant
jet sum and strict witness under the reversal of Definition 2.18,
Morgan--Tian pp. 30-31. Coefficient identities are required on the actual
open chart strip, so no derivative of an arbitrary extension is used.
See proof-work/tasks/M25/derivations/2026-09-22-axial-reflection-jet-inventory.md.
-/

set_option autoImplicit false

open scoped BigOperators Topology ContDiff

namespace PoincareMT

/-- The frozen covariant derivative depends only on the open-set germ;
the local form needed for Definition 2.16, p. 30. -/
theorem roundCylinderTensorDerivative_congrOn
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {r : ℕ} {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    {T T' : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ}
    (hT : Set.EqOn T T' U) :
    Set.EqOn (roundCylinderTensorDerivative u c T)
      (roundCylinderTensorDerivative u c T') U := by
  intro p hp
  funext a
  have hmem : ∀ᶠ x in 𝓝 p, x ∈ U := hU.mem_nhds hp
  have hev : (fun x => T x (fun i => a i.succ)) =ᶠ[𝓝 p]
      (fun x => T' x (fun i => a i.succ)) :=
    hmem.mono fun x hx => congrFun (hT hx) _
  unfold roundCylinderTensorDerivative
  rw [hev.fderiv_eq, hT hp]

/-- A local two-slot coefficient identity transports every iterated
covariant derivative in Definition 2.16, p. 30. -/
theorem roundCylinderIteratedDerivative_axialReflection
    (q : UnitTwoSphere) (B B' : RoundCylinderTwoTensor)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    (hcoeff : ∀ p ∈ U, ∀ a b : Fin 3,
      roundCylinderTensorCoefficient B'
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
        roundCylinderAxialSign a * roundCylinderAxialSign b *
          roundCylinderTensorCoefficient B
            (chartAt (EuclideanSpace ℝ (Fin 2)) q)
            (roundCylinderCoordinateReflection p) a b)
    (k : ℕ) :
    Set.EqOn
      (roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) B' k)
      (roundCylinderTensorReflection
        (roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k)) U := by
  induction k with
  | zero =>
    intro p hp
    funext a
    change roundCylinderTensorCoefficient B' _ p (a 0) (a 1) -
        roundCylinderGram 0 _ p (a 0) (a 1) =
      roundCylinderSlotSign a *
        (roundCylinderTensorCoefficient B _ (roundCylinderCoordinateReflection p)
            (a 0) (a 1) -
          roundCylinderGram 0 _ (roundCylinderCoordinateReflection p) (a 0) (a 1))
    rw [hcoeff p hp, roundCylinderGram_axialReflection q p]
    have hslot : roundCylinderSlotSign a =
        roundCylinderAxialSign (a 0) * roundCylinderAxialSign (a 1) :=
      Fin.prod_univ_two _
    rw [hslot]
    ring
  | succ k ih =>
    intro p hp
    funext a
    exact (congrFun (roundCylinderTensorDerivative_congrOn 0 _ hU ih hp) a).trans
      (roundCylinderTensorDerivative_axialReflection q
        (roundCylinderIteratedDerivative 0 _ B k) p a)

/-- The exact finite covariant-jet sum is unchanged on the retained strip;
Definitions 2.16 and 2.18, pp. 30-31. -/
theorem roundCylinderJetErrorSquared_axialReflection
    (epsilon : ℝ) (B B' : RoundCylinderTwoTensor)
    (hcoeff : ∀ (q : UnitTwoSphere) (p : RoundCylinderCoordinates),
      p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
        Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ a b : Fin 3,
        roundCylinderTensorCoefficient B'
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
          roundCylinderAxialSign a * roundCylinderAxialSign b *
            roundCylinderTensorCoefficient B
              (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              (roundCylinderCoordinateReflection p) a b)
    (order : ℕ) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) :
    roundCylinderJetErrorSquared 0 B' order z =
      roundCylinderJetErrorSquared 0 B order (z.1, -z.2) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  have hp : p ∈ c.target ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨mem_chart_target _ _, hz⟩
  change (∑ k ∈ Finset.range (order + 1),
      roundCylinderTensorNormSquared 0 c p
        (roundCylinderIteratedDerivative 0 c B' k p)) =
    ∑ k ∈ Finset.range (order + 1),
      roundCylinderTensorNormSquared 0 c (roundCylinderCoordinateReflection p)
        (roundCylinderIteratedDerivative 0 c B k (roundCylinderCoordinateReflection p))
  apply Finset.sum_congr rfl
  intro k _
  have hjet := roundCylinderIteratedDerivative_axialReflection z.1 B B'
    (c.open_target.prod isOpen_Ioo) (hcoeff z.1) k hp
  rw [hjet]
  exact roundCylinderTensorNormSquared_axialReflection z.1 p
    (roundCylinderIteratedDerivative 0 c B k (roundCylinderCoordinateReflection p))

/-- Coefficient smoothness on the actual open chart strip survives
Definition 2.18's reversal, p. 31. -/
theorem RoundCylinderTensorSmoothOn.axialReflection
    {epsilon : ℝ} {B B' : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn epsilon B)
    (hcoeff : ∀ (q : UnitTwoSphere) (p : RoundCylinderCoordinates),
      p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
        Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ a b : Fin 3,
        roundCylinderTensorCoefficient B'
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
          roundCylinderAxialSign a * roundCylinderAxialSign b *
            roundCylinderTensorCoefficient B
              (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              (roundCylinderCoordinateReflection p) a b) :
    RoundCylinderTensorSmoothOn epsilon B' := by
  intro q a b
  let U := (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
    Set.Ioo (-epsilon⁻¹) epsilon⁻¹
  have hmap : Set.MapsTo roundCylinderCoordinateReflection U U := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    change -epsilon⁻¹ < -p.2 ∧ -p.2 < epsilon⁻¹
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hs : ContDiffOn ℝ ∞
      (fun p => roundCylinderAxialSign a * roundCylinderAxialSign b *
        roundCylinderTensorCoefficient B
          (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (roundCylinderCoordinateReflection p) a b) U :=
    contDiffOn_const.mul ((hB q a b).comp
      roundCylinderCoordinateReflection.contDiff.contDiffOn hmap)
  exact hs.congr fun p hp => hcoeff q p hp a b

/-- Reversal keeps the strict comparison witness and every retained jet
of Definitions 2.16 and 2.18, pp. 30-31. -/
theorem RoundCylinderClose.axialReflection
    {epsilon : ℝ} {B B' : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon 0 B)
    (hcoeff : ∀ (q : UnitTwoSphere) (p : RoundCylinderCoordinates),
      p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
        Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ a b : Fin 3,
        roundCylinderTensorCoefficient B'
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
          roundCylinderAxialSign a * roundCylinderAxialSign b *
            roundCylinderTensorCoefficient B
              (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              (roundCylinderCoordinateReflection p) a b) :
    RoundCylinderClose epsilon 0 B' := by
  rcases hB with ⟨hsmooth, bound, hbound, hjet⟩
  refine ⟨hsmooth.axialReflection hcoeff, bound, hbound, ?_⟩
  intro z hz
  rw [roundCylinderJetErrorSquared_axialReflection epsilon B B' hcoeff _ z hz]
  apply hjet
  constructor <;> dsimp <;> linarith [hz.1, hz.2]

end PoincareMT
