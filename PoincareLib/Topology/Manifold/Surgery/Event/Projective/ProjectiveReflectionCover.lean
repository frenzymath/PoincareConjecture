import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectivePolarCover
import PoincareLib.Topology.Manifold.Surgery.Event.Components.Components
import Mathlib.Topology.Covering.Quotient
import Mathlib.Data.ZMod.Basic

/-!
# The free reflection quotient covering of the punctured projective carrier

The order-two action reverses the sphere and height simultaneously. Its
nonidentity element is fixed-point free, so local injective neighborhoods
of the already constructed polar projection are disjoint from their images.
The target is the actual open complement of the chosen projective point.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- The two-element additive group acts by the actual free cylinder reflection. -/
@[instance_reducible]
noncomputable def cylinderReflectionAction : AddAction (ZMod 2) RoundCylinderSpace where
  vadd n p := if n = 0 then p else (-p.1, -p.2)
  zero_vadd p := if_pos rfl
  add_vadd n m p := by
    change (if n + m = 0 then p else (-p.1, -p.2)) =
      if n = 0 then (if m = 0 then p else (-p.1, -p.2))
      else (-((if m = 0 then p else (-p.1, -p.2)).1),
        -((if m = 0 then p else (-p.1, -p.2)).2))
    have htwo : (2 : ZMod 2) = 0 := rfl
    fin_cases n <;> fin_cases m <;> norm_num [htwo]
    intro h
    exact False.elim (h htwo)

attribute [local instance] cylinderReflectionAction

/-- The identity element fixes each cylinder point. -/
theorem cylinderReflection_zero (p : RoundCylinderSpace) : (0 : ZMod 2) +ᵥ p = p :=
  zero_vadd _ _

/-- The nonidentity element is exactly simultaneous angular and height reversal. -/
theorem cylinderReflection_one (p : RoundCylinderSpace) :
    (1 : ZMod 2) +ᵥ p = (-p.1, -p.2) := if_neg (by decide)

/-- Every deck transformation is continuous in the actual product topology. -/
instance cylinderReflection_continuous : ContinuousConstVAdd (ZMod 2) RoundCylinderSpace where
  continuous_const_vadd n := by
    change Continuous (fun p : RoundCylinderSpace => if n = 0 then p else (-p.1, -p.2))
    by_cases hn : n = 0
    · simp only [if_pos hn]
      exact continuous_id
    · simpa only [if_neg hn, Function.comp_def] using
        ((continuous_neg.comp continuous_fst).prodMk (continuous_neg.comp continuous_snd) :
          Continuous (fun p : RoundCylinderSpace => (-p.1, -p.2)))

/-- The actual angular antipode has no fixed unit vector. -/
theorem cylinderReflection_ne (p : RoundCylinderSpace) : (-p.1, -p.2) ≠ p := by
  intro h
  have he : -(p.1.val) = p.1.val := congrArg Subtype.val (congrArg Prod.fst h)
  have hz : p.1.val = 0 := by
    ext i
    have hi := congrArg (fun v : StandardCapSpace => v i) he
    change -p.1.val i = p.1.val i at hi
    change p.1.val i = 0
    linarith
  exact ne_zero_of_mem_unit_sphere p.1 hz

variable (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))

/-- The target is the literal open complement of the chosen affine center. -/
noncomputable def projectivePolarTarget : TopologicalSpace.Opens projectiveCarrier.{u}.carrier :=
  ⟨{projectiveAffineMap R 0}ᶜ, isClosed_singleton.isOpen_compl⟩

/-- The same polar projection, with its exact image as target. -/
noncomputable def projectivePolarProjection (p : RoundCylinderSpace) : projectivePolarTarget.{u} R :=
  ⟨projectivePolarMap R p, projectivePolar_ne_center R p⟩

/-- Exact range recognition supplies surjectivity onto that open carrier. -/
theorem projectivePolarProjection_surjective :
    Function.Surjective (projectivePolarProjection.{u} R) := by
  intro y
  have hy : y.val ∈ ({projectiveAffineMap.{u} R 0}ᶜ : Set projectiveCarrier.{u}.carrier) := y.property
  rw [← projectivePolar_range R] at hy
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, Subtype.ext hp⟩

/-- The restricted-target projection is the genuine two-sheet quotient covering. -/
theorem projectivePolarProjection_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (projectivePolarProjection.{u} R) (ZMod 2) where
  toIsQuotientMap :=
    ((projectivePolar_localDiffeomorph R).isLocalHomeomorph.isOpenMap.codRestrict
      (projectivePolar_ne_center R)).isQuotientMap
      ((projectivePolar_localDiffeomorph R).contMDiff.continuous.subtype_mk _)
      (projectivePolarProjection_surjective R)
  apply_eq_iff_mem_orbit := by
    intro x y
    rw [show projectivePolarProjection R x = projectivePolarProjection R y ↔
      projectivePolarMap R x = projectivePolarMap R y from Subtype.ext_iff]
    rw [projectivePolar_fibers]
    constructor
    · rintro (rfl | h)
      · exact ⟨0, cylinderReflection_zero _⟩
      · exact ⟨1, (cylinderReflection_one y).trans h.symm⟩
    · rintro ⟨n, hn⟩
      fin_cases n
      · exact Or.inl (hn.symm.trans (cylinderReflection_zero y))
      · exact Or.inr (hn.symm.trans (cylinderReflection_one y))
  disjoint p := by
    let h := projectivePolar_localDiffeomorph.{u} R p
    refine ⟨h.localInverse.target, h.localInverse.open_target.mem_nhds
      h.localInverse_mem_target, ?_⟩
    intro n hn
    fin_cases n
    · rfl
    · obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := hn
      have he : projectivePolarMap.{u} R ((1 : ZMod 2) +ᵥ y) = projectivePolarMap R y := by
        rw [cylinderReflection_one]
        exact projectivePolar_reflection R y
      have hi : (1 : ZMod 2) +ᵥ y = y := by
        calc
          (1 : ZMod 2) +ᵥ y = h.localInverse
              (projectivePolarMap R ((1 : ZMod 2) +ᵥ y)) := (h.localInverse_left_inv hx).symm
          _ = h.localInverse (projectivePolarMap R y) := congrArg h.localInverse he
          _ = y := h.localInverse_left_inv hy
      exact False.elim (cylinderReflection_ne y ((cylinderReflection_one y).symm.trans hi))

end PoincareMT.M38
