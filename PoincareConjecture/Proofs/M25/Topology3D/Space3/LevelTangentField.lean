import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false

open Set Filter Matrix
open scoped ContDiff InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

noncomputable def heightCrossMap (u : E3) : E3 →L[ℝ] E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (((crossProduct.flip (WithLp.ofLp u)).toContinuousLinearMap).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap)

@[simp] theorem heightCrossMap_apply (u n : E3) :
    heightCrossMap u n = WithLp.toLp 2 (WithLp.ofLp n ⨯₃ WithLp.ofLp u) := rfl

theorem heightCrossMap_normal (u n : E3) : ⟪n, heightCrossMap u n⟫_ℝ = 0 := by
  rw [heightCrossMap_apply, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm]
  exact dot_self_cross _ _

theorem heightCrossMap_height (u n : E3) : ⟪u, heightCrossMap u n⟫_ℝ = 0 := by
  rw [heightCrossMap_apply, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm]
  exact dot_cross_self _ _

theorem heightCrossMap_ne_zero (u n : E3) (hn : n ≠ 0)
    (hu : ∀ a : ℝ, a • n ≠ u) : heightCrossMap u n ≠ 0 := by
  have hn' : WithLp.ofLp n ≠ 0 := by
    intro h
    exact hn ((EuclideanSpace.equiv (Fin 3) ℝ).injective
      (h.trans (map_zero (EuclideanSpace.equiv (Fin 3) ℝ)).symm))
  have hind : LinearIndependent ℝ ![WithLp.ofLp n, WithLp.ofLp u] := by
    apply (LinearIndependent.pair_iff' hn').mpr
    intro a ha
    apply hu a
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    exact ha
  intro hz
  apply crossProduct_ne_zero_iff_linearIndependent.mpr hind
  simpa only [heightCrossMap_apply, WithLp.ofLp_toLp, WithLp.ofLp_zero] using
    congrArg WithLp.ofLp hz

theorem heightCrossMap_ne_zero_of_regular_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] E3) (n u : E3) (hn : n ≠ 0)
    (hnA : ∀ v, ⟪n, A v⟫_ℝ = 0)
    (hreg : (InnerProductSpace.toDual ℝ E3 u).comp A ≠ 0) :
    heightCrossMap u n ≠ 0 := by
  apply heightCrossMap_ne_zero u n hn
  intro a ha
  apply hreg
  ext v
  change ⟪u, A v⟫_ℝ = 0
  rw [← ha, real_inner_smul_left, hnA v, mul_zero]

theorem gradientHeightCross_contDiffOn {U : Set E3} (hU : IsOpen U)
    (ρ : E3 → ℝ) (hρ : ContDiffOn ℝ ∞ ρ U) (u : E3) :
    ContDiffOn ℝ ∞ (fun y => heightCrossMap u (gradient ρ y)) U :=
  (heightCrossMap u).contDiff.comp_contDiffOn (contDiffOn_gradient_of_isOpen hU ρ hρ)

theorem exists_compact_level_tangent_field {K U : Set E3}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (ρ : E3 → ℝ) (hρ : ContDiffOn ℝ ∞ ρ U) (u : E3) :
    ∃ g : E3 → E3, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      (∀ᶠ y in 𝓝ˢ K, g y = heightCrossMap u (gradient ρ y)) ∧
      (∀ y, fderiv ℝ ρ y (g y) = 0) ∧ (∀ y, ⟪u, g y⟫_ℝ = 0) := by
  let A : E3 → E3 →L[ℝ] (ℝ × ℝ) := fun y =>
    (fderiv ℝ ρ y).prod (InnerProductSpace.toDual ℝ E3 u)
  have hA (y : E3) (_hy : y ∈ U) : A y (heightCrossMap u (gradient ρ y)) = 0 := by
    apply Prod.ext
    · change fderiv ℝ ρ y (heightCrossMap u (gradient ρ y)) = 0
      rw [← inner_gradient_left]
      exact heightCrossMap_normal _ _
    · exact heightCrossMap_height _ _
  obtain ⟨g, hg, hgc, hgs, hnear, hzero⟩ :=
    exists_compactField_extension_preserving hK hU hKU
      (fun y => heightCrossMap u (gradient ρ y))
      (gradientHeightCross_contDiffOn hU ρ hρ u) A hA
  exact ⟨g, hg, hgc, hgs, hnear, fun y => congrArg Prod.fst (hzero y),
    fun y => congrArg Prod.snd (hzero y)⟩

end PoincareConjecture.M25.Topology3D
