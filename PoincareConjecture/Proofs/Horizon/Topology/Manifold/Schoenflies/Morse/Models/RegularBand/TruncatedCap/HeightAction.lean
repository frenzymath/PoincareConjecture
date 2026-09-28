import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.TruncatedCap

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)


def heightAction {v : E3} (hv : ‖v‖ = 1) (φ : Real ≃ₘ[Real] Real) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := by
  let C := (heightCoordinates hv).toDiffeomorph
  let P : (Real × Hemisphere.Plane v) ≃ₘ[Real] (Real × Hemisphere.Plane v) := {
    toEquiv := φ.toEquiv.prodCongr (Equiv.refl _)
    contMDiff_toFun := ((φ.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff
    contMDiff_invFun := ((φ.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd).contMDiff }
  exact (C.symm.trans P).trans C

theorem heightAction_apply {v : E3} (hv : ‖v‖ = 1)
    (φ : Real ≃ₘ[Real] Real) (y : E3) :
    heightAction hv φ y = φ (inner Real v y) • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) := rfl

theorem heightAction_height {v : E3} (hv : ‖v‖ = 1)
    (φ : Real ≃ₘ[Real] Real) (y : E3) :
    inner Real v (heightAction hv φ y) = φ (inner Real v y) :=
  inner_heightCoordinates hv _

theorem heightAction_projection {v : E3} (hv : ‖v‖ = 1)
    (φ : Real ≃ₘ[Real] Real) (y : E3) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (heightAction hv φ y) =
      (Hemisphere.Plane v).orthogonalProjectionOnto y :=
  congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply _)

theorem heightAction_eq_self {v : E3} (hv : ‖v‖ = 1)
    (φ : Real ≃ₘ[Real] Real) {y : E3} (hy : φ (inner Real v y) = inner Real v y) :
    heightAction hv φ y = y := by
  rw [heightAction_apply, hy]
  exact (heightCoordinates hv).apply_symm_apply y



theorem image_heightAction_truncated_cap {v : E3} (hv : ‖v‖ = 1)
    {a : Real} (ha : 0 < a) (ha1 : a < 1)
    (φ : Real ≃ₘ[Real] Real) (hmono : StrictMono φ) (hzero : φ a = 0)
    (hhigh : ∀ t, 1 ≤ t → φ t = t) :
    heightAction hv φ '' (boundedCylinderNorthernCap v ∩ {y | a ≤ inner Real v y}) =
      boundedCylinderNorthernCap v := by
  have hmem (y : E3) : heightAction hv φ y ∈ boundedCylinderNorthernCap v ↔
      y ∈ boundedCylinderNorthernCap v ∧ a ≤ inner Real v y := by
    by_cases ht : 1 ≤ inner Real v y
    · rw [heightAction_eq_self hv φ (hhigh _ ht)]
      exact (and_iff_left (ha1.le.trans ht)).symm
    have ht' : inner Real v y < 1 := lt_of_not_ge ht
    have hφt : inner Real v (heightAction hv φ y) < 1 := by
      rw [heightAction_height, ← hhigh 1 le_rfl]
      exact hmono ht'
    have hφnonneg : 0 ≤ φ (inner Real v y) ↔ a ≤ inner Real v y := by
      rw [← hzero]
      exact hmono.le_iff_le
    rw [mem_boundedCylinderNorthernCap_iff_of_height_lt_one hv hφt,
      mem_boundedCylinderNorthernCap_iff_of_height_lt_one hv ht',
      heightAction_height, heightAction_projection, hφnonneg]
    constructor
    · rintro ⟨hat, hn⟩
      exact ⟨⟨ha.le.trans hat, hn⟩, hat⟩
    · rintro ⟨⟨_, hn⟩, hat⟩
      exact ⟨hat, hn⟩
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact (hmem y).mpr hy
  · intro y hy
    obtain ⟨z, rfl⟩ := (heightAction hv φ).surjective y
    exact ⟨z, (hmem z).mp hy, rfl⟩

end Poincare.Manifold.Schoenflies.TruncatedCap
