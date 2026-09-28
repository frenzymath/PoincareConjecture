import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.TensorNorm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

namespace PoincareConjecture
namespace DeepHorn

theorem evolvingCylinderGram_posSemidef {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p).PosSemidef := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let s := cylinderSphereVector c p
  let t := cylinderAxialVector
  have heq : roundCylinderGram u c p =
      (2 * (1 - u)) • Matrix.gram ℝ s + Matrix.vecMulVec t t := by
    ext a b
    simp [roundCylinderGram, roundCylinderTensorCoefficient, EvolvingRoundCylinderMetric,
      s, t, Matrix.gram, Matrix.vecMulVec]
    rfl
  rw [heq]
  exact (Matrix.PosSemidef.smul (Matrix.posSemidef_gram ℝ s) (by positivity)).add
    (by simpa using Matrix.posSemidef_vecMulVec_self_star t)

theorem evolvingCylinderTensorNormSquared_nonneg {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    {r : ℕ} (A : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A := by
  apply inverseGram_contraction_nonneg
  exact (evolvingCylinderGram_posSemidef hu q p).posDef_iff_det_ne_zero.mpr
    (roundCylinderGram_det_ne_zero hu q p)

theorem evolvingCylinderJetErrorSquared_mono {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace) {k l : ℕ} (hkl : k ≤ l) :
    roundCylinderJetErrorSquared u B k z ≤ roundCylinderJetErrorSquared u B l z := by
  unfold roundCylinderJetErrorSquared
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hkl 1))
    (fun i _ _ => evolvingCylinderTensorNormSquared_nonneg hu z.1 _ _)

theorem neckInterval_subset {epsilon delta : ℝ} (he : 0 < epsilon)
    (hed : epsilon ≤ delta) :
    Set.Ioo (-delta⁻¹) delta⁻¹ ⊆ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ := by
  have hInv : delta⁻¹ ≤ epsilon⁻¹ := (inv_le_inv₀ (he.trans_le hed) he).2 hed
  exact Set.Ioo_subset_Ioo (neg_le_neg hInv) hInv


theorem roundCylinderFamilyClose_mono {epsilon delta : ℝ}
    {I : Set ℝ} {B : ℝ → RoundCylinderTwoTensor}
    (he : 0 < epsilon) (hed : epsilon ≤ delta) (hI : ∀ u ∈ I, u < 1)
    (hB : RoundCylinderFamilyClose epsilon I B) :
    RoundCylinderFamilyClose delta I B := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hB
  refine ⟨?_, bound, hbound.trans_le (pow_le_pow_left₀ he.le hed 2), ?_⟩
  · intro u hu q a b
    exact (hsmooth u hu q a b).mono
      (Set.prod_mono subset_rfl (neckInterval_subset he hed))
  · intro u hu z hz
    exact (evolvingCylinderJetErrorSquared_mono (hI u hu) (B u) z
      (Nat.floor_mono ((inv_le_inv₀ (he.trans_le hed) he).2 hed))).trans
      (hjet u hu z (neckInterval_subset he hed hz))

end DeepHorn
end PoincareConjecture
