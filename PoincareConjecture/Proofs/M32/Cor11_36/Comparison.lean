import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.TensorNorm

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

namespace PoincareConjecture.M32

theorem evolvingCylinderGram_posSemidef {s : ℝ} (hs : s < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (roundCylinderGram s (chartAt (EuclideanSpace ℝ (Fin 2)) q) p).PosSemidef := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let v := cylinderSphereVector c p
  let w := cylinderAxialVector
  have hgram : roundCylinderGram s c p =
      (2 * (1 - s)) • Matrix.gram ℝ v + Matrix.vecMulVec w w := by
    ext a b
    simp [roundCylinderGram, roundCylinderTensorCoefficient, EvolvingRoundCylinderMetric,
      v, w, Matrix.gram, Matrix.vecMulVec]
    rfl
  rw [hgram]
  exact (Matrix.PosSemidef.smul (Matrix.posSemidef_gram ℝ v) (by positivity)).add
    (by simpa using Matrix.posSemidef_vecMulVec_self_star w)

theorem evolvingCylinderTensorNormSquared_nonneg {s : ℝ} (hs : s < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    {r : ℕ} (A : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared s (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A := by
  apply inverseGram_contraction_nonneg
  exact (evolvingCylinderGram_posSemidef hs q p).posDef_iff_det_ne_zero.mpr
    (roundCylinderGram_det_ne_zero hs q p)

theorem evolvingCylinderJetErrorSquared_mono {s : ℝ} (hs : s < 1)
    (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace) {k l : ℕ} (hkl : k ≤ l) :
    roundCylinderJetErrorSquared s B k z ≤ roundCylinderJetErrorSquared s B l z := by
  unfold roundCylinderJetErrorSquared
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hkl 1))
    (fun i _ _ => evolvingCylinderTensorNormSquared_nonneg hs z.1 _ _)

theorem neckInterval_subset {epsilon delta : ℝ} (he : 0 < epsilon)
    (hed : epsilon ≤ delta) :
    Set.Ioo (-delta⁻¹) delta⁻¹ ⊆ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ := by
  have hinv : delta⁻¹ ≤ epsilon⁻¹ := (inv_le_inv₀ (he.trans_le hed) he).2 hed
  exact Set.Ioo_subset_Ioo (neg_le_neg hinv) hinv

theorem roundCylinderFamilyClose_mono {epsilon delta : ℝ}
    {I : Set ℝ} {B : ℝ → RoundCylinderTwoTensor}
    (he : 0 < epsilon) (hed : epsilon ≤ delta) (hI : ∀ s ∈ I, s < 1)
    (hB : RoundCylinderFamilyClose epsilon I B) :
    RoundCylinderFamilyClose delta I B := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hB
  refine ⟨?_, bound, hbound.trans_le (pow_le_pow_left₀ he.le hed 2), ?_⟩
  · intro s hs q a b
    exact (hsmooth s hs q a b).mono
      (Set.prod_mono subset_rfl (neckInterval_subset he hed))
  · intro s hs z hz
    exact (evolvingCylinderJetErrorSquared_mono (hI s hs) (B s) z
      (Nat.floor_mono ((inv_le_inv₀ (he.trans_le hed) he).2 hed))).trans
      (hjet s hs z (neckInterval_subset he hed hz))

end PoincareConjecture.M32
