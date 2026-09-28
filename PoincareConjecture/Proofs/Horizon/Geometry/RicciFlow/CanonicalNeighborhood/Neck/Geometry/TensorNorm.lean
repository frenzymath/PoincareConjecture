import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Norm
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators
open Matrix
namespace PoincareConjecture

noncomputable def cylinderSphereVector
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (a : Fin 3) :
    TangentSpace (𝓡 3) (c.symm p.1 : EuclideanSpace ℝ (Fin 3)) :=
  mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm p.1)
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis a).1)

noncomputable def cylinderAxialVector (a : Fin 3) : ℝ :=
  (roundCylinderCoordinateBasis a).2

theorem roundCylinderGram_posSemidef (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p).PosSemidef := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let s := cylinderSphereVector c p
  let t := cylinderAxialVector
  have hEq : roundCylinderGram 0 c p =
      (2 : ℝ) • Matrix.gram ℝ s + Matrix.vecMulVec t t := by
    ext a b
    simp [roundCylinderGram, roundCylinderTensorCoefficient, EvolvingRoundCylinderMetric,
      s, t, Matrix.gram, Matrix.vecMulVec]
    rfl
  rw [hEq]
  exact (Matrix.PosSemidef.smul (Matrix.posSemidef_gram ℝ s) (by norm_num)).add
    (by simpa using Matrix.posSemidef_vecMulVec_self_star t)

theorem roundCylinderGram_posDef (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p).PosDef :=
  (roundCylinderGram_posSemidef q p).posDef_iff_det_ne_zero.mpr
    (roundCylinderGram_det_ne_zero (u := 0) (by norm_num) q p)

noncomputable def componentMultilinearMap {E ι σ : Type*} [AddCommMonoid E] [Module ℝ E]
    [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (T : (σ → ι) → ℝ) (b : Module.Basis ι ℝ E) :
    MultilinearMap ℝ (fun _ : σ => E) ℝ :=
  ∑ I : σ → ι, (MultilinearMap.mkPiRing ℝ σ (T I)).compLinearMap
    (fun r => b.coord (I r))

theorem componentMultilinearMap_basis {E ι σ : Type*} [AddCommMonoid E] [Module ℝ E]
    [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (T : (σ → ι) → ℝ) (b : Module.Basis ι ℝ E) (J : σ → ι) :
    componentMultilinearMap T b (fun r => b (J r)) = T J := by
  classical
  simp [componentMultilinearMap, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, b.coord_apply]
  change (∑ I : σ → ι, (∏ r, (Finsupp.single (J r) 1) (I r)) * T I) = T J
  have hsum : (∑ I : σ → ι, (∏ r, (Finsupp.single (J r) 1) (I r)) * T I) =
      (∏ r, (Finsupp.single (J r) 1) (J r)) * T J := by
    apply Fintype.sum_eq_single J
    intro i hne
    obtain ⟨r, hr⟩ : ∃ r, i r ≠ J r := by
      by_contra h
      apply hne
      funext r
      by_contra h'
      exact h ⟨r, h'⟩
    exact mul_eq_zero.mpr (Or.inl (Finset.prod_eq_zero (Finset.mem_univ r)
      (by simp [hr])))
  simpa using hsum

lemma inverseGram_contraction_nonneg {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (T : (σ → ι) → ℝ) :
    0 ≤ ∑ a : σ → ι, ∑ b : σ → ι,
      (∏ r, G⁻¹ (a r) (b r)) * T a * T b := by
  let normed : NormedAddCommGroup (ι → ℝ) := G.toNormedAddCommGroup hG
  let : NormedAddCommGroup (ι → ℝ) := normed
  let semi : SeminormedAddCommGroup (ι → ℝ) := normed.toSeminormedAddCommGroup
  let : SeminormedAddCommGroup (ι → ℝ) := semi
  let : InnerProductSpace ℝ (ι → ℝ) := G.toInnerProductSpace hG.posSemidef
  let basis : Module.Basis ι ℝ (ι → ℝ) := Pi.basisFun ℝ ι
  let A := componentMultilinearMap T basis
  have hGram : Matrix.of (fun i j => inner ℝ (basis i) (basis j)) = G := by
    ext i j
    change (G *ᵥ (Pi.basisFun ℝ ι j : ι → ℝ)) ⬝ᵥ star (Pi.basisFun ℝ ι i : ι → ℝ) = G i j
    simp only [Pi.basisFun_apply]
    rw [Matrix.mulVec_single_one, dotProduct]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [hbi]
    · simp
  have hcontractA :
      (∑ a : σ → ι, ∑ b : σ → ι,
        (∏ r, G⁻¹ (a r) (b r)) *
          (A (fun r => basis (a r)) * A (fun r => basis (b r)))) =
        ∑ a : σ → Fin (Module.finrank ℝ (ι → ℝ)),
          (A (fun r => stdOrthonormalBasis ℝ (ι → ℝ) (a r))) ^ 2 := by
    rw [← hGram]
    simpa only [pow_two] using
      (multilinear_sum_mul_eq_inverse_gram A A basis
        (stdOrthonormalBasis ℝ (ι → ℝ))).symm
  have hcontract :
      (∑ a : σ → ι, ∑ b : σ → ι,
        (∏ r, G⁻¹ (a r) (b r)) * T a * T b) =
        ∑ a : σ → Fin (Module.finrank ℝ (ι → ℝ)),
          (A (fun r => stdOrthonormalBasis ℝ (ι → ℝ) (a r))) ^ 2 := by
    rw [← hcontractA]
    congr 1
    funext a
    rw [componentMultilinearMap_basis T basis a]
    congr 1
    funext b
    rw [componentMultilinearMap_basis T basis b]
    ring
  rw [hcontract]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem roundCylinderTensorNormSquared_nonneg (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p T := by
  exact inverseGram_contraction_nonneg
    (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)
    (roundCylinderGram_posDef q p) T

end PoincareConjecture
