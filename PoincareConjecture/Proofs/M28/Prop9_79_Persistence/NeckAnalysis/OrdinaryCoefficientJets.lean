import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.ReverseCovariantJets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

open FiniteHessian

theorem iteratedFDeriv_roundCylinderGram_axial (u : ℝ) (q : UnitTwoSphere)
    (k : ℕ) (s : ℝ) (a b : Fin 3) :
    iteratedFDeriv ℝ k (fun p => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) (0, s) =
    iteratedFDeriv ℝ k (fun p => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) 0 := by
  have heq : (fun p : RoundCylinderCoordinates => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) ((0, s) + p) a b) =
      (fun p => roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) := by
    funext p
    simp [roundCylinderGram_chosen_chart]
  have h := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun p => roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)
    k (0, s) 0
  rw [heq, add_zero] at h
  exact h.symm

theorem exists_bound_roundCylinderGram_jets (u : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : UnitTwoSphere) (s : ℝ), ∀ k ≤ m,
      ∀ a b : Fin 3, ‖iteratedFDeriv ℝ k (fun p => roundCylinderGram u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) (0, s)‖ ≤ C := by
  let value : Fin (m + 1) × Fin 3 × Fin 3 → ℝ := fun i =>
    ‖iteratedFDeriv ℝ i.1 (fun p : RoundCylinderCoordinates =>
      (Matrix.diagonal ![2 * (1 - u) * sphereChartConformalFactor p.1,
        2 * (1 - u) * sphereChartConformalFactor p.1, 1]) i.2.1 i.2.2) 0‖
  refine ⟨∑ i, value i, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro q s k hk a b
  rw [iteratedFDeriv_roundCylinderGram_axial]
  simp_rw [roundCylinderGram_chosen_chart]
  exact Finset.single_le_sum (f := value) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩, a, b))

theorem hasUniformJetBoundsAt_cylinder_coefficients_of_close
    {ι : Type*} {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1)
    (m : ℕ) (hm : m ≤ ⌊epsilon⁻¹⌋₊)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (B : ι → RoundCylinderTwoTensor) (hB : ∀ i, RoundCylinderClose epsilon 0 (B i))
    (a b : Fin 3) :
    HasUniformJetBoundsAt m (fun i p => roundCylinderTensorCoefficient (B i)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) p a b) (fun i => (0, s i)) := by
  have herror := hasUniformJetBoundsAt_cylinder_error_of_close
    hepsilon hsmall m hm q s hs B hB 0 (by omega) ![a, b]
  simp only [Nat.sub_zero] at herror
  have hgram : HasUniformJetBoundsAt m (fun i p => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) p a b) (fun i => (0, s i)) := by
    obtain ⟨C, _, hC⟩ := exists_bound_roundCylinderGram_jets 0 m
    exact fun k hk => ⟨C, fun i => hC (q i) (s i) k hk a b⟩
  have hc (i : ι) : ContDiffAt ℝ ∞ (fun p => roundCylinderTensorCoefficient (B i)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) p a b) (0, s i) := by
    apply ((hB i).1 (q i) a b).contDiffAt
    apply ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).open_target.prod isOpen_Ioo).mem_nhds
    refine ⟨?_, hs i⟩
    rw [← sphere_chart_center (q i)]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).map_source (mem_chart_source _ (q i))
  have hcerror (i : ι) : ContDiffAt ℝ ∞ (fun p => roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) 0 p ![a, b]) (0, s i) := by
    exact (hc i).sub (contDiff_roundCylinderGram 0 (q i) a b).contDiffAt
  have hsum := herror.add hgram hcerror
    (fun i => (contDiff_roundCylinderGram 0 (q i) a b).contDiffAt)
  apply hsum.congr_germ
  intro i
  apply Filter.Eventually.of_forall
  intro p
  simp [roundCylinderIteratedDerivative]

end PoincareConjecture.Proofs.M28.NeckAnalysis
