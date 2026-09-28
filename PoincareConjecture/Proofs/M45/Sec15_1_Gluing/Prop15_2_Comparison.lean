import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Patches
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderTimeComparison

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators Topology

universe u

namespace PoincareConjecture.M45

theorem evolvingCylinderInverseWeight_pos {t : ℝ} (ht : t < 1) (i : Fin 3) :
    0 < M44.evolvingCylinderInverseWeight t i := by
  have h : 0 < (2 * (1 - t))⁻¹ := by positivity
  fin_cases i
  · exact h
  · exact h
  · norm_num [M44.evolvingCylinderInverseWeight]

theorem evolvingTensorNormSquared_nonneg {t : ℝ} (ht : t < 1)
    {r : ℕ} (q : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared t
      (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T := by
  rw [M44.evolving_roundCylinderTensorNormSquared_center ht]
  exact Finset.sum_nonneg fun a _ => mul_nonneg
    (Finset.prod_nonneg fun i _ => (evolvingCylinderInverseWeight_pos ht (a i)).le)
    (sq_nonneg _)

theorem evolvingJetError_mono_order {t : ℝ} (ht : t < 1)
    (B : RoundCylinderTwoTensor) {m n : ℕ} (hmn : m ≤ n)
    (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared t B m z ≤ roundCylinderJetErrorSquared t B n z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hmn 1))
  intro k _ _
  exact evolvingTensorNormSquared_nonneg ht z.1 z.2 _

theorem cylinderDomain_mono {eta epsilon : ℝ} (heta : 0 < eta) (hle : eta ≤ epsilon) :
    Set.Ioo (-epsilon⁻¹) epsilon⁻¹ ⊆ Set.Ioo (-eta⁻¹) eta⁻¹ := by
  have hi : epsilon⁻¹ ≤ eta⁻¹ := inv_anti₀ heta hle
  intro s hs
  exact ⟨lt_of_le_of_lt (neg_le_neg hi) hs.1, lt_of_lt_of_le hs.2 hi⟩

theorem familyClose_mono {eta epsilon : ℝ} (heta : 0 < eta) (hle : eta ≤ epsilon)
    {J K : Set ℝ} (hKJ : K ⊆ J) (hK : ∀ t ∈ K, t < 1)
    {B : ℝ → RoundCylinderTwoTensor} (hB : RoundCylinderFamilyClose eta J B) :
    RoundCylinderFamilyClose epsilon K B := by
  have hdom := cylinderDomain_mono heta hle
  have hi : epsilon⁻¹ ≤ eta⁻¹ := inv_anti₀ heta hle
  have horder : ⌊epsilon⁻¹⌋₊ ≤ ⌊eta⁻¹⌋₊ := Nat.floor_mono hi
  refine ⟨?_, ?_⟩
  · intro t ht q a b
    exact (hB.1 t (hKJ ht) q a b).mono fun p hp => ⟨hp.1, hdom hp.2⟩
  · obtain ⟨bound, hbound, hjet⟩ := hB.2
    have hsquare : eta ^ 2 ≤ epsilon ^ 2 := (sq_le_sq₀ heta.le (heta.trans_le hle).le).mpr hle
    refine ⟨bound, hbound.trans_le hsquare, ?_⟩
    intro t ht z hz
    exact (evolvingJetError_mono_order (hK t ht) (B t) horder z).trans
      (hjet t (hKJ ht) z (hdom hz))

theorem recent_piecewise_comparison {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_one : beta ≤ 1)
    (I : M45NeckGluingInput.{u} epsilon beta) (hduration : 1 ≤ I.recent_duration) :
    RoundCylinderFamilyClose epsilon (Set.Ioc (-1 : ℝ) 0)
      (I.piecewiseTensor I.recent_patch.coordinate) := by
  have he : 0 < beta * epsilon := mul_pos hbeta hepsilon
  have hle : beta * epsilon ≤ epsilon := by nlinarith
  have ht : Set.Ioc (-1 : ℝ) 0 ⊆ Set.Icc (-I.recent_duration) 0 := by
    intro t h
    exact ⟨by linarith [h.1], h.2⟩
  have hb := familyClose_mono he hle ht (fun t h => h.2.trans_lt (by norm_num))
    I.recent_comparison
  have heq (t : ℝ) (h : t ∈ Set.Ioc (-1 : ℝ) 0) :
      I.piecewiseTensor I.recent_patch.coordinate t =
        roundCylinderPullback (I.recent_flow.metric t) I.recent_patch.coordinate := by
    simp only [M45NeckGluingInput.piecewiseTensor, if_pos (ht h).1]
  refine ⟨?_, ?_⟩
  · intro t h
    rw [heq t h]
    exact hb.1 t h
  · obtain ⟨bound, hbound, hjet⟩ := hb.2
    refine ⟨bound, hbound, ?_⟩
    intro t h z hz
    rw [heq t h]
    exact hjet t h z hz

end PoincareConjecture.M45
