import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementEnergy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Topology

namespace PoincareConjecture

theorem m64Observed_replacement_energy_le_norm {m : ℕ} {M : Type*} [TopologicalSpace M]
    (e : M → EuclideanSpace ℝ (Fin m)) (hei : IsEmbedding e)
    (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hQ : Continuous Q) {bound : ℝ} (hb : ∀ q, ‖Q q‖ ≤ bound)
    {K : Set LoopPlane} (f : LoopPlane → M)
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (hf : MemLp (e ∘ f) 2 (volume.restrict K))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict K)) :
    (∫ z in K, (Q (f z) (V 0 z) (V 0 z) + Q (f z) (V 1 z) (V 1 z)) / 2) ≤
      (bound / 2) * ∫ z in K, ∑ i : Fin 2, ‖V i z‖ ^ 2 := by
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  have hfm : AEStronglyMeasurable f (volume.restrict K) :=
    hei.aestronglyMeasurable_comp_iff.mp hf.aestronglyMeasurable
  have henergy := m64Observed_energyDensity_integrable Q hQ hb f hfm V hV
  have hnorm : IntegrableOn (fun z => ∑ i : Fin 2, ‖V i z‖ ^ 2) K := by
    simp only [Fin.sum_univ_two]
    exact (hV 0).norm.integrable_sq.add (hV 1).norm.integrable_sq
  rw [← integral_const_mul]
  apply integral_mono_ae henergy (hnorm.const_mul (bound / 2))
  exact ae_of_all _ fun z => by
    have hcol (i : Fin 2) : Q (f z) (V i z) (V i z) ≤ bound * ‖V i z‖ ^ 2 := by
      have hop := (Q (f z)).le_opNorm₂ (V i z) (V i z)
      have hbound := mul_le_mul_of_nonneg_right (hb (f z)) (sq_nonneg ‖V i z‖)
      rw [Real.norm_eq_abs] at hop
      nlinarith [le_abs_self (Q (f z) (V i z) (V i z))]
    simp only [Fin.sum_univ_two]
    nlinarith [hcol 0, hcol 1]

end PoincareConjecture
