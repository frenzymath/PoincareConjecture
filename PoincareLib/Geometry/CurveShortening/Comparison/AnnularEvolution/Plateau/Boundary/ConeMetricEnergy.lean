import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.ReplacementEnergy

/-!
# Metric energy of the actual observed replacement

The bounded observed metric controls the constructed L2 columns. The
target's measurability is recovered through its genuine observation
embedding, so the integral estimate concerns actual admissible data.
Source: Morrey ICM pp. 183-185; M64 phase-cone normalization derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Topology

namespace PoincareMT

/-- The actual observed metric energy of a replacement is bounded by its actual squared
column norm, with all integrability supplied by L2. Proof expansion for Morgan-Tian (2007),
Lemma 19.15, pp. 447-449; M64 derivation 2026-09-26-phase-cone-normalization.md. -/
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

end PoincareMT
