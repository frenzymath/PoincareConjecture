import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNaturalGrowthTest












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture





theorem m64ScalarBoundary_indicator_equation
    {U O : Set LoopPlane} (hU : MeasurableSet U) (hO : IsOpen O) (hOU : O ⊆ U)
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict U)) (hb : IntegrableOn b U)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O ∩ {p : LoopPlane | 0 < p 1} →
      (∫ p in U, ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p in U, b p * phi p) :
    let S := O ∩ {p : LoopPlane | 0 < p 1}
    (∀ i, MemLp (S.indicator (F i)) 2 volume) ∧ Integrable (S.indicator b) ∧
      ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ S →
        (∫ p, ∑ i : Fin 2, S.indicator (F i) p *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) = ∫ p, S.indicator b p * phi p := by
  classical
  let S := O ∩ {p : LoopPlane | 0 < p 1}
  have hS : MeasurableSet S := (hO.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous)).measurableSet
  have hSU : S ⊆ U := inter_subset_left.trans hOU
  refine ⟨fun i => (memLp_indicator_iff_restrict hS).mpr
    ((hF i).mono_measure (Measure.restrict_mono hSU le_rfl)),
    (integrable_indicator_iff hS).mpr (hb.mono_set hSU), ?_⟩
  intro phi hp hc hs
  have hD (p : LoopPlane) (hps : p ∉ S) (i : Fin 2) :
      fderiv ℝ phi p (EuclideanSpace.single i 1) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun q => fderiv ℝ phi q (EuclideanSpace.single i 1))
      (fun hm => hps (hs (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) hm)))
  have hphi (p : LoopPlane) (hps : p ∉ S) : phi p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hps (hs hm))
  have hactual := heq phi hp hc hs
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hSU
      (fun p hp => by simp only [hD p hp.2, mul_zero, Finset.sum_const_zero]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hSU
      (fun p hp => by rw [hphi p hp.2, mul_zero])] at hactual
  have hleft : (fun p => ∑ i : Fin 2,
      S.indicator (F i) p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      S.indicator (fun p => ∑ i : Fin 2,
        F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  have hright : (fun p => S.indicator b p * phi p) =
      S.indicator (fun p => b p * phi p) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  rw [hleft, hright, integral_indicator hS, integral_indicator hS]
  exact hactual

end PoincareConjecture
