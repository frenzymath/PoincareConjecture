import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

theorem m64MemLp_piecewise_of_subset
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {mu : Measure X} {S K : Set X} [DecidablePred (· ∈ K)]
    (hK : MeasurableSet K) (hKS : K ⊆ S)
    {p : ℝ≥0∞} {f g : X → E}
    (hf : MemLp f p (mu.restrict K)) (hg : MemLp g p (mu.restrict S)) :
    MemLp (K.piecewise f g) p (mu.restrict S) := by
  classical
  apply MemLp.piecewise hK
  · rwa [Measure.restrict_restrict hK, inter_eq_left.mpr hKS]
  · exact hg.mono_measure Measure.restrict_le_self

theorem m64Integral_piecewise_of_subset
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {mu : Measure X} {S K : Set X} [DecidablePred (· ∈ K)]
    (hK : MeasurableSet K) (hKS : K ⊆ S)
    {f g : X → E} (hf : IntegrableOn f K mu) (hg : IntegrableOn g S mu) :
    (∫ x in S, K.piecewise f g x ∂mu) =
      (∫ x in S, g x ∂mu) + (∫ x in K, f x ∂mu) - ∫ x in K, g x ∂mu := by
  classical
  have hfirst : IntegrableOn f K (mu.restrict S) := by
    rwa [IntegrableOn, Measure.restrict_restrict hK, inter_eq_left.mpr hKS]
  have hlast : IntegrableOn g Kᶜ (mu.restrict S) :=
    (show Integrable g (mu.restrict S) from hg).mono_measure Measure.restrict_le_self
  rw [integral_piecewise hK hfirst hlast,
    Measure.restrict_restrict hK, inter_eq_left.mpr hKS,
    Measure.restrict_restrict hK.compl]
  have hset : Kᶜ ∩ S = S \ K := by ext x; simp [and_comm]
  rw [hset, setIntegral_sdiff hK hg hKS]
  abel

theorem m64L2_test_integrable
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {mu : Measure X} {u : X → E} {phi : X → ℝ}
    (hu : MemLp u 2 mu) (hp : MemLp phi 2 mu) :
    Integrable (fun x => phi x • u x) mu :=
  memLp_one_iff_integrable.mp (show MemLp (fun x => phi x • u x) 1 mu from MemLp.smul hu hp)

theorem m64Annulus_continuous_memLp_two
    {E : Type*} [NormedAddCommGroup E] {f : LoopPlane → E} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (interior m64AnnulusDomain)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).continuousOn.integrableOn_compact
    m64AnnulusDomain_isCompact |>.mono_set interior_subset

end PoincareConjecture
