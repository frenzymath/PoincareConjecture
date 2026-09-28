import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSplit

set_option autoImplicit false

open Set
open scoped BigOperators

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projectToFace_zero_mix_compl {s : Finset ι} {u v : ι → ℝ}
    (hu : u ∈ barycentricFace s) (hv : v ∈ barycentricFace sᶜ)
    {t : ℝ} (ht : t ≠ 0) :
    projectToFace sᶜ 0 ((1 - t) • u + t • v) = v := by
  have h := projectToFace_zero_mix hv (by simpa using hu)
    (t := 1 - t) (by intro he; apply ht; linarith)
  simpa only [sub_sub_cancel, add_comm] using h

omit [DecidableEq ι] in

theorem convex_barycentricFace (s : Finset ι) : Convex ℝ (barycentricFace s) := by
  intro u hu v hv a b ha hb hab
  refine ⟨convex_stdSimplex ℝ ι hu.1 hv.1 ha hb hab, ?_⟩
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, hu.2 i hi, hv.2 i hi, smul_zero, add_zero]

noncomputable def splitMix (s : Finset ι) (t : ℝ) (q : ι → ℝ) : ι → ℝ :=
  (1 - t) • projectToFace s 0 q + t • projectToFace sᶜ 0 q

theorem splitMix_mem_barycentricFace {s r : Finset ι} {q : ι → ℝ}
    (hq : q ∈ barycentricFace r) (hm : 0 < ∑ i ∈ s, q i)
    (hn : 0 < ∑ i ∈ sᶜ, q i) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    splitMix s t q ∈ barycentricFace r :=
  convex_barycentricFace r (projectToFace_zero_mem_of_mem hq hm)
    (projectToFace_zero_mem_of_mem hq hn) (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem projectToFace_splitMix {s : Finset ι} {q : ι → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hm : 0 < ∑ i ∈ s, q i) (hn : 0 < ∑ i ∈ sᶜ, q i)
    {t : ℝ} (ht : t ≠ 1) :
    projectToFace s 0 (splitMix s t q) = projectToFace s 0 q :=
  projectToFace_zero_mix (projectToFace_zero_mem s hq hm)
    (projectToFace_zero_mem sᶜ hq hn) ht

theorem projectToFace_compl_splitMix {s : Finset ι} {q : ι → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hm : 0 < ∑ i ∈ s, q i) (hn : 0 < ∑ i ∈ sᶜ, q i)
    {t : ℝ} (ht : t ≠ 0) :
    projectToFace sᶜ 0 (splitMix s t q) = projectToFace sᶜ 0 q :=
  projectToFace_zero_mix_compl (projectToFace_zero_mem s hq hm)
    (projectToFace_zero_mem sᶜ hq hn) ht

theorem splitMix_splitMix {s : Finset ι} {q : ι → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hm : 0 < ∑ i ∈ s, q i) (hn : 0 < ∑ i ∈ sᶜ, q i)
    {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (u : ℝ) :
    splitMix s u (splitMix s t q) = splitMix s u q := by
  change (1 - u) • projectToFace s 0 (splitMix s t q) +
    u • projectToFace sᶜ 0 (splitMix s t q) = _
  rw [projectToFace_splitMix hq hm hn ht1, projectToFace_compl_splitMix hq hm hn ht0]
  rfl

theorem splitMix_current {s : Finset ι} {q : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) (hm : 0 < ∑ i ∈ s, q i) (hn : 0 < ∑ i ∈ sᶜ, q i) :
    splitMix s (∑ i ∈ sᶜ, q i) q = q :=
  mix_projectToFace_zero hq hm.ne' hn.ne'

theorem continuousOn_splitMix (s : Finset ι) :
    ContinuousOn (fun p : ℝ × (ι → ℝ) => splitMix s p.1 p.2)
      {p | (∑ i ∈ s, p.2 i) ≠ 0 ∧ (∑ i ∈ sᶜ, p.2 i) ≠ 0} := by
  let D : Set (ℝ × (ι → ℝ)) :=
    {p | (∑ i ∈ s, p.2 i) ≠ 0 ∧ (∑ i ∈ sᶜ, p.2 i) ≠ 0}
  have hleft : ContinuousOn (fun p : ℝ × (ι → ℝ) => projectToFace s 0 p.2) D :=
    (continuousOn_projectToFace_zero s).comp continuous_snd.continuousOn (fun _ hp => hp.1)
  have hright : ContinuousOn (fun p : ℝ × (ι → ℝ) => projectToFace sᶜ 0 p.2) D :=
    (continuousOn_projectToFace_zero sᶜ).comp continuous_snd.continuousOn (fun _ hp => hp.2)
  exact ((continuous_const.sub continuous_fst).continuousOn.smul hleft).add
    (continuous_fst.continuousOn.smul hright)

end StdSimplexCore
