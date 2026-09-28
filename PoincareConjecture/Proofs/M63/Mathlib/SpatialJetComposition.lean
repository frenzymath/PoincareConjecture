import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

set_option autoImplicit false

open Set
open scoped ContDiff

theorem contDiffOn_iteratedDeriv_comp_of_spatial_jets
    {Z E F : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set Z} {U : Set E} (hU : IsOpen U) {Φ : E → F}
    {n m : ℕ∞} {k : ℕ} (horder : n + k ≤ m)
    (hΦ : ContDiffOn ℝ m Φ U) {f : Z → ℝ → E} {x : Z → ℝ}
    (hf : ∀ z ∈ S, ContDiffAt ℝ ∞ (f z) (x z))
    (hmem : ∀ z ∈ S, f z (x z) ∈ U)
    (hjets : ∀ j : ℕ, ContDiffOn ℝ n
      (fun z => iteratedDeriv j (f z) (x z)) S) :
    ContDiffOn ℝ n (fun z => iteratedDeriv k (Φ ∘ f z) (x z)) S := by
  classical
  have horder' : (n : ℕ∞ω) + (k : ℕ∞ω) ≤ (m : ℕ∞ω) := by exact_mod_cast horder
  have hkm : (k : ℕ∞ω) ≤ (m : ℕ∞ω) :=
    (le_add_of_nonneg_left (show (0 : ℕ∞ω) ≤ n from bot_le)).trans horder'
  have hzero : ContDiffOn ℝ n (fun z => f z (x z)) S := by
    simpa only [iteratedDeriv_zero] using hjets 0
  have hterm (c : OrderedFinpartition k) : ContDiffOn ℝ n
      (fun z => iteratedFDeriv ℝ c.length Φ (f z (x z))
        (fun j => iteratedDeriv (c.partSize j) (f z) (x z))) S := by
    have hlength : (c.length : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast c.length_le
    have houter : ContDiffOn ℝ n (iteratedFDeriv ℝ c.length Φ) U := by
      intro y hy
      exact ((hΦ.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right
        ((add_le_add le_rfl hlength).trans horder')).contDiffWithinAt
    let B : (E [×c.length]→L[ℝ] F) →L[ℝ] (E [×c.length]→L[ℝ] F) :=
      ContinuousLinearMap.id ℝ _
    have htuple : ContDiffOn ℝ n (fun z => fun _ : Option (Fin c.length) =>
        (iteratedFDeriv ℝ c.length Φ (f z (x z)),
          fun j => iteratedDeriv (c.partSize j) (f z) (x z))) S :=
      contDiffOn_pi.mpr fun _ => (houter.comp hzero hmem).prodMk
        (contDiffOn_pi.mpr fun j => hjets (c.partSize j))
    exact B.continuousMultilinearMapOption.contDiff.comp_contDiffOn htuple
  have hsum := ContDiffOn.sum (s := Finset.univ) (fun c _ => hterm c)
  apply hsum.congr
  intro z hz
  exact iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (hΦ.contDiffAt (hU.mem_nhds (hmem z hz))) ((hf z hz).of_le (by simp)) hkm
