import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Local Lipschitz control of a finite minimum of branch actions

Morgan--Tian Corollary 6.67 and Claims 6.68-6.69, pp. 139-140.
After compact capture and the inverse theorem produce finitely many
surviving branches, their smooth actions bound the actual minimum from
above and one realizes it at every endpoint. The following elementary
comparison transfers their common Lipschitz bound to that minimum.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

universe u v

namespace PoincareMT.Proofs.M46

/-- An attained lower envelope of functions with one common Lipschitz
bound has the same bound, as used in Corollary 6.67, p. 140. -/
theorem lipschitzOnWith_of_attained_lower_envelope
    {E : Type u} [PseudoMetricSpace E] {ι : Type v}
    {S : Set E} {f : E → ℝ} {g : ι → E → ℝ} {K : ℝ≥0}
    (hupper : ∀ z ∈ S, ∀ i, f z ≤ g i z)
    (hattained : ∀ z ∈ S, ∃ i, f z = g i z)
    (hLip : ∀ i, LipschitzOnWith K (g i) S) : LipschitzOnWith K f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  obtain ⟨i, hi⟩ := hattained z hz
  obtain ⟨j, hj⟩ := hattained w hw
  have hiLip := (hLip i).dist_le_mul z hz w hw
  have hjLip := (hLip j).dist_le_mul z hz w hw
  rw [Real.dist_eq] at hiLip hjLip ⊢
  have hzi := hupper z hz j
  have hwi := hupper w hw i
  have hleft := (abs_le.mp hiLip).1
  have hright := (abs_le.mp hjLip).2
  apply abs_le.mpr
  constructor <;> linarith

/-- Finitely many smooth competing actions give a chart-local
Lipschitz bound whenever one attains the actual minimum at each point,
Corollary 6.67 and Claim 6.69, pp. 139-140. -/
theorem finite_smooth_lower_envelope_locally_lipschitz
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} [Finite ι] {f : E → ℝ} {g : ι → E → ℝ}
    {z : E} {N : Set E} (hN : N ∈ 𝓝 z)
    (hupper : ∀ w ∈ N, ∀ i, f w ≤ g i w)
    (hattained : ∀ w ∈ N, ∃ i, f w = g i w)
    (hsm : ∀ i, ContDiffAt ℝ 1 (g i) z) :
    ∃ S : Set E, IsOpen S ∧ z ∈ S ∧ S ⊆ N ∧
      ∃ K : ℝ≥0, LipschitzOnWith K f S := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose K U hU hLip using fun i => (hsm i).exists_lipschitzOnWith
  let C : ℝ≥0 := Finset.univ.sup K
  have hK (i : ι) : K i ≤ C := Finset.le_sup (Finset.mem_univ i)
  have hcommon : N ∩ ⋂ i, U i ∈ 𝓝 z :=
    inter_mem hN (Filter.iInter_mem.mpr hU)
  obtain ⟨S, hSsub, hS, hzS⟩ := mem_nhds_iff.mp hcommon
  have hSN : S ⊆ N := fun _ hw => (hSsub hw).1
  refine ⟨S, hS, hzS, hSN, C, ?_⟩
  exact lipschitzOnWith_of_attained_lower_envelope
    (fun w hw => hupper w (hSN hw)) (fun w hw => hattained w (hSN hw))
    (fun i => ((hLip i).mono (fun w hw => mem_iInter.mp (hSsub hw).2 i)).weaken (hK i))

end PoincareMT.Proofs.M46
