import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamReplacement












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "v" => m64AnnulusSeamTranslation



theorem m64AnnulusSeamTranslation_norm : ‖v‖ = curvePeriod := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have heq : v = curvePeriod • EuclideanSpace.single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [m64AnnulusSeamTranslation, annulusPoint]
  rw [heq, norm_smul]
  simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos hP]



theorem m64AnnulusSeamDisk_disjoint (a : LoopPlane) {r : ℝ} (hr : 2 * r < curvePeriod) :
    Disjoint (Metric.closedBall a r)
      ((fun p : LoopPlane => p - v) ⁻¹' Metric.closedBall a r) := by
  apply disjoint_left.mpr
  intro p hp hq
  have h1 : dist p a ≤ r := hp
  have h2 : dist (p - v) a ≤ r := hq
  have hdist : dist p (p - v) = curvePeriod := by
    rw [dist_eq_norm, sub_sub_cancel, m64AnnulusSeamTranslation_norm]
  apply (not_le_of_gt hr)
  calc
    curvePeriod = dist p (p - v) := hdist.symm
    _ ≤ dist p a + dist a (p - v) := dist_triangle p a (p - v)
    _ ≤ r + r := add_le_add h1 (by simpa only [dist_comm] using h2)
    _ = 2 * r := (two_mul r).symm

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain



theorem M64ObservedWeakAnnulus.exists_seam_replacement_of_outer_agreement
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (a : LoopPlane)
    {rho : ℝ} (hrho : 0 < rho) (hwidth : 2 * rho < curvePeriod)
    (hKO : Metric.closedBall a rho ⊆ O)
    (hKS : Metric.closedBall a rho ⊆ m64AnnulusSeamDomain)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) O)
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict O,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hmatch : ∀ p : LoopPlane, rho * Real.exp (-1) ≤ dist p a →
      dist p a ≤ rho → f p = m64AnnulusSeamExtend A.map p) :
    ∃ r : ℝ, 0 < r ∧ rho * Real.exp (-1) ≤ r ∧ r ≤ rho ∧
      ∃ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
        B.map = m64AnnulusSeamPatch (Metric.closedBall a r) f A.map ∧
        ∀ i, (B.column i : LoopPlane → E) =ᵐ[volume.restrict S]
          m64AnnulusSeamPatch (Metric.closedBall a r) (V i) (A.column i) := by
  obtain ⟨r, hr, hlo, hhi, hflux⟩ :=
    A.exists_seam_matching_rectangle_circle hO a hrho hKO hKS f V hf hV hw hmatch
  have hsmallO := (Metric.closedBall_subset_closedBall hhi).trans hKO
  have hsmallS := (Metric.closedBall_subset_closedBall hhi).trans hKS
  have hsep := m64AnnulusSeamDisk_disjoint a (r := r) (by linarith)
  refine ⟨r, hr, hlo, hhi, ?_⟩
  exact A.seam_replace Metric.isClosed_closedBall.measurableSet hsmallS hsep f V
    (hf.mono_measure (Measure.restrict_mono hsmallO le_rfl))
    (fun i => (hV i).mono_measure (Measure.restrict_mono hsmallO le_rfl))
    (fun i => (ht i).filter_mono (ae_mono (Measure.restrict_mono hsmallO le_rfl))) hflux

end PoincareConjecture
