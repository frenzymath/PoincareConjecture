import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Endpoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section

namespace PoincareConjecture.CoordinateExponential

open Set Metric Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}

namespace LocalFlowData

theorem exists_openPartialHomeomorph [CompleteSpace E] (D : LocalFlowData B U x) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e.source ⊆ D.domain ∧ (e : E → E) = D.exponential ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hf := D.smooth_exponential.contDiffAt (D.isOpen_domain.mem_nhds D.zero_mem_domain)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hfd : ContinuousAt (fderiv ℝ D.exponential) 0 :=
    (hf.fderiv_right (m := 0) (by simp)).continuousAt
  have hinvertible : {v : E | ∃ A : E ≃L[ℝ] E,
      (A : E →L[ℝ] E) = fderiv ℝ D.exponential v} ∈ 𝓝 0 := by
    have h := (ContinuousLinearEquiv.refl ℝ E).nhds
    change Set.range (fun A : E ≃L[ℝ] E => (A : E →L[ℝ] E)) ∈
      𝓝 (ContinuousLinearMap.id ℝ E) at h
    rw [← D.hasFDerivAt_exponential_zero.fderiv] at h
    exact hfd.preimage_mem_nhds h
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (D.isOpen_domain.mem_nhds D.zero_mem_domain) hinvertible)
  let H := hf.toOpenPartialHomeomorph D.exponential
    (f' := ContinuousLinearEquiv.refl ℝ E) D.hasFDerivAt_exponential_zero hn
  let e := H.restrOpen (ball 0 r) isOpen_ball
  have hsource : e.source ⊆ D.domain := fun v hv => (hsub hv.2).1
  have heq : (e : E → E) = D.exponential := rfl
  refine ⟨e, ⟨hf.mem_toOpenPartialHomeomorph_source (f' := ContinuousLinearEquiv.refl ℝ E)
    D.hasFDerivAt_exponential_zero hn, mem_ball_self hr⟩,
    hsource, heq, ?_, ?_⟩
  · exact D.smooth_exponential.mono hsource
  · intro y hy
    have hys := e.map_target hy
    obtain ⟨A, hA⟩ := (hsub hys.2).2
    have hsmooth : ContDiffAt ℝ ∞ e (e.symm y) :=
      D.smooth_exponential.contDiffAt (D.isOpen_domain.mem_nhds (hsource hys))
    have hderiv : HasFDerivAt e (A : E →L[ℝ] E) (e.symm y) := by
      rw [hA]
      exact (hsmooth.differentiableAt hn).hasFDerivAt
    exact (e.contDiffAt_symm hy hderiv hsmooth).contDiffWithinAt

end LocalFlowData

theorem exists_local_exponential [FiniteDimensional ℝ E]
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ u v, B y u v = B y v u) (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = x ∧ e.target ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
      ∃ Γ : E × ℝ → E × E,
        ContDiffOn ℝ ∞ Γ (e.source ×ˢ Ioo (-2 : ℝ) 2) ∧
        ∀ v ∈ e.source,
          Γ (v, 0) = (x, v) ∧ (Γ (v, 1)).1 = e v ∧
          ∀ t ∈ Ioo (-2 : ℝ) 2,
            (Γ (v, t)).1 ∈ U ∧
            HasDerivAt (fun s => Γ (v, s))
              (coordinateGeodesicField B (Γ (v, t))) t := by
  obtain ⟨D⟩ := exists_localFlowData hU hB hinv hsymm hx
  obtain ⟨e, hzero, hsource, heq, hsmooth, hinverse⟩ := D.exists_openPartialHomeomorph
  have hezero : e 0 = x := by rw [heq]; exact D.exponential_zero
  have htarget : e.target ⊆ U := by
    intro y hy
    have h := D.trajectory_mem (hsource (e.map_target hy)) (t := 1) (by norm_num)
    rw [D.trajectory_endpoint, ← heq, e.right_inv hy] at h
    exact h
  refine ⟨e, hzero, hezero, htarget, hsmooth, hinverse, ?_,
    (fun p => D.trajectory p.1 p.2), ?_, ?_⟩
  · rw [heq]
    exact D.hasFDerivAt_exponential_zero
  · exact D.smooth_trajectory.mono (Set.prod_mono hsource Subset.rfl)
  · intro v hv
    refine ⟨D.trajectory_initial (hsource hv), ?_, ?_⟩
    · rw [D.trajectory_endpoint, heq]
    · intro t ht
      exact ⟨D.trajectory_mem (hsource hv) ht, D.trajectory_hasDerivAt (hsource hv) ht⟩

end PoincareConjecture.CoordinateExponential
