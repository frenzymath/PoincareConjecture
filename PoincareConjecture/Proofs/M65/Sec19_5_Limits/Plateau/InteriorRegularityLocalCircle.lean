import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalPolar
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65LocalWeakMap

open M65Interior

private theorem closedTarget_of_ae {E : Type*} [PseudoMetricSpace E]
    {S : Set E} (hS : IsClosed S) (hS' : S.Nonempty) {a b : ℝ} (hab : a < b)
    {v : ℝ → E} (hv : ContinuousOn v (Icc a b))
    (hmem : ∀ᵐ t ∂volume.restrict (Icc a b), v t ∈ S) : MapsTo v (Icc a b) S := by
  have hzero : (fun t => infDist (v t) S) =ᵐ[volume.restrict (Icc a b)] fun _ => (0 : ℝ) :=
    hmem.mono (fun _ ht => infDist_zero_of_mem ht)
  have heq := Measure.eqOn_of_ae_eq hzero
    ((continuous_infDist_pt S).comp_continuousOn hv) continuousOn_const
    (closure_interior_Icc hab.ne).symm.subset
  intro t ht
  exact (hS.mem_iff_infDist_zero hS').mpr (heq ht)

theorem polar_continuous_circle {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (hU : IsOpen U) (he : IsClosed (range e))
    (x : LoopPlane) {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (hRU : closedBall x R ⊆ U) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      MemLp (fun t => (-r * Real.sin t) • F.derivative 0 (polarPlane x (r, t)) +
        (r * Real.cos t) • F.derivative 1 (polarPlane x (r, t))) 2
          (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      ∃ v : ℝ → EuclideanSpace ℝ (Fin N),
        ContinuousOn v (Icc (-Real.pi) Real.pi) ∧ v (-Real.pi) = v Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
          fun t => e (F.value (polarPlane x (r, t)))) ∧
        MapsTo v (Icc (-Real.pi) Real.pi) (range e) ∧
        (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) (-Real.pi) Real.pi) ∧
        ∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          v t - v s = ∫ θ in s..t,
            (-r * Real.sin θ) • F.derivative 0 (polarPlane x (r, θ)) +
              (r * Real.cos θ) • F.derivative 1 (polarPlane x (r, θ)) := by
  have hπ : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  filter_upwards [ae_all_iff.mpr (fun j => F.polar_coordinate_AC hU x hε hR hRU j)]
    with r hr
  choose v hv hvu hvp hvi using fun j => (hr j).2
  let V (t : ℝ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun j => v j t)
  let d (t : ℝ) := (-r * Real.sin t) • F.derivative 0 (polarPlane x (r, t)) +
    (r * Real.cos t) • F.derivative 1 (polarPlane x (r, t))
  have hm : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    apply MemLp.of_eval_piLp
    intro j
    exact (hr j).1
  have hcont : ContinuousOn V (Icc (-Real.pi) Real.pi) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp_continuousOn
      (continuousOn_pi.mpr (fun j => by
        simpa only [uIcc_of_le hπ.le] using (hv j).continuousOn))
  have hAE : V =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => e (F.value (polarPlane x (r, t))) := by
    filter_upwards [ae_all_iff.mpr hvu] with t ht
    ext j
    exact ht j
  have hmaps : MapsTo V (Icc (-Real.pi) Real.pi) (range e) :=
    closedTarget_of_ae he ⟨e (F.value x), ⟨F.value x, rfl⟩⟩ hπ hcont
      (hAE.mono (fun t ht => ht ▸ mem_range_self _))
  refine ⟨hm, V, hcont, ?_, hAE, hmaps, fun j => hv j, ?_⟩
  · ext j
    exact hvp j
  · intro s hs t ht
    have hdi : IntegrableOn d (Icc (-Real.pi) Real.pi) := hm.integrable (by norm_num)
    have hi : IntervalIntegrable d volume s t :=
      (hdi.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
    ext j
    change v j t - v j s = (EuclideanSpace.proj j) (∫ θ in s..t, d θ)
    rw [← (EuclideanSpace.proj j).intervalIntegral_comp_comm hi]
    exact hvi j s hs t ht

end PoincareConjecture.M65LocalWeakMap
