import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Sweep.Metric.Transport
import PoincareLib.Geometry.Riemannian.Distance.CompactConfinement
import PoincareLib.Geometry.Riemannian.MetricComparison

/-!
# Closed-interval distance bounds from interior curve speed

An interior C1 curve with bounded metric speed is Lipschitz there. Its
continuous endpoint values extend the same bound to the closed interval.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A C1 curve with bounded speed has endpoint distance at most the speed bound times the
interval length. Source: MT Lemma 19.15, pp. 447-449, its weak minimum and sweep
construction. -/
theorem m64_curve_edist_le_speed_Icc (g : RiemannianMetric n M)
    {c : ℝ → M} {s t K : ℝ} (hst : s ≤ t)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 c (Icc s t))
    (hbound : ∀ x ∈ Icc s t,
      g.tangentNorm (c x) (curveVelocity c x) ≤ K) :
    g.edist (c s) (c t) ≤ ENNReal.ofReal K * ENNReal.ofReal (t - s) := by
  have h := g.edist_le_pathELength_of_mem_Icc hc (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
  apply h.trans
  rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm]
  calc
    _ ≤ ∫⁻ _ in Icc s t, ENNReal.ofReal K := by
      apply setLIntegral_mono' measurableSet_Icc
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    _ = _ := by simp [Real.volume_Icc]

/-- Interior C1 regularity and closed-interval continuity suffice for the speed-to-distance
estimate at included endpoints. Source: MT Lemma 19.15, pp. 447-449, its weak minimum and
sweep construction. -/
theorem m64_curve_edist_le_speed_closed [T2Space M]
    (g : RiemannianMetric n M) {c : ℝ → M} {a b K : ℝ} (hK : 0 ≤ K)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 c (Ioo a b))
    (hcont : ContinuousOn c (Icc a b))
    (hbound : ∀ x ∈ Ioo a b, g.tangentNorm (c x) (curveVelocity c x) ≤ K) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      g.edist (c s) (c t) ≤ ENNReal.ofReal K * ENNReal.ofReal |s - t| := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : R1Space M := T2Space.r1Space
  let : RegularSpace M := RegularSpace.of_hasBasis
    isCompact_isClosed_basis_nhds (fun _ _ ⟨_, _, h⟩ => h)
  let : T3Space M := ⟨⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let C : ℝ≥0 := ⟨K, hK⟩
  by_cases hab : a < b
  · have hleft {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
        g.edist (c s) (c t) ≤ ENNReal.ofReal K * ENNReal.ofReal (t - s) := by
      have hsub : Icc s t ⊆ Ioo a b := fun x hx =>
        ⟨hs.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
      exact m64_curve_edist_le_speed_Icc g hst (hc.mono hsub)
        (fun x hx => hbound x (hsub hx))
    have hLip : LipschitzOnWith C c (Ioo a b) := by
      intro s hs t ht
      change g.edist (c s) (c t) ≤ (C : ℝ≥0∞) * edist s t
      rw [ENNReal.coe_nnreal_eq, edist_dist, Real.dist_eq]
      change g.edist (c s) (c t) ≤ ENNReal.ofReal K * ENNReal.ofReal |s - t|
      rcases le_total s t with hst | hts
      · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hleft hs ht hst
      · have h := hleft ht hs hts
        have hsym : g.edist (c s) (c t) = g.edist (c t) (c s) := by
          change edist (c s) (c t) = edist (c t) (c s)
          exact edist_comm _ _
        simpa only [abs_of_nonneg (sub_nonneg.mpr hts), hsym] using h
    have hclosed : LipschitzOnWith C c (Icc a b) := by
      have hc' : ContinuousOn c (closure (Ioo a b)) := by
        simpa only [closure_Ioo hab.ne] using hcont
      simpa only [closure_Ioo hab.ne] using LipschitzOnWith.closure hc' hLip
    intro s hs t ht
    have h := hclosed hs ht
    change g.edist (c s) (c t) ≤ (C : ℝ≥0∞) * edist s t at h
    rw [ENNReal.coe_nnreal_eq, edist_dist, Real.dist_eq] at h
    exact h
  · intro s hs t ht
    have hst : s = t := by linarith [hs.1, hs.2, ht.1, ht.2]
    subst t
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero, mul_zero]
    change edist (c s) (c s) ≤ 0
    exact le_of_eq (edist_self _)

end PoincareMT
