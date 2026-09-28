import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlExtension
import PoincareConjecture.Proofs.M34.Standard.NeckSharpMetricComparisonPath
import PoincareConjecture.Proofs.M34.Mathlib.LastCrossingLevel

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem collar_height_le_pathELength_of_axial_speed
    {A : ℝ} (hA : 0 ≤ A)
    (hspeed : ∀ x ∈ N.end_neck.carrier, ∀ v : TangentSpace (𝓡 3) x,
      |(mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.end_neck.coordinate_inverse x v).2| ≤
        A * g.tangentNorm x v)
    {c d b : ℝ} (hc : -N.epsilon⁻¹ < c) (hcd : c < d) (hdb : d < b)
    (hb : b < N.epsilon⁻¹) {γ : ℝ → M} {s t : ℝ} (hst : s ≤ t)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc s t))
    (hmem : MapsTo γ (Icc s t) N.carrier)
    (hstart : γ s ∈ N.closed_core)
    (hfinish : γ t ∈ frontier (N.recutCarrier b)) :
    ENNReal.ofReal (b - d) ≤
      ENNReal.ofReal A * g.pathELength γ s t := by
  have hcont : ContinuousOn (N.collarHeight c ∘ γ) (Icc s t) :=
    (N.collarHeight_continuousOn hc (hcd.trans (hdb.trans hb))).comp hγ.continuousOn hmem
  have hstartH : N.collarHeight c (γ s) = c :=
    N.collarHeight_eq_of_mem_recut (Or.inl hstart)
  have hfinishH : N.collarHeight c (γ t) = b :=
    N.collarHeight_eq_of_mem_frontier (hc.trans (hcd.trans hdb)) hb (hcd.trans hdb).le hfinish
  obtain ⟨u, hu, hulevel, hafter⟩ := hcont.exists_last_eq_of_lt hst
    (by simpa only [Function.comp_apply, hstartH] using hcd.le)
    (by simpa only [Function.comp_apply, hfinishH] using hdb)
  change N.collarHeight c (γ u) = d at hulevel
  have hend : MapsTo γ (Icc u t) N.end_neck.carrier := by
    intro v hv
    have hcut : c < N.collarHeight c (γ v) := by
      rcases hv.1.eq_or_lt with h | h
      · subst v
        exact hulevel.symm ▸ hcd
      · exact hcd.trans (hafter v ⟨h, hv.2⟩)
    exact (N.collarHeight_above_cutoff hcut).1
  have huH : (N.end_neck.coordinate_inverse (γ u)).2 = d := by
    have hcut : c < N.collarHeight c (γ u) := by
      exact hulevel.symm ▸ hcd
    exact (N.collarHeight_above_cutoff hcut).2.symm.trans hulevel
  have htH : (N.end_neck.coordinate_inverse (γ t)).2 = b := by
    have hcut : c < N.collarHeight c (γ t) := hfinishH.symm ▸ hcd.trans hdb
    exact (N.collarHeight_above_cutoff hcut).2.symm.trans hfinishH
  have hlength := N.end_neck.height_displacement_le_pathELength_of_axial_speed hA hspeed hu.2.le
    (hγ.mono (Icc_subset_Icc_left hu.1)) hend
  rw [htH, huH, abs_of_pos (sub_pos.mpr hdb)] at hlength
  have hmono : g.pathELength γ u t ≤ g.pathELength γ s t := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.pathELength_mono hu.1 le_rfl
  exact hlength.trans (mul_le_mul' le_rfl hmono)

theorem collar_height_le_pathELength
    {c d b : ℝ} (hc : -N.epsilon⁻¹ < c) (hcd : c < d) (hdb : d < b)
    (hb : b < N.epsilon⁻¹) {γ : ℝ → M} {s t : ℝ} (hst : s ≤ t)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc s t))
    (hmem : MapsTo γ (Icc s t) N.carrier)
    (hstart : γ s ∈ N.closed_core)
    (hfinish : γ t ∈ frontier (N.recutCarrier b)) :
    ENNReal.ofReal (b - d) ≤
      ENNReal.ofReal (2 / N.end_neck.scale) * g.pathELength γ s t := by
  exact N.collar_height_le_pathELength_of_axial_speed
    (div_nonneg (by norm_num) N.end_neck.scale_pos.le)
    (fun _ hx v => N.end_neck.coordinate_inverse_axial_le_tangentNorm hx v)
    hc hcd hdb hb hst hγ hmem hstart hfinish

end PoincareConjecture.CapCertificate
