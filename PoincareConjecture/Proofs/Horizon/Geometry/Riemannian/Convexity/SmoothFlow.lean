import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.FlowContraction
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open PoincareConjecture Filter Set
open scoped ContDiff Topology Manifold Bundle

namespace Poincare.Geometry.Riemannian.Convexity

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ} {g : RiemannianMetric n (E n)}



theorem exists_smooth_normalizedNegGradient_flow
    (D : LeviCivitaData g) {f : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hregular : ∀ y ∈ U, g.inner y (D.gradient f y) (D.gradient f y) ≠ 0)
    {x : E n} (hx : x ∈ U) :
    ∃ (V : Set (E n)) (δ : ℝ) (q : ℝ × E n → E n),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ q (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, q (0, y) = y) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo (-δ) δ,
        q (t, y) ∈ U ∧
          HasDerivAt (fun s => q (s, y)) (normalizedNegGradient D f (q (t, y))) t := by
  have hfield : ContDiffOn ℝ ∞ (normalizedNegGradient D f) U := by
    intro y hy
    have hs := contMDiffAt_normalizedNegGradient D
      (contMDiffAt_iff_contDiffAt.mpr (hf.contDiffAt (hU.mem_nhds hy))) (hregular y hy)
    rw [Bundle.contMDiffAt_totalSpace] at hs
    exact (contMDiffAt_iff_contDiffAt.mp (by simpa using hs.2)).contDiffWithinAt
  obtain ⟨V, δ, Φ, hV, hxV, hVU, hδ, hΦ, hinit, hmaps, hderiv⟩ :=
    Poincare.ODE.LocalFlow.exists_smooth_localFlow hU hfield hx
  refine ⟨V, δ, fun p => Φ (p.2, p.1), hV, hxV, hVU, hδ, ?_, hinit, ?_⟩
  · exact hΦ.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun _ hp => ⟨hp.2, hp.1⟩)
  · intro y hy t ht
    exact ⟨hmaps y hy t ht, hderiv y hy t ht⟩



theorem exists_local_contracting_normalized_flow
    (D : LeviCivitaData g) {f : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {η B : ℝ} (hη : 0 ≤ η)
    (hregular : ∀ y ∈ U, 0 < g.inner y (D.gradient f y) (D.gradient f y))
    (hupper : ∀ y ∈ U, g.inner y (D.gradient f y) (D.gradient f y) ≤ B)
    (hhess : ∀ y ∈ U, ∀ v, mvfderiv (𝓡 n) f y v = 0 →
      η * g.inner y v v ≤ D.hessian f y v v)
    {x : E n} (hx : x ∈ U) :
    ∃ (V : Set (E n)) (δ : ℝ) (q : ℝ × E n → E n),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ q (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, q (0, y) = y) ∧
      (∀ y ∈ V, ∀ t ∈ Ioo (-δ) δ, q (t, y) ∈ U ∧
        HasDerivAt (fun s => q (s, y)) (normalizedNegGradient D f (q (t, y))) t) ∧
      ∀ y ∈ V, ∀ v, mvfderiv (𝓡 n) f y v = 0 → ∀ t ∈ Ico 0 δ,
        f (q (t, y)) = f y - t ∧
        g.inner (q (t, y)) (fderiv ℝ (fun z => q (t, z)) y v)
          (fderiv ℝ (fun z => q (t, z)) y v) ≤
            g.inner y v v * Real.exp (-2 * (η / B) * t) := by
  obtain ⟨V, δ, q, hV, hxV, hVU, hδ, hq, hinit, horbit⟩ :=
    exists_smooth_normalizedNegGradient_flow D hU hf (fun y hy => (hregular y hy).ne') hx
  refine ⟨V, δ, q, hV, hxV, hVU, hδ, hq, hinit, horbit, ?_⟩
  intro y hy v hv t ht
  have hsub : Icc 0 t ⊆ Ioo (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1], hs.2.trans_lt ht.2⟩
  have hqs (s : ℝ) (hs : s ∈ Icc 0 t) : ContDiffAt ℝ ∞ q (s, y) :=
    hq.contDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hsub hs, hy⟩)
  have hfs : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc 0 t,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (q (s, z)) := by
    filter_upwards [hV.mem_nhds hy] with z hz s hs
    exact contMDiffAt_iff_contDiffAt.mpr
      (hf.contDiffAt (hU.mem_nhds (horbit z hz s (hsub hs)).1))
  have hrs : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc 0 t,
      0 < g.inner (q (s, z)) (D.gradient f (q (s, z))) (D.gradient f (q (s, z))) := by
    filter_upwards [hV.mem_nhds hy] with z hz s hs
    exact hregular _ (horbit z hz s (hsub hs)).1
  have hts : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc 0 t,
      HasDerivAt (fun r => q (r, z)) (normalizedNegGradient D f (q (s, z))) s := by
    filter_upwards [hV.mem_nhds hy] with z hz s hs
    exact (horbit z hz s (hsub hs)).2
  refine ⟨?_, ?_⟩
  · have hlevel := comp_normalizedNegGradient_eq_sub D hfs.self_of_nhds
      (fun s hs => (hrs.self_of_nhds s hs).ne') hts.self_of_nhds t ⟨ht.1, le_rfl⟩
    simpa only [hinit y hy, sub_zero] using hlevel
  have he : (fun z => q (0, z)) =ᶠ[𝓝 y] id := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact hinit z hz
  have hd : fderiv ℝ (fun z => q (0, z)) y = ContinuousLinearMap.id ℝ (E n) := by
    rw [he.fderiv_eq, fderiv_id]
  have hinitial : mvfderiv (𝓡 n) f (q (0, y))
      (fderiv ℝ (fun z => q (0, z)) y v) = 0 := by
    rw [hd, ContinuousLinearMap.id_apply]
    rw [hinit y hy]
    exact hv
  have htan (s : ℝ) (hs : s ∈ Icc 0 t) :
      mvfderiv (𝓡 n) f (q (s, y)) (fderiv ℝ (fun z => q (s, z)) y v) = 0 :=
    (normalized_flow_preserves_level_differential D hqs hfs
      (hrs.mono (fun _ hz r hr => (hz r hr).ne')) hts v s hs).trans hinitial
  have hbound := normalized_flow_squared_length_le D hη hqs hfs hrs
    (fun s hs => hupper _ (horbit y hy s (hsub hs)).1) hts v hinitial
    (fun s hs => hhess _ (horbit y hy s (hsub hs)).1 _ (htan s hs)) t ⟨ht.1, le_rfl⟩
  change g.euclideanCoefficients (q (t, y)) _ _ ≤
    g.euclideanCoefficients (q (0, y)) _ _ * _ at hbound
  simp only [hinit y hy, hd, ContinuousLinearMap.id_apply, sub_zero] at hbound
  convert! hbound using 1

end Poincare.Geometry.Riemannian.Convexity
