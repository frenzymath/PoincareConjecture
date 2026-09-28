import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.Continuity.AreaComparison
import PoincareConjecture.Statements.M66
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Energy.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m66_familyWidth_le_of_metric_le [T2Space M] [SecondCountableTopology M]
    (hM61 : M61RawWidthCore.{u}) (hcompact : IsCompact (univ : Set M))
    (g h : RiemannianMetric 3 M) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ c * g.inner x v v)
    {d : ℝ} (hd : 0 < d)
    (hreverse : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ d * h.inner x v v)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily F) : m61FamilyWidth h F ≤ c * m61FamilyWidth g F := by
  obtain ⟨a, ha⟩ := (hM61.family h hcompact F hnull).attained
  rw [← ha]
  exact (m66_fillingArea_le_of_metric_le g h hc hbound hd hreverse (F a)).trans
    (mul_le_mul_of_nonneg_left
      (le_csSup (hM61.family g hcompact F hnull).bounded_above ⟨a, rfl⟩) hc.le)

theorem m66_freeClassWidth_le_of_metric_le [T2Space M] [SecondCountableTopology M]
    (hM61 : M61RawWidthCore.{u}) (hcompact : IsCompact (univ : Set M))
    (g h : RiemannianMetric 3 M) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ c * g.inner x v v)
    {d : ℝ} (hd : 0 < d)
    (hreverse : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ d * h.inner x v v)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily F) :
    m61FreeClassWidth h F ≤ c * m61FreeClassWidth g F := by
  have hle : m61FreeClassWidth h F / c ≤ m61FreeClassWidth g F := by
    apply le_csInf (hM61.free_class g hcompact F hnull).nonempty
    rintro _ ⟨G, hG, hFG, rfl⟩
    apply (div_le_iff₀ hc).mpr
    calc
      _ ≤ m61FamilyWidth h G := (hM61.free_class h hcompact F hnull).le_member G hG hFG
      _ ≤ c * m61FamilyWidth g G :=
        m66_familyWidth_le_of_metric_le hM61 hcompact g h hc hbound hd hreverse G hG
      _ = _ := mul_comm _ _
  exact (div_le_iff₀ hc).mp hle |>.trans_eq (mul_comm _ _)

theorem m66Width_continuousAt (hM61 : M61RawWidthCore.{u})
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁) (t : Icc t₀ t₁) :
    ContinuousAt (m66Width P) t := by
  let : T2Space M := P.hausdorff
  let : SecondCountableTopology M := P.second_countable
  have hcont : ContinuousOn
      (fun p : ℝ × M => (P.flow.connection p.1).curvatureTensorNorm p.2)
      (Icc t₀ t₁ ×ˢ univ) := by
    have h := (RicciFlowAnalysis.contMDiffOn_flow_curvatureDerivativeEnergy P.flow 0).continuousOn.sqrt
    apply h.congr
    intro p _hp
    dsimp only
    rw [LeviCivitaData.horizon_curvatureDerivativeNorm_zero]
    exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod P.compact).exists_bound_of_continuousOn hcont
  let D := 3 * max B 0
  have hcurv (r : ℝ) (hr : r ∈ Icc t₀ t₁) (x : M) :
      (P.flow.connection r).curvatureTensorNorm x ≤ max B 0 :=
    (le_abs_self _).trans ((hB (r, x) ⟨hr, mem_univ x⟩).trans (le_max_left _ _))
  have hRic (r : ℝ) (hr : r ∈ Icc t₀ t₁) (x : M)
      (v : TangentSpace (𝓡 3) x) :
      |(P.flow.connection r).ricci x v v| ≤ D * (P.flow.metric r).inner x v v := by
    have hv : 0 ≤ (P.flow.metric r).inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact ((P.flow.metric r).pos x v hv).le
    have hfactor : (3 : ℝ) * (P.flow.connection r).curvatureTensorNorm x ≤ D :=
      mul_le_mul_of_nonneg_left (hcurv r hr x) (by norm_num)
    exact (RicciFlowAnalysis.abs_ricci_le_curvatureTensorNorm (P.flow.connection r) x v).trans
      (mul_le_mul_of_nonneg_right hfactor hv)
  have hwidth (a b : Icc t₀ t₁) :
      m66Width P b ≤ Real.exp ((2 * D) * |b.1 - a.1|) * m66Width P a := by
    apply m66_freeClassWidth_le_of_metric_le hM61 P.compact
      (P.flow.metric a.1) (P.flow.metric b.1) (Real.exp_pos _)
      (fun x v => (P.flow.metric_inner_self_exp_bounds (convex_Icc t₀ t₁) Subset.rfl
        x v D (fun r hr => hRic r hr x v) a.2 b.2).2)
      (Real.exp_pos ((2 * D) * |a.1 - b.1|))
      (fun x v => (P.flow.metric_inner_self_exp_bounds (convex_Icc t₀ t₁) Subset.rfl
        x v D (fun r hr => hRic r hr x v) b.2 a.2).2) P.family P.family_null
  let E : Icc t₀ t₁ → ℝ := fun s => Real.exp ((2 * D) * |s.1 - t.1|)
  have hE : Continuous E := Real.continuous_exp.comp
    ((continuous_subtype_val.sub continuous_const).abs.const_mul (2 * D))
  have hEpos (s : Icc t₀ t₁) : 0 < E s := Real.exp_pos _
  have hEt : E t = 1 := by simp [E]
  have hupper (s : Icc t₀ t₁) : m66Width P s ≤ E s * m66Width P t := hwidth t s
  have hlower (s : Icc t₀ t₁) : m66Width P t / E s ≤ m66Width P s := by
    apply (div_le_iff₀ (hEpos s)).mpr
    have h := hwidth s t
    simpa only [E, abs_sub_comm t.1 s.1, mul_comm] using h
  have hconstant : ContinuousAt (fun _ : Icc t₀ t₁ => m66Width P t) t := continuousAt_const
  have hlowlim : Tendsto (fun s => m66Width P t / E s) (𝓝 t) (𝓝 (m66Width P t)) := by
    have hh : Tendsto (fun s => m66Width P t / E s) (𝓝 t)
        (𝓝 (m66Width P t / E t)) :=
      hconstant.tendsto.div hE.continuousAt.tendsto (hEpos t).ne'
    simpa only [hEt, div_one] using hh
  have huplim : Tendsto (fun s => E s * m66Width P t) (𝓝 t) (𝓝 (m66Width P t)) := by
    have hh : Tendsto (fun s => E s * m66Width P t) (𝓝 t)
        (𝓝 (E t * m66Width P t)) := hE.continuousAt.tendsto.mul hconstant.tendsto
    simpa only [hEt, one_mul] using hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowlim huplim hlower hupper

end PoincareConjecture
