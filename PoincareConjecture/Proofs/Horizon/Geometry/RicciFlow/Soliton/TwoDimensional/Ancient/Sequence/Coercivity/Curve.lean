import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem continuousOn_speed_of_contMDiffOn_one (g : RiemannianMetric n M)
    {γ : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ I) :
    ContinuousOn (fun t => g.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) I := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 0
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro t
    apply contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
        (n := 0) (x := t) (c := (1 : ℝ)))
  have hv : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 0
      (fun t => (⟨γ t, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t (1 : ℝ)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)))) I := by
    have h := (hγ.contMDiffOn_tangentMapWithin (m := 0) (by norm_num)
      hI.uniqueMDiffOn).comp hunit.contMDiffOn (fun t ht => ht)
    apply h.congr
    intro t ht
    simp only [Function.comp_def, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hI.mem_nhds ht)]
  intro t ht
  have hγt := ((hγ t ht).of_le (by norm_num : (0 : ℕ∞ω) ≤ 1)).contMDiffAt
    (hI.mem_nhds ht)
  have hvt := (hv t ht).contMDiffAt (hI.mem_nhds ht)
  have h := (((g.contMDiff (γ t)).of_le (by simp : (0 : ℕ∞ω) ≤ ∞)).comp t hγt).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : M => ℝ) hvt hvt
  have hh := (contMDiffAt_totalSpace.mp h).2
  exact Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
    hh.continuousAt.continuousWithinAt


theorem toReal_edist_endpoints_le_of_interior_bound [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) {γ : ℝ → M} {τ B : ℝ} (hτ : 0 < τ)
    (hγ : ContinuousOn γ (Icc 0 τ))
    (hB : ∀ a b : ℝ, 0 < a → a ≤ b → b < τ → (g.edist (γ a) (γ b)).toReal ≤ B) :
    (g.edist (γ 0) (γ τ)).toReal ≤ B := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < τ / 2 :=
    Ioo_mem_nhdsGT (by positivity)
  have he0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have heτ : Tendsto (fun ε : ℝ => τ - ε) (𝓝[>] 0) (𝓝 τ) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub he0
  have h0 : Tendsto (fun ε : ℝ => γ ε) (𝓝[>] 0) (𝓝 (γ 0)) := by
    apply (hγ 0 ⟨le_rfl, hτ.le⟩).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨he0, hev.mono (fun ε hε => ⟨hε.1.le, by linarith⟩)⟩
  have ht : Tendsto (fun ε : ℝ => γ (τ - ε)) (𝓝[>] 0) (𝓝 (γ τ)) := by
    apply (hγ τ ⟨hτ.le, le_rfl⟩).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨heτ, hev.mono (fun ε hε => ⟨by linarith, by linarith⟩)⟩
  have hd : Tendsto (fun ε : ℝ => g.edist (γ ε) (γ (τ - ε))) (𝓝[>] 0)
      (𝓝 (g.edist (γ 0) (γ τ))) := h0.edist ht
  apply le_of_tendsto ((ENNReal.continuousAt_toReal (g.edist_ne_top _ _)).tendsto.comp hd)
  exact hev.mono (fun ε hε => hB ε (τ - ε) hε.1 (by linarith) (by linarith))

end PoincareConjecture.RiemannianMetric
