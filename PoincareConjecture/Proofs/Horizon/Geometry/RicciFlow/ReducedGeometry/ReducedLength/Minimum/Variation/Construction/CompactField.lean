import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Construction.SquareFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.CompactFieldVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Construction

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem alongCurve_const_smul_contMDiffOn (α : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s)) {U : Set ℝ} (hU : IsOpen U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, Y s⟩ : TangentBundle (𝓡 n) M)) U) (z : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, z • Y s⟩ : TangentBundle (𝓡 n) M)) U := by
  intro s hs
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (α s)
  have hαs := (hα s hs).contMDiffAt (hU.mem_nhds hs)
  have hYs := (hY s hs).contMDiffAt (hU.mem_nhds hs)
  apply ContMDiffAt.contMDiffWithinAt
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hαs, ?_⟩
  have hcoord := (Bundle.contMDiffAt_totalSpace.mp hYs).2
  have hconst : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun _ : ℝ ↦ z) s := contMDiffAt_const
  apply (hconst.smul hcoord).congr_of_eventuallyEq
  have hnear : ∀ᶠ r in 𝓝 s, α r ∈ e.baseSet :=
    hαs.continuousAt (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))
  filter_upwards [hnear] with r hr
  change (e ⟨α r, z • Y r⟩).2 = z • (e ⟨α r, Y r⟩).2
  simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hr, map_smul]

end PoincareConjecture.ReducedLengthMinimum.Variation.Construction

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variation.Geometry ReducedLengthMinimum.Variation.Construction

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_initialFixedLVariation_of_smooth_field (K : AncientKappaSolution 2 M)
    {τ : ℝ} (p : BackwardTimePath K.flow 0 0 τ) (α : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 2) (α s)) (U : Set ℝ)
    (hU : IsOpen U) (hIU : Icc 0 (Real.sqrt τ) ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ α U)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 2)) ∞
      (fun s ↦ (⟨α s, Y s⟩ : TangentBundle (𝓡 2) M)) U)
    (hagrees : ∀ s ∈ Icc 0 (Real.sqrt τ), α s = p.curve (s ^ 2))
    (hY0 : Y 0 = 0) :
    ∃ V : InitialFixedLVariation K.flow 0 0 τ p,
      V.toLVariation.baseSquareCurve = α ∧
        ∀ s ∈ Icc 0 (Real.sqrt τ),
          (squareVariationField V.toLVariation s : EuclideanSpace ℝ (Fin 2)) = Y s := by
  let Ylin : ∀ s, ℝ →L[ℝ] TangentSpace (𝓡 2) (α s) :=
    fun s ↦ ContinuousLinearMap.toSpanSingleton ℝ (Y s)
  have hYlin (z : ℝ) : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 2)) ∞
      (fun s ↦ (⟨α s, Ylin s z⟩ : TangentBundle (𝓡 2) M)) U :=
    alongCurve_const_smul_contMDiffOn α Y hU hα hY z
  obtain ⟨f, Ω, N, hΩ, hN, h0N, hIN, hf, hcenter, hfixed, hvelocity⟩ :=
    exists_smooth_family_of_compact_linear_field α Ylin U (Icc 0 (Real.sqrt τ))
      hU isCompact_Icc hIU hα hYlin
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds h0N)
  have hparam : Ioo (-ρ) ρ ⊆ N := by
    intro z hz
    apply hρN
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hz
  have hrectangle : Icc 0 (Real.sqrt τ) ×ˢ Ioo (-ρ) ρ ⊆ Ω :=
    fun z hz ↦ hIN ⟨hz.1, hparam hz.2⟩
  have hf' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 2) ∞ f Ω := by
    convert! hf using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hYlin0 : Ylin 0 = 0 := by
    ext z
    simp [Ylin, hY0]
  obtain ⟨V, _, hVf, _, _⟩ := K.exists_initialFixedLVariation_of_smoothSquareFamily
    p f Ω hΩ hf' ρ hρ hrectangle
    (fun s hs ↦ (hcenter s).trans (hagrees s hs))
    (fun z _ ↦ (hfixed 0 hYlin0 z).trans (hcenter 0).symm)
  refine ⟨V, funext (fun s ↦ (hVf s 0).trans (hcenter s)), ?_⟩
  intro s hs
  have hfield : (squareVariationField V.toLVariation s : EuclideanSpace ℝ (Fin 2)) =
      curveVelocity (n := 2) (fun z ↦ f (s, z)) 0 :=
    congrArg (fun γ : ℝ → M ↦ (curveVelocity γ 0 : EuclideanSpace ℝ (Fin 2)))
      (funext (hVf s))
  rw [hfield]
  have hc : (fun u : ℝ ↦ f (s, u • (1 : ℝ))) = (fun u ↦ f (s, u)) := by
    funext u
    simp only [smul_eq_mul, mul_one]
  have hv := hvelocity s hs (1 : ℝ)
  rw [hc] at hv
  simpa only [Ylin, ContinuousLinearMap.toSpanSingleton_apply_one] using hv

end PoincareConjecture.AncientKappaSolution
