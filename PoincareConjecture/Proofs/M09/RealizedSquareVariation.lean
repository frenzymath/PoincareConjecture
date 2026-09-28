import PoincareConjecture.Proofs.M09.CompactFieldVariation
import PoincareConjecture.Proofs.M09.ScaledAdaptedField
import PoincareConjecture.Proofs.M09.SmoothSquareVariation

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem exists_initialFixedLVariation_of_smooth_field
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (Y : ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s)) (U : Set ℝ)
    (hU : IsOpen U) (hKU : Set.Icc 0 (Real.sqrt b) ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) U)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨A.squareFamily Z s, Y s⟩ : TangentBundle (𝓡 n) M)) U)
    (hY0 : Y 0 = 0) :
    ∃ V : InitialFixedLVariation F T 0 b (A.path Z b hb hmax),
      V.toLVariation.baseSquareCurve = A.squareFamily Z ∧
        ∀ s ∈ Set.Icc 0 (Real.sqrt b), (squareVariationField V.toLVariation s : E) = Y s := by
  let Ylin : ∀ s, ℝ →L[ℝ] TangentSpace (𝓡 n) (A.squareFamily Z s) :=
    fun s ↦ ContinuousLinearMap.toSpanSingleton ℝ (Y s)
  have hYlin (z : ℝ) : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨A.squareFamily Z s, Ylin s z⟩ : TangentBundle (𝓡 n) M)) U :=
    field_smul_smooth (A.squareFamily Z) Y (fun _ ↦ z) U hU hα contDiffOn_const hY
  obtain ⟨f, Ω, N, hΩ, hN, h0N, hKN, hf, hcenter, hfixed, hvelocity⟩ :=
    exists_smooth_family_of_compact_linear_field (A.squareFamily Z) Ylin U
      (Set.Icc 0 (Real.sqrt b)) hU isCompact_Icc hKU hα hYlin
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds h0N)
  have hparam : Set.Ioo (-ρ) ρ ⊆ N := by
    intro z hz
    apply hρN
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hz
  have hrectangle : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ Ω :=
    fun z hz ↦ hKN ⟨hz.1, hparam hz.2⟩
  have hf' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ f Ω := by
    convert! hf using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hYlin0 : Ylin 0 = 0 := by
    ext z
    simp [Ylin, hY0]
  obtain ⟨V, _, hVf, _, _⟩ := exists_initialFixedLVariation_of_smoothSquareFamily
    hM04 hτmax hwindow A Z b hb hmax f Ω hΩ hf' ρ hρ hrectangle
    (fun s _ ↦ hcenter s) (fun z _ ↦ (hfixed 0 hYlin0 z).trans (hcenter 0).symm)
  refine ⟨V, funext (fun s ↦ (hVf s 0).trans (hcenter s)), ?_⟩
  intro s hs
  have hfield : (squareVariationField V.toLVariation s : E) =
      curveVelocity (n := n) (fun z ↦ f (s, z)) 0 :=
    congrArg (fun γ : ℝ → M ↦ (curveVelocity γ 0 : E)) (funext (hVf s))
  rw [hfield]
  have hc : (fun u : ℝ ↦ f (s, u • (1 : ℝ))) = (fun u ↦ f (s, u)) := by
    funext u
    simp only [smul_eq_mul, mul_one]
  have hv := hvelocity s hs (1 : ℝ)
  rw [hc] at hv
  simpa only [Ylin, ContinuousLinearMap.toSpanSingleton_apply_one] using hv

end PoincareConjecture.Proofs.M09
