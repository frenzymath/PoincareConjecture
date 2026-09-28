import PoincareConjecture.Proofs.M08.MetricCompactness
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false
set_option maxHeartbeats 5000000

open scoped Manifold ContDiff Bundle intervalIntegral ENNReal

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem curveVelocity_continuous {γ : ℝ → M}
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ) :
    Continuous (fun s ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n)) (γ s) (curveVelocity (n := n) γ s)) := by
  let ι : ℝ → TangentBundle (𝓘(ℝ, ℝ)) ℝ :=
    (tangentBundleModelSpaceHomeomorph (𝓘(ℝ, ℝ))).symm ∘
      (fun s : ℝ ↦ (s, (1 : ℝ)))
  have hι : Continuous ι := by
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(ℝ, ℝ)) (n := ∞)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have ht : Continuous (tangentMap (𝓘(ℝ, ℝ)) (𝓡 n) γ) :=
    hγ.continuous_tangentMap (by norm_num)
  have hcomp : Continuous
      (fun s ↦ tangentMap (𝓘(ℝ, ℝ)) (𝓡 n) γ (ι s)) := ht.comp hι
  have heq : (fun s ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n)) (γ s) (curveVelocity (n := n) γ s)) =
      (fun s ↦ tangentMap (𝓘(ℝ, ℝ)) (𝓡 n) γ (ι s)) := by
    funext s
    simp [ι, tangentMap, curveVelocity, Bundle.TotalSpace.toProd,
      Function.comp_def] <;> rfl
  rw [heq]
  exact hcomp

private theorem metric_inner_continuousOn {J : Set ℝ} {F : RicciFlow n M J}
    {time : ℝ → ℝ} {γ : ℝ → M} {v w : ∀ s, TangentSpace (𝓡 n) (γ s)}
    {S : Set ℝ}
    (hpath : ContinuousOn γ S)
    (htime : Continuous time)
    (hv : ContinuousOn (fun s ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n)) (γ s) (v s)) S)
    (hw : ContinuousOn (fun s ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n)) (γ s) (w s)) S)
    (hdom : Set.MapsTo (fun s ↦ (time s, γ s)) S (J ×ˢ Set.univ)) :
    ContinuousOn (fun s ↦ (F.metric (time s)).inner (γ s) (v s) (w s)) S := by
  let b : ℝ → M := γ
  let ψ : ∀ s, TangentSpace (𝓡 n) (b s) →L[ℝ]
      TangentSpace (𝓡 n) (b s) →L[ℝ] ℝ :=
    fun s ↦ (F.metric (time s)).inner (b s)
  have hpair : ContinuousOn (fun s ↦ (time s, b s)) S :=
    htime.continuousOn.prodMk hpath
  have hmetric : ContinuousOn (fun s ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] ℝ) (b s) (ψ s)) S := by
    exact F.smooth.continuousOn.comp hpair hdom
  have happly := hmetric.clm_bundle_apply₂ (F₃ := ℝ)
    (E₃ := Bundle.Trivial M ℝ) hv hw
  intro s hs
  have hs' := happly s hs
  simp only [FiberBundle.continuousWithinAt_totalSpace] at hs'
  exact hs'.2

private theorem backwardLIntegrand_continuousOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {γ : ℝ → M}
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hmem : ∀ τ ∈ Set.Icc τ₁ τ₂, T - τ ∈ J) :
    ContinuousOn (backwardLIntegrand F T γ) (Set.Icc τ₁ τ₂) := by
  let S : Set ℝ := Set.Icc τ₁ τ₂
  have htime : Continuous (fun s : ℝ ↦ T - s) :=
    continuous_const.sub continuous_id
  have hpath : ContinuousOn γ S := hγ.continuous.continuousOn
  have hvel : ContinuousOn (fun s ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n)) (γ s) (curveVelocity (n := n) γ s)) S :=
    (curveVelocity_continuous hγ).continuousOn
  have hdom : Set.MapsTo (fun s : ℝ ↦ (T - s, γ s)) S (J ×ˢ Set.univ) := by
    intro s hs
    exact ⟨hmem s hs, Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun s ↦ (F.connection (T - s)).scalarCurvature (γ s)) S := by
    have hsmooth := hM04.scalar_regular n M J F
    have hcomp := hsmooth.continuousOn.comp
      (htime.continuousOn.prodMk hpath) hdom
    convert hcomp using 1
    funext s
    rfl
  have hkin : ContinuousOn
      (fun s ↦ (F.metric (T - s)).inner (γ s)
        (curveVelocity (n := n) γ s) (curveVelocity (n := n) γ s)) S := by
    exact metric_inner_continuousOn hpath htime hvel hvel hdom
  have hsum : ContinuousOn
      (fun s ↦ (F.connection (T - s)).scalarCurvature (γ s) +
        (F.metric (T - s)).inner (γ s)
          (curveVelocity (n := n) γ s) (curveVelocity (n := n) γ s)) S :=
    hscalar.add hkin
  have hsqrt : ContinuousOn Real.sqrt S := Real.continuous_sqrt.continuousOn
  exact (hsqrt.mul hsum).congr (fun s hs ↦ by rfl)

theorem exists_backwardTimePath {J : Set ℝ} [ConnectedSpace M] [T3Space M]
    {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
    (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂)
    (hmem : ∀ τ ∈ Set.Icc τ₁ τ₂, T - τ ∈ J)
    (p₁ p₂ : M) : ∃ p : BackwardTimePath F T τ₁ τ₂,
      p.curve τ₁ = p₁ ∧ p.curve τ₂ = p₂ := by
  let g := F.metric T
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hfinite : edist p₁ p₂ ≠ ⊤ := finiteEdistMetric g p₁ p₂
  have hlt : edist p₁ p₂ < ENNReal.ofReal ((edist p₁ p₂).toReal + 1) := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hfinite]
    linarith
  have hpath := Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
    (I := 𝓡 n) (x := p₁) (y := p₂) hlt hordered
  obtain ⟨γ, hγ₁, hγ₂, hγsmooth, hγlen, hγleft, hγright⟩ := hpath
  let p : BackwardTimePath F T τ₁ τ₂ :=
    { curve := γ
      nonnegative := hτ₁
      ordered := hordered
      terminal_mem := hT
      time_mem := hmem
      continuous := by exact hγsmooth.continuous.continuousOn
      regular := by exact hγsmooth.contMDiffOn
      l_integrable := by
        have hc := backwardLIntegrand_continuousOn
          (F := F) (T := T) (τ₁ := τ₁) (τ₂ := τ₂) (γ := γ)
          hγsmooth hM04 hmem
        have hcu : ContinuousOn (backwardLIntegrand F T γ)
            (Set.uIcc τ₁ τ₂) := by
          simpa only [Set.uIcc_of_le hordered.le] using hc
        exact hcu.intervalIntegrable }
  refine ⟨p, ?_, ?_⟩
  · exact hγ₁
  · exact hγ₂

end PoincareConjecture.M08
