import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.CompactConfinement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open scoped Topology ContDiff Manifold Bundle

namespace Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem hasDerivAt_function_along_neg_gradient_manifold
    (D : LeviCivitaData g) {f : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ t))
    (hγ : IsMIntegralCurveAt (I := 𝓡 n) γ (fun y => -D.gradient f y) t) :
    HasDerivAt (f ∘ γ) (-g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t))) t := by
  have hd := (hf.hasMFDerivAt.comp t hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hi := D.inner_gradient f (γ t) (D.gradient f (γ t))
  change g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)) =
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ t) (D.gradient f (γ t)) at hi
  change HasDerivAt (f ∘ γ)
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ t) ((1 : ℝ) • -D.gradient f (γ t))) t at hd
  simpa only [one_smul, map_neg, ← hi] using! hd



theorem neg_gradient_mem_sublevel_component_manifold
    (D : LeviCivitaData g) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {p : M} {b a c T : ℝ} {γ : ℝ → M} (ha : a < 0) (hT : T < c)
    (hinit : γ 0 ∈ connectedComponentIn (U ∩ f ⁻¹' Iic b) p)
    (hγU : ∀ t ∈ Ioo a c, γ t ∈ U)
    (hγ : IsMIntegralCurveOn (I := 𝓡 n) γ (fun y => -D.gradient f y) (Ioo a c)) :
    ∀ t ∈ Icc 0 T, γ t ∈ connectedComponentIn (U ∩ f ⁻¹' Iic b) p := by
  intro t ht
  have hsub : Icc 0 T ⊆ Ioo a c := fun s hs => ⟨ha.trans_le hs.1, hs.2.trans_lt hT⟩
  have hcont : ContinuousOn γ (Icc 0 T) := (hγ.continuousOn).mono hsub
  have hfc : ContinuousOn (f ∘ γ) (Icc 0 T) :=
    hf.continuousOn.comp hcont (fun s hs => hγU s (hsub hs))
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) := hasDerivAt_function_along_neg_gradient_manifold D
    ((hf.contMDiffAt (hU.mem_nhds (hγU s (hsub hs)))).mdifferentiableAt (by simp))
    (hγ.isMIntegralCurveAt (isOpen_Ioo.mem_nhds (hsub hs)))
  have hanti : AntitoneOn (f ∘ γ) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hfc
      (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hd s (interior_subset hs)).deriv]
    apply neg_nonpos.mpr
    by_cases hz : D.gradient f (γ s) = 0
    · simp [hz]
    · exact (g.pos _ _ hz).le
  have hpath : IsPreconnected (γ '' Icc 0 T) := isPreconnected_Icc.image γ hcont
  have hpathsub : γ '' Icc 0 T ⊆ U ∩ f ⁻¹' Iic b := by
    rintro y ⟨s, hs, rfl⟩
    refine ⟨hγU s (hsub hs), ?_⟩
    exact (hanti ⟨le_rfl, ht.1.trans ht.2⟩ hs hs.1).trans
      (connectedComponentIn_subset _ _ hinit).2
  have hpathC := hpath.subset_connectedComponentIn
    (mem_image_of_mem γ (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩)) hpathsub
  rw [connectedComponentIn_eq hinit]
  exact hpathC (mem_image_of_mem γ ht)



theorem exists_forward_neg_gradient_in_compact_sublevel_component_manifold
    [T2Space M] (D : LeviCivitaData g) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {p x : M} {b : ℝ}
    (hK : IsCompact (connectedComponentIn (U ∩ f ⁻¹' Iic b) p))
    (hx : x ∈ connectedComponentIn (U ∩ f ⁻¹' Iic b) p) :
    ∃ a < 0, ∃ γ : ℝ → M, γ 0 = x ∧ (∀ t ∈ Ioi a, γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ (fun y => -D.gradient f y) (Ioi a) ∧
      ∀ t : ℝ, 0 ≤ t → γ t ∈ connectedComponentIn (U ∩ f ⁻¹' Iic b) p := by
  let K := connectedComponentIn (U ∩ f ⁻¹' Iic b) p
  have hKU : K ⊆ U := (connectedComponentIn_subset _ _).trans inter_subset_left
  have hfield : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (fun y => -D.gradient f y)) U := by
    intro y hy
    exact (D.contMDiffAt_gradient (hf.contMDiffAt (hU.mem_nhds hy))).neg_section.contMDiffWithinAt
  apply Poincare.Manifold.exists_forward_integralCurve_of_compact_confinement hU hK hKU hfield hx
  intro a c ha hc γ hγ0 hγU hγ t ht
  exact neg_gradient_mem_sublevel_component_manifold D hU hf ha ht.2
    (by simpa only [hγ0] using hx) hγU hγ t ⟨ht.1, le_rfl⟩

end Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow
