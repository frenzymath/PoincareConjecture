import PoincareConjecture.Proofs.M62.Lemma0_2_ScalarEvolution
import PoincareConjecture.Proofs.M62.Lemma0_1_Commutator
import PoincareConjecture.Proofs.M62.Lemma0_2_NormalDecomposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem hasDerivAt_curvatureSquared [T2Space M]
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    HasDerivAt (fun s => m62CurvatureSquared F c s x)
      (m62SpatialEvolutionRhs F c t x) t := by
  have hmem : (x, t) ∈ (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) :=
    ⟨mem_univ _, ht⟩
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun s : ℝ => (x, s)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => c x s) t :=
    ((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime
  have hH : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun s => (⟨c x s, m62CurvatureVector F c s x⟩ : TangentBundle (𝓡 n) M)) t :=
    (((curvature_joint_contMDiff F c hc).contMDiffAt
      (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp t htime
  have h := hasDerivAt_flow_metric_pairing F ht hγ hH hH
  apply h.congr_deriv
  rw [(F.metric t).symm (c x t) (m62CurvatureVector F c t x)
    (rampHorizontalCovariantDerivative (F.connection t) (fun s => c x s)
      (fun s => m62CurvatureVector F c s x) t)]
  rw [curvature_squared_time_pair F c hc ht x]
  dsimp only [m62SpatialEvolutionRhs]
  rw [curvature_squared_arcSecond_eq F c hc ht x,
    spatialDerivative_norm_split F c hc ht x]
  dsimp only [m62TangentRicci]
  ring

theorem spatial_evolution [T2Space M]
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) : M62SpatialEvolution F c where
  speed_positive := fun _ ht x => speed_pos F c hc ht x
  speed_squared := fun _ ht x => hasDerivAt_speed_sq F c hc ht x
  speed_derivative := fun _ ht x => hasDerivAt_speed F c hc ht x
  commutator := fun f hf _ ht x => arc_time_commutator F c hc f hf ht x
  curvature_squared_smooth := curvatureSquared_contDiffOn F c hc
  exact_curvature := fun _ ht x => hasDerivAt_curvatureSquared F c hc ht x

theorem SpacetimeData.curve_laws [T2Space M]
    {F : RicciFlow n M (Set.Icc a b)} (G : SpacetimeData F)
    (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c) : M62CurveLaws G c where
  spatial := spatial_evolution F c hc
  lifted_time := G.lifted_time c hc
  normal_norm := G.normal_norm c hc
  exact_curvature := fun t x => by
    rw [G.spacetimeEvolutionRhs_eq_spatial c hc t x]
    exact hasDerivAt_curvatureSquared F c hc t.property x
  regularized_gradient := fun _ hε t x => G.regularized_gradient_le c hc hε t x

end PoincareConjecture.M62
