import PoincareConjecture.Proofs.M14.Mathlib.InitialSliceInjectivity
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeDifferentialGauge
import PoincareConjecture.Proofs.M14.Sec6_3_InitialGaugeNeighborhood
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialSlices

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space {p : G.Point} : T2Space (G.Horizontal p) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal p

attribute [local instance] horizontal_t2Space

theorem exists_open_smallTime_differential_bijective
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {S : ℝ}
    (hS : 0 < S) (hsurv : (Z, S) ∈ E.domain) :
    ∃ U : Set (G.Horizontal x), IsOpen U ∧ Z ∈ U ∧
      ∃ d : ℝ, 0 < d ∧ d ≤ S ∧
        ∀ W ∈ U, ∀ s ∈ Ioc 0 d,
          ∃ hs : (W, s) ∈ E.domain, Function.Bijective (E.differential W s hs) := by
  obtain ⟨b, ⟨t₀, x₀⟩, rfl⟩ := G.gaugeCover.covers x
  let base := (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal base) :=
    (metric.toCore base).toNormedAddCommGroupOfTopology
      (metric.continuousAt base) (metric.isVonNBounded base)
  let : InnerProductSpace ℝ (G.Horizontal base) :=
    .ofCoreOfTopology (metric.toCore base) (metric.continuousAt base) (metric.isVonNBounded base)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal base) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal base
  let U : Set (G.Horizontal base) := {A | (A, S) ∈ E.domain}
  have hU : IsOpen U := exponentialFamily_domain_slice_isOpen E S
  have hZU : Z ∈ U := hsurv
  have htube : U ×ˢ Icc 0 S ⊆ E.domain := fun z hz =>
    (E.maximal_lifetime z.1).out (E.domain_zero z.1) hz.1 hz.2
  obtain ⟨N, hN, hZN, hNU, d, hd, hdS, β, hβ, hrec, _, hzero⟩ :=
    exists_smooth_initial_gaugeFamily b t₀ x₀ hU hZU hS
      (fun z : G.Horizontal base × ℝ => E.gamma z.1 z.2)
      (E.family_smooth.mono htube) (fun A _ => E.gamma_at_zero A)
  let f : ℝ × G.Horizontal base → EuclideanSpace ℝ (Fin n) :=
    fun z => (β (z.2, z.1)).2.val
  have hf : ContDiffOn ℝ ∞ f (Icc 0 d ×ˢ N) := by
    have hval : ContMDiff (𝓡 n) (𝓡 n) ∞
        (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) :=
      contMDiff_subtype_val
    have hq := hval.comp_contMDiffOn (fun z hz => (hβ z hz).snd)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hq
    exact hq.contDiffOn.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hz => ⟨hz.2, hz.1⟩)
  let j := (G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀
  let L : G.Horizontal base →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (2 : ℝ) • j.symm.toContinuousLinearMap
  have hL : Function.Injective L :=
    (smul_right_injective (EuclideanSpace ℝ (Fin n)) (by norm_num : (2 : ℝ) ≠ 0)).comp
      j.symm.injective
  have hfzero (A : G.Horizontal base) (hA : A ∈ N) : f (0, A) = x₀.val :=
    congrArg (fun z => z.2.val) (hzero A hA)
  have hfvelocity (A : G.Horizontal base) (hA : A ∈ N) :
      derivWithin (fun s => f (s, A)) (Icc 0 d) 0 = L A := by
    exact exponentialGauge_initial_velocity b t₀ x₀ E hS hd hdS
      (htube ⟨hNU hA, hS.le, le_rfl⟩)
      (hβ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun _ hs => ⟨hA, hs⟩))
      (fun s hs => hrec (A, s) ⟨hA, hs⟩) (hzero A hA)
  obtain ⟨V, hV, hZV, hVN, e, he, hed, hgood⟩ :=
    exists_open_initial_sliceDerivative_injective hN hZN hd f hf x₀.val hfzero L hL
      hfvelocity
  refine ⟨V, hV, hZV, e, he, hed.trans hdS, ?_⟩
  intro W hW s hs
  have hsD : s ∈ Icc 0 d := ⟨hs.1.le, hs.2.trans hed⟩
  have hWN : W ∈ N := hVN hW
  have hWs : (W, s) ∈ E.domain := htube ⟨hNU hWN, hs.1.le, hsD.2.trans hdS⟩
  refine ⟨hWs, ?_⟩
  have hslice : ContMDiffOn (𝓘(ℝ, G.Horizontal base)) (spacetimeModel n) ∞
      (fun A => β (A, s)) N :=
    hβ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun _ hA => ⟨hA, hsD⟩)
  have hslice' := ((hslice W hWN).contMDiffAt (hN.mem_nhds hWN)).mdifferentiableAt
    (by simp)
  have hgerm : (fun A => E.gamma A s) =ᶠ[𝓝 W]
      (fun A => (G.gaugeCover.cylinder b).toSpacetime (β (A, s))) := by
    filter_upwards [hN.mem_nhds hWN] with A hA
    exact (hrec (A, s) ⟨hA, hsD⟩).symm
  let jₛ := (G.gaugeCover.metric b).spatialTangentEquiv (β (W, s)).1 (β (W, s)).2
  have hident (v : G.Horizontal base) : HEq (E.differential W s hWs v)
      (jₛ (fderiv ℝ (fun A => f (s, A)) W v)) :=
    exponentialGauge_differential_heq E hWs b (fun A => β (A, s)) v hslice' hgerm
  have hinj : Function.Injective (E.differential W s hWs) := by
    intro v w hvw
    apply hgood W hW s hs
    apply jₛ.injective
    exact eq_of_heq ((hident v).symm.trans ((heq_of_eq hvw).trans (hident w)))
  let : FiniteDimensional ℝ (G.Horizontal (E.gamma W s)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal (E.gamma W s)
  have hdim : Module.finrank ℝ (G.Horizontal base) =
      Module.finrank ℝ (G.Horizontal (E.gamma W s)) :=
    (VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal base).trans
      (VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal (E.gamma W s)).symm
  exact (LinearEquiv.ofInjectiveOfFinrankEq
    (E.differential W s hWs).toLinearMap hinj hdim).bijective

end PoincareConjecture.M14
