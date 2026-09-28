import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.ParametrizedJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CovariantJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

theorem cylinderChart_symm_smooth (q : UnitTwoSphere) :
    ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : RoundCylinderCoordinates =>
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) := by
  have h : ContMDiff (𝓡 2) (𝓡 2) ∞
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm := by
    apply contMDiffOn_univ.mp
    rw [← roundCylinder_sphereChart_target q]
    exact contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q)
  exact (h.comp contDiff_fst.contMDiff).prodMk contDiff_snd.contMDiff

theorem roundCylinderTensorCoefficient_pullback_eq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (q : UnitTwoSphere) (f : RoundCylinderSpace → M)
    (p : RoundCylinderCoordinates)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) (i j : Fin 3) :
    roundCylinderTensorCoefficient (roundCylinderPullback g f)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
      g.inner (f ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
          (fun y => f ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))
          p (roundCylinderCoordinateBasis i))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
          (fun y => f ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))
          p (roundCylinderCoordinateBasis j)) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  have hc : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm p.1 := by
    apply ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q)).contMDiffAt ?_).mdifferentiableAt (by simp)
    exact c.open_target.mem_nhds (by rw [roundCylinder_sphereChart_target]; trivial)
  have heq (v : RoundCylinderCoordinates) :
      mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (fun y => f (c.symm y.1, y.2)) p v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (c.symm p.1, p.2)
          (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 v.1, v.2) := by
    let L₁ := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
    let L₂ := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
    have h₁ := hc.comp p L₁.mdifferentiableAt
    have h₂ := L₂.mdifferentiableAt (x := p)
    have hh := mfderiv_comp p hf (h₁.prodMk h₂)
    have hL₁ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2) Prod.fst p = L₁ :=
      L₁.mfderiv_eq
    have hL₂ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) L₂ p = L₂ :=
      L₂.mfderiv_eq
    rw [mfderiv_prodMk h₁ h₂, mfderiv_comp p hc L₁.mdifferentiableAt, hL₁, hL₂] at hh
    exact congrArg (fun L => L v) hh
  unfold roundCylinderTensorCoefficient roundCylinderPullback
  rw [heq, heq]

private theorem contDiffAt_cylinder_pullback_inner
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : RoundCylinderCoordinates → M}
    {p : RoundCylinderCoordinates}
    (hf : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ f p)
    (v w : RoundCylinderCoordinates) :
    ContDiffAt ℝ ∞ (fun y => g.inner (f y)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f y v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f y w)) p := by
  have hg := (g.contMDiff (f p)).comp p hf
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf v)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf w)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp at hh
  convert! contMDiffAt_iff_contDiffAt.mp hh using 1



theorem roundCylinderTensorSmoothOn_smul_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) (s : ℝ) :
    RoundCylinderTensorSmoothOn ε (fun z v w => s * roundCylinderPullback g f z v w) := by
  intro q i j p hp
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let A : RoundCylinderCoordinates → ℝ := fun y =>
    g.inner (f (c.symm y.1, y.2))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (fun x => f (c.symm x.1, x.2)) y (roundCylinderCoordinateBasis i))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (fun x => f (c.symm x.1, x.2)) y (roundCylinderCoordinateBasis j))
  have hfp : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f (c.symm p.1, p.2) :=
    hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp.2⟩)
  have hA : ContDiffAt ℝ ∞ A p := contDiffAt_cylinder_pullback_inner g
    (hfp.comp p (cylinderChart_symm_smooth q p)) _ _
  have heq : (fun y => roundCylinderTensorCoefficient (roundCylinderPullback g f) c y i j)
      =ᶠ[𝓝 p] A := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show p ∈ (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ : Set RoundCylinderCoordinates) from
        ⟨mem_univ _, hp.2⟩)] with y hy
    exact roundCylinderTensorCoefficient_pullback_eq g q f y
      ((hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨mem_univ _, hy.2⟩)).mdifferentiableAt (by simp)) i j
  exact (contDiffAt_const.mul (hA.congr_of_eventuallyEq heq)).contDiffWithinAt

namespace PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space



theorem smooth_convergence_cylinder_coefficients
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Ioo a b) (q : UnitTwoSphere) (i j : Fin 3) :
    let B : ℕ → RoundCylinderTwoTensor := fun k =>
      roundCylinderPullback ((S.flow (G.subsequence k)).metricAt t)
        (fun z => ((G.embedding k).toFun (0, Φ z)).2)
    let B₀ := roundCylinderPullback (G.limitFlow.metricAt t) Φ
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    (∀ p : RoundCylinderCoordinates, ∃ W, IsOpen W ∧ p ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        (fun y => roundCylinderTensorCoefficient (B k) c y i j) W) ∧
    ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient (B k) c p i j))
      (iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient B₀ c p i j)) atTop K := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let f : RoundCylinderCoordinates → G.limitCarrier.carrier := fun p => Φ (c.symm p.1, p.2)
  have hf : ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ f :=
    hΦ.comp (cylinderChart_symm_smooth q)
  let e : RoundCylinderCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨hloc, hjet⟩ := G.smooth_convergence_parametrized_inner hzero e isOpen_univ
    hf.contMDiffOn ht (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)
  let A : ℕ → RoundCylinderCoordinates → ℝ := fun k x =>
    ((S.flow (G.subsequence k)).metricAt t).inner (((G.embedding k).toFun (0, f x)).2)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (fun y => ((G.embedding k).toFun (0, f y)).2) x (roundCylinderCoordinateBasis i))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (fun y => ((G.embedding k).toFun (0, f y)).2) x (roundCylinderCoordinateBasis j))
  let C : ℕ → RoundCylinderCoordinates → ℝ := fun k p =>
    roundCylinderTensorCoefficient
      (roundCylinderPullback ((S.flow (G.subsequence k)).metricAt t)
        (fun z => ((G.embedding k).toFun (0, Φ z)).2)) c p i j
  have hnear (K : Set RoundCylinderCoordinates) (hK : IsCompact K) :
      ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ k in atTop, EqOn (C k) (A k) W := by
    obtain ⟨D, hD, hKD, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
    obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (hD.image hf.continuous)
    refine ⟨interior D, isOpen_interior, hKD, ?_⟩
    filter_upwards [eventually_ge_atTop s] with k hk p hp
    apply roundCylinderTensorCoefficient_pullback_eq
    have hmem : Φ (c.symm p.1, p.2) ∈ G.exhaustion k :=
      G.exhaustion_monotone hk (hs (mem_image_of_mem f (interior_subset hp)))
    exact (((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hmem).comp
      (c.symm p.1, p.2) (hΦ _)).mdifferentiableAt (by simp)
  have heq₀ : (fun p => roundCylinderTensorCoefficient
      (roundCylinderPullback (G.limitFlow.metricAt t) Φ) c p i j) =
      (fun x => (G.limitFlow.metricAt t).inner (f x)
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f x (roundCylinderCoordinateBasis i))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f x (roundCylinderCoordinateBasis j))) := by
    funext p
    exact roundCylinderTensorCoefficient_pullback_eq _ q Φ p
      ((hΦ _).mdifferentiableAt (by simp)) i j
  change (∀ p, ∃ W, IsOpen W ∧ p ∈ W ∧
    ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (C k) W) ∧ _
  constructor
  · intro p
    obtain ⟨V, hV, hpV, hvs⟩ := hloc p (mem_univ _)
    obtain ⟨W, hW, hpW, heq⟩ := hnear {p} isCompact_singleton
    refine ⟨V ∩ W, hV.inter hW, ⟨hpV, hpW (mem_singleton _)⟩, ?_⟩
    filter_upwards [hvs, heq] with k hks hk
    exact (hks.mono inter_subset_left).congr (fun x hx => hk hx.2)
  · intro m K hK
    rw [heq₀]
    obtain ⟨W, hW, hKW, heq⟩ := hnear K hK
    apply (hjet m K hK (subset_univ K)).congr
    filter_upwards [heq] with k hk x hx
    exact ((Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen hW hk m) (hKW hx)).symm




theorem tendstoUniformlyOn_cylinder_covariant_derivative
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Ioo a b) {u : ℝ} (hu : u < 1)
    (hround : roundCylinderPullback (G.limitFlow.metricAt t) Φ = EvolvingRoundCylinderMetric u)
    (q : UnitTwoSphere) (k : ℕ) (a : Fin (2 + k) → Fin 3)
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun l p => roundCylinderIteratedDerivative u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (roundCylinderPullback ((S.flow (G.subsequence l)).metricAt t)
          (fun z => ((G.embedding l).toFun (0, Φ z)).2)) k p a)
      (fun _ => 0) atTop K := by
  have hc := G.smooth_convergence_cylinder_coefficients hzero hΦ ht q
  dsimp only at hc
  rw [hround] at hc
  exact tendstoUniformlyOn_roundCylinderIteratedDerivative u
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) isOpen_univ
    (fun a b d => (contDiff_roundCylinderChristoffel hu q a b d).contDiffOn)
    (fun a b => (contDiff_roundCylinderGram u q a b).contDiffOn)
    (fun a b p _ => (hc a b).1 p)
    (fun a b m K hK _ => (hc a b).2 m K hK) k a hK (subset_univ K)

end PointedGeometricConvergence
end PoincareConjecture
