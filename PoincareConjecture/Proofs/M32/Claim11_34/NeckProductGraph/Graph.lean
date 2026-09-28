import PoincareConjecture.Proofs.M32.Claim11_34.NeckProductGraph.Projection
import PoincareConjecture.Proofs.M32.Mathlib.OrderedProductGraph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.M32

private theorem neck_graph_lift_smooth
    {M : Type u} {L : Type v} {C : Type w}
    [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) L]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C]
    {gM : RiemannianMetric 3 M} (N : EpsilonNeck gM)
    (E : OpenPartialHomeomorph L M)
    (hEi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target)
    (Phi : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L)
    {a : ℝ} (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (htarget : ∀ q : UnitTwoSphere, N.coordinate_map (q, a) ∈ E.target) :
    ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : UnitTwoSphere => Phi.symm (E.symm (N.coordinate_map (q, a)))) := by
  intro q
  exact (Phi.symm.contMDiff _).comp q
    ((hEi.contMDiffAt (E.open_target.mem_nhds (htarget q))).comp q
      ((N.sphereSlice_contMDiff ha) q))

theorem exists_neckSlice_product_projection_localDiffeomorph :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} {L : Type v} {C : Type w}
        [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) L] [IsManifold (𝓡 3) ∞ L]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M],
      ∀ (gM : RiemannianMetric 3 M) (gC : RiemannianMetric 2 C)
        (gL : RiemannianMetric 3 L) (DL : LeviCivitaData gL) (DM : LeviCivitaData gM)
        (Phi : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L),
        (∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          gL.inner (Phi z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z w) =
            gC.inner z.1 v.1 w.1 + v.2 * w.2) →
      ∀ (E : OpenPartialHomeomorph L M),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target →
      ∀ (N : EpsilonNeck gM) {a : ℝ}, a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ {K : Set L}, IsCompact K → K ⊆ E.source →
      ∀ {Q Lambda delta : ℝ}, 0 < Q → 0 < Lambda → 0 ≤ delta →
        Q * N.scale ^ 2 ≤ Lambda → delta * Lambda ≤ 1 / 100 →
        N.epsilon ≤ epsilon₀ →
        (∀ q : UnitTwoSphere, N.coordinate_map (q, a) ∈ E.target) →
        (∀ q : UnitTwoSphere, E.symm (N.coordinate_map (q, a)) ∈ K) →
        (∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
          gL.inner x v v ≤ 2 * Q * gM.inner (E x)
            (mfderiv (𝓡 3) (𝓡 3) E x v) (mfderiv (𝓡 3) (𝓡 3) E x v)) →
        (∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
          |DM.ricci (E x) (mfderiv (𝓡 3) (𝓡 3) E x v)
              (mfderiv (𝓡 3) (𝓡 3) E x v) - DL.ricci x v v| ≤
            delta * gL.inner x v v) →
        IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞
          (fun q : UnitTwoSphere => (Phi.symm (E.symm (N.coordinate_map (q, a)))).1) := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ :=
    EpsilonNeck.exists_ricci_quadratic_control.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M L C topM topL topC chartM smoothM chartL smoothL chartC smoothC
    measM borelM t2M t3M gM gC gL DL DM Phi hproduct E hE hEi N a ha K _hK _hKS
    Q Lambda delta hQ hLambda hdelta hscale herror hN htarget hpreimage hmetric hricci
  have hsmooth := neck_graph_lift_smooth N E hEi Phi ha htarget
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv
    (contMDiff_fst.comp hsmooth)
  intro q
  exact neckSlice_product_projection_mfderiv_bijective gC gL DL DM Phi hproduct E hE hEi
    N ha q (htarget q) hQ hLambda hdelta hscale herror
    (hmetric _ (hpreimage q)) (hricci _ (hpreimage q)) (hcontrol N DM hN)

theorem exists_neckSlice_product_graph :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} {L : Type v} {C : Type w}
        [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) L] [IsManifold (𝓡 3) ∞ L]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [T2Space C] [ConnectedSpace C],
      ∀ (gM : RiemannianMetric 3 M) (gC : RiemannianMetric 2 C)
        (gL : RiemannianMetric 3 L) (DL : LeviCivitaData gL) (DM : LeviCivitaData gM)
        (Phi : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L),
        (∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          gL.inner (Phi z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z w) =
            gC.inner z.1 v.1 w.1 + v.2 * w.2) →
      ∀ (E : OpenPartialHomeomorph L M),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target →
      ∀ (N : EpsilonNeck gM) {a : ℝ}, a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ {K : Set L}, IsCompact K → K ⊆ E.source →
      ∀ {Q Lambda delta : ℝ}, 0 < Q → 0 < Lambda → 0 ≤ delta →
        Q * N.scale ^ 2 ≤ Lambda → delta * Lambda ≤ 1 / 100 →
        N.epsilon ≤ epsilon₀ →
        (∀ q : UnitTwoSphere, N.coordinate_map (q, a) ∈ E.target) →
        (∀ q : UnitTwoSphere, E.symm (N.coordinate_map (q, a)) ∈ K) →
        (∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
          gL.inner x v v ≤ 2 * Q * gM.inner (E x)
            (mfderiv (𝓡 3) (𝓡 3) E x v) (mfderiv (𝓡 3) (𝓡 3) E x v)) →
        (∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
          |DM.ricci (E x) (mfderiv (𝓡 3) (𝓡 3) E x v)
              (mfderiv (𝓡 3) (𝓡 3) E x v) - DL.ricci x v v| ≤
            delta * gL.inner x v v) →
        ∃ d : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ C, ∃ H : C → ℝ,
          (∀ q : UnitTwoSphere, d q = (Phi.symm (E.symm (N.coordinate_map (q, a)))).1) ∧
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H ∧
          range (fun q : UnitTwoSphere => Phi.symm (E.symm (N.coordinate_map (q, a)))) =
            {z : C × ℝ | z.2 = H z.1} := by
  obtain ⟨epsilon₀, hpos, hsmall, hlocal⟩ :=
    exists_neckSlice_product_projection_localDiffeomorph.{u, v, w}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M L C topM topL topC chartM smoothM chartL smoothL chartC smoothC
    measM borelM t2M t3M t2C connC gM gC gL DL DM Phi hproduct E hE hEi N a ha K hK hKS
    Q Lambda delta hQ hLambda hdelta hscale herror hN htarget hpreimage hmetric hricci
  let f : UnitTwoSphere → C × ℝ :=
    fun q => Phi.symm (E.symm (N.coordinate_map (q, a)))
  have hsmooth : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f :=
    neck_graph_lift_smooth N E hEi Phi ha htarget
  have hp : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun q => (f q).1) :=
    hlocal gM gC gL DL DM Phi hproduct E hE hEi N ha hK hKS hQ hLambda hdelta
      hscale herror hN htarget hpreimage hmetric hricci
  have hinj : Function.Injective f := by
    intro q q' heq
    have hi := Phi.symm.injective heq
    have hs := congrArg E hi
    rw [E.right_inv (htarget q), E.right_inv (htarget q')] at hs
    have hc := congrArg N.coordinate_inverse hs
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, ha⟩,
      N.coordinate_inverse_coordinate_map ⟨mem_univ _, ha⟩] at hc
    exact congrArg Prod.fst hc
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  have hbij : Function.Bijective (fun q => (f q).1) :=
    bijective_of_isLocalHomeomorph_ordered_fibers (fun q => (f q).1)
      hp.isLocalHomeomorph (fun q => (f q).2)
      (contMDiff_snd.comp hsmooth).continuous hinj
  let d : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ C := hp.diffeomorphOfBijective hbij
  have hd (q : UnitTwoSphere) : d q = (f q).1 := rfl
  let H : C → ℝ := fun c => (f (d.symm c)).2
  refine ⟨d, H, hd, (contMDiff_snd.comp hsmooth).comp d.symm.contMDiff, ?_⟩
  change range f = {z : C × ℝ | z.2 = H z.1}
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    change (f q).2 = (f (d.symm ((f q).1))).2
    rw [← hd q, d.symm_apply_apply]
  · intro hz
    change z.2 = (f (d.symm z.1)).2 at hz
    refine ⟨d.symm z.1, ?_⟩
    apply Prod.ext
    · exact (hd (d.symm z.1)).symm.trans (d.apply_symm_apply z.1)
    · exact hz.symm

end PoincareConjecture.M32
