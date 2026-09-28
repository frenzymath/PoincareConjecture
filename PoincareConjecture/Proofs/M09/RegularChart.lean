import PoincareConjecture.Proofs.M09.RegularDomainOpen
import Mathlib.Topology.IsLocalHomeomorph








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem lExponentialFamily_exists_regular_chart {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ∃ G : OpenPartialHomeomorph (TangentSpace (𝓡 n) p × ℝ) (M × ℝ),
      G.source = A.regularDomain ∧
      (∀ z, G z = (A.gamma z.1 z.2, z.2)) ∧
      ContMDiffOn ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ)))
        ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞ G G.source ∧
      ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) ∞ G.symm G.target ∧
      G.target ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      ∀ z ∈ G.target, (G.symm z).2 = z.2 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  let Φ : E × ℝ → M × ℝ := fun z ↦ (A.gamma z.1 z.2, z.2)
  let R := A.regularDomain
  have hR : IsOpen R := lExponentialFamily_regularDomain_isOpen F hM04 T τmax
    hτmax hwindow hcurvature hL p A
  have hRt : R ⊆ Set.univ ×ˢ Set.Ioo 0 τmax := by
    rintro z ⟨⟨ht, hm, _⟩, _⟩
    exact ⟨Set.mem_univ _, ht, hm⟩
  have hinj : Set.InjOn Φ R := by
    rintro ⟨Z, τ⟩ hz ⟨W, σ⟩ hw heq
    have ht : τ = σ := congrArg Prod.snd heq
    subst σ
    obtain ⟨hτ, hm, hmin, huniq⟩ := hz.1
    obtain ⟨_, _, hWmin, _⟩ := hw.1
    have hend : A.gamma W τ = A.gamma Z τ := (congrArg Prod.fst heq).symm
    have hcurve := huniq (A.path W τ hτ hm)
      ((congrFun (A.path_eq W τ hτ hm) 0).trans (A.gamma_at_zero W))
      ((congrFun (A.path_eq W τ hτ hm) τ).trans hend) hWmin
    rw [A.path_eq] at hcurve
    exact Prod.ext (lExponentialFamily_initialVector_eq_of_eqOn A W Z τ hτ hm hcurve).symm rfl
  have hlocal : IsLocalHomeomorphOn Φ R := IsLocalHomeomorphOn.mk Φ R (by
    intro z hz
    obtain ⟨e, hze, _, he, _⟩ := lExponentialFamily_exists_local_inverse A z
      (hRt hz).2.1 (hRt hz).2.2 hz.2
    exact ⟨e, hze, he.symm⟩)
  have hopen : IsOpenMap (R.restrict Φ) := by
    apply IsOpenMap.of_nhds_le
    intro z
    have hsub := hR.isOpenEmbedding_subtypeVal.map_nhds_eq z
    have hmap : Filter.map (R.restrict Φ) (𝓝 z) = 𝓝 (Φ z) := by
      rw [show R.restrict Φ = Φ ∘ Subtype.val from rfl, ← Filter.map_map, hsub]
      exact hlocal.map_nhds_eq z.property
    exact hmap.ge
  let G := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv Φ R) hlocal.continuousOn hopen hR
  have hforward (z : E × ℝ) : G z = Φ z := rfl
  have hsource : G.source = R := rfl
  have hsmooth : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ)))
      ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞ G G.source :=
    (A.gamma_smooth.prodMk contMDiffOn_snd).mono hRt
  have htime (z : M × ℝ) (hz : z ∈ G.target) : (G.symm z).2 = z.2 :=
    congrArg Prod.snd (G.right_inv hz)
  have htarget : G.target ⊆ Set.univ ×ˢ Set.Ioo 0 τmax := by
    intro z hz
    have ht := (hRt (G.map_target hz)).2
    rw [htime z hz] at ht
    exact ⟨Set.mem_univ _, ht⟩
  refine ⟨G, hsource, hforward, hsmooth, ?_, htarget, htime⟩
  intro y hy
  have hx : G.symm y ∈ R := G.map_target hy
  obtain ⟨e, hxe, _, he, hinv, _⟩ := lExponentialFamily_exists_local_inverse A (G.symm y)
    (hRt hx).2.1 (hRt hx).2.2 hx.2
  have hey : e (G.symm y) = y := (he hxe).trans (G.right_inv hy)
  have hye : y ∈ e.target := hey ▸ e.map_source hxe
  have hnear : ∀ᶠ w in 𝓝 y, G.symm w ∈ e.source :=
    (G.symm.continuousAt hy).preimage_mem_nhds (e.open_source.mem_nhds hxe)
  have hagree : (G.symm : M × ℝ → E × ℝ) =ᶠ[𝓝 y] e.symm := by
    filter_upwards [G.open_target.mem_nhds hy, e.open_target.mem_nhds hye, hnear] with w hw hew hsw
    have hforwardw : e (G.symm w) = w := (he hsw).trans (G.right_inv hw)
    exact (e.left_inv hsw).symm.trans (congrArg e.symm hforwardw)
  exact ((hinv.contMDiffAt (e.open_target.mem_nhds hye)).congr_of_eventuallyEq hagree).contMDiffWithinAt

end PoincareConjecture.Proofs.M09
