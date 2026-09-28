import PoincareConjecture.Definitions.M13OrdinaryRescaling
import PoincareConjecture.Proofs.M13.MetricCalculus
import PoincareConjecture.Proofs.M13.ConnectionScale
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Geometry.Manifold.Algebra.Monoid










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
theorem parabolicTimeInv_contMDiff [T2Space M] (Q : ℝ) (_hQ : 0 < Q) (a : ℝ) :
    ContMDiff ((𝓘(ℝ)).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × M ↦ (parabolicTimeInv Q a p.1, p.2)) := by
  have ht : ContMDiff ((𝓘(ℝ)).prod (𝓡 n)) 𝓘(ℝ) ∞
      (fun p : ℝ × M ↦ parabolicTimeInv Q a p.1) := by
    change ContMDiff ((𝓘(ℝ)).prod (𝓡 n)) 𝓘(ℝ) ∞
      (fun p : ℝ × M ↦ a + p.1 / Q)
    have hclock : ContDiff ℝ ∞ (fun t : ℝ ↦ a + t / Q) :=
      contDiff_const.add (contDiff_id.div_const Q)
    exact hclock.contMDiff.comp contMDiff_fst
  exact ht.prodMk contMDiff_snd

theorem identity_metricHomothety (g : RiemannianMetric n M) (Q : ℝ) (hQ : 0 < Q) :
    MetricHomothety g (scaleSmoothMetric g Q hQ)
      (Diffeomorph.refl (𝓡 n) M ∞) Q := by
  intro x u v
  rw [Diffeomorph.coe_refl]
  change ((scaleSmoothMetric g Q hQ).inner x)
      (mfderiv (𝓡 n) (𝓡 n) (fun y : M => y) x u)
      (mfderiv (𝓡 n) (𝓡 n) (fun y : M => y) x v) = Q * (g.inner x u) v
  have hfun : (fun y : M => y) = (@id M) := rfl
  rw [hfun, mfderiv_id]
  simp only [ContinuousLinearMap.id_apply, scaleSmoothMetric_inner]

theorem ordinary_scaled_smooth
    [T2Space M] [SecondCountableTopology M]
    (I : SpacetimeInterval) (F : RicciFlow n M I.domain)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    RiemannianMetric.IsSmoothFamilyOn
      (fun s ↦ scaleSmoothMetric (F.metric (parabolicTimeInv Q a s)) Q hQ)
      (parabolicInterval Q hQ a I).domain := by
  unfold RiemannianMetric.IsSmoothFamilyOn
  let r : ℝ × M → ℝ × M := fun p ↦ (parabolicTimeInv Q a p.1, p.2)
  let sold : ℝ × M → Bundle.TotalSpace
      (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
    fun p ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      p.2 ((F.metric p.1).inner p.2)
  let snew : ℝ × M → Bundle.TotalSpace
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
    fun p ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      p.2 ((scaleSmoothMetric (F.metric (parabolicTimeInv Q a p.1)) Q hQ).inner p.2)
  have hr : ContMDiff ((𝓘(ℝ)).prod (𝓡 n)) ((𝓘(ℝ)).prod (𝓡 n)) ∞ r := by
    exact parabolicTimeInv_contMDiff Q hQ a
  have hmap : (parabolicInterval Q hQ a I).domain ×ˢ Set.univ ⊆
      r ⁻¹' (I.domain ×ˢ Set.univ) := by
    intro p hp
    exact ⟨(mem_parabolicInterval_iff Q hQ a I p.1).1 hp.1, trivial⟩
  have hcomp : ContMDiffOn ((𝓘(ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (sold ∘ r) ((parabolicInterval Q hQ a I).domain ×ˢ Set.univ) := by
    exact F.smooth.comp hr.contMDiffOn hmap
  intro p hp
  have hold := Bundle.contMDiffWithinAt_totalSpace.mp (hcomp p hp)
  let e := trivializationAt
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) p.2
  have hbase : (fun q : ℝ × M ↦ q.2) ⁻¹' e.baseSet ∈
      𝓝[(parabolicInterval Q hQ a I).domain ×ˢ Set.univ] p := by
    apply mem_nhdsWithin_of_mem_nhds
    exact (continuousAt_snd.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt _ _ _)))
  let : ∀ x : M, IsTopologicalAddGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    infer_instance
  let : ∀ x : M, IsTopologicalAddGroup
      (TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    infer_instance
  let : ∀ x : M, ContinuousAdd (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    exact (inferInstance :
      IsTopologicalAddGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ)).toContinuousAdd
  let : ∀ x : M, ContinuousSMul ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    infer_instance
  let : e.IsLinear ℝ := by
    dsimp [e]
    rw [hom_trivializationAt]
    refine ⟨?_⟩
    intro b hb
    exact (Bundle.Pretrivialization.continuousLinearMap.isLinear
      (RingHom.id ℝ)
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.2)
      (trivializationAt (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) p.2)).linear b hb
  have hcoord := (contMDiffWithinAt_const (I := (𝓘(ℝ)).prod (𝓡 n))
      (I' := 𝓘(ℝ))
      (n := ∞) (x := p) (c := Q)).smul hold.2
  change ContMDiffWithinAt ((𝓘(ℝ)).prod (𝓡 n))
    ((𝓡 n).prod 𝓘(ℝ,
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
    snew ((parabolicInterval Q hQ a I).domain ×ˢ Set.univ) p
  refine Bundle.contMDiffWithinAt_totalSpace.mpr ⟨?_, ?_⟩
  · exact contMDiffWithinAt_snd
  · refine hcoord.congr_of_eventuallyEq ?_ ?_
    · apply Filter.eventually_of_mem
      · exact hbase
      · intro q hq
        change q.2 ∈ e.baseSet at hq
        change (e (snew q)).2 = Q • (e (sold (r q))).2
        apply (e.linear ℝ hq).2
    · change (e (snew p)).2 = Q • (e (sold (r p))).2
      apply (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' p.2)).2

theorem ordinaryParabolicRescaling
    [T2Space M] [SecondCountableTopology M]
    (I : SpacetimeInterval) (F : RicciFlow n M I.domain)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    Nonempty (OrdinaryParabolicRescaling F Q hQ a) := by
  let g : ℝ → RiemannianMetric n M :=
    fun s ↦ scaleSmoothMetric (F.metric (parabolicTimeInv Q a s)) Q hQ
  let D : ∀ s, LeviCivitaData (g s) :=
    fun s ↦ scaleLeviCivitaData (F.connection (parabolicTimeInv Q a s)) Q hQ
  let J := (parabolicInterval Q hQ a I).domain
  let hflow : RicciFlow n M J := by
    refine {
      metric := g
      connection := D
      interval := (parabolicInterval Q hQ a I).ordConnected
      nontrivial := (parabolicInterval Q hQ a I).nontrivial
      smooth := ?_
      equation := ?_ }
    · exact ordinary_scaled_smooth I F Q hQ a
    · intro t ht x u v
      let t₀ := parabolicTimeInv Q a t
      have ht₀ : t₀ ∈ I.domain := (mem_parabolicInterval_iff Q hQ a I t).1 ht
      have hclock : HasDerivWithinAt (fun s : ℝ ↦ parabolicTimeInv Q a s)
          (1 / Q) J t := by
        simpa [parabolicTimeInv, Function.id_def] using
          (((hasDerivAt_id t).div_const Q).const_add a).hasDerivWithinAt
      have hclock_map : Set.MapsTo (fun s : ℝ ↦ parabolicTimeInv Q a s) J I.domain := by
        intro s hs
        exact (mem_parabolicInterval_iff Q hQ a I s).1 hs
      have heq := (F.equation t₀ ht₀ x u v).comp t hclock hclock_map
      have heqQ := heq.const_mul Q
      change HasDerivWithinAt
        (fun s : ℝ ↦ Q * (F.metric (parabolicTimeInv Q a s)).inner x u v)
        _ J t at heqQ
      have hricci := homothety_ricci_eq
        (F.metric t₀) (scaleSmoothMetric (F.metric t₀) Q hQ)
        (Diffeomorph.refl (𝓡 n) M ∞) Q hQ
        (identity_metricHomothety (F.metric t₀) Q hQ)
        (F.connection t₀) (scaleLeviCivitaData (F.connection t₀) Q hQ) x u v
      have hricci' :
          (scaleLeviCivitaData (F.connection t₀) Q hQ).ricci x u v =
            (F.connection t₀).ricci x u v := by
        rw [Diffeomorph.coe_refl] at hricci
        change (scaleLeviCivitaData (F.connection t₀) Q hQ).ricci x
            (mfderiv (𝓡 n) (𝓡 n) (fun y : M => y) x u)
            (mfderiv (𝓡 n) (𝓡 n) (fun y : M => y) x v) =
          (F.connection t₀).ricci x u v at hricci
        have hfun : (fun y : M => y) = (@id M) := rfl
        rw [hfun, mfderiv_id] at hricci
        simpa only [ContinuousLinearMap.id_apply] using hricci
      have hderiv : -2 * (D t).ricci x u v =
          Q * (-2 * (F.connection t₀).ricci x u v * (1 / Q)) := by
        dsimp [D, t₀]
        rw [← hricci']
        field_simp [hQ.ne']
        ring
      rw [hderiv]
      simpa [g, scaleSmoothMetric_inner] using heqQ
  refine ⟨{ flow := hflow, metric_eq := ?_, metric_homothety := ?_, metric_calculus := ?_ }⟩
  · intro s x u v
    dsimp [hflow]
    simp [g, scaleSmoothMetric_inner]
  · intro s
    dsimp [hflow]
    exact identity_metricHomothety (F.metric (parabolicTimeInv Q a s)) Q hQ
  · intro _ _ _ s
    dsimp [hflow]
    exact metricHomothetyCalculus
      (F.metric (parabolicTimeInv Q a s)) (g s)
      (Diffeomorph.refl (𝓡 n) M ∞) Q hQ
      (identity_metricHomothety (F.metric (parabolicTimeInv Q a s)) Q hQ)

end PoincareConjecture.M13
