import PoincareConjecture.Proofs.M14.Mathlib.ClosedProductInverse
import PoincareConjecture.Proofs.M14.Sec6_3_JointNeighborhood
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeSliceInvertible
import PoincareConjecture.Proofs.M14.Sec6_3_BackwardClock

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

theorem exists_jointMap_local_inverse (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hz : (Z, s) ∈ M14JointDomain G E) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    ∃ O : Set G.Point, IsOpen O ∧ E.gamma Z s ∈ O ∧
      ∃ inv : G.Point → G.Horizontal x × ℝ,
        ContMDiffOn (spacetimeModel n) (𝓘(ℝ, G.Horizontal x × ℝ)) ∞ inv O ∧
        (∀ q ∈ O, inv q ∈ M14JointDomain G E) ∧
        ∀ q ∈ O, E.gamma (inv q).1 (inv q).2 = q := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  have hsurv := jointDomain_subset_domain E hz
  have hpos := jointDomain_time_pos E hz
  have hbij : Function.Bijective (E.differential Z s hsurv) := by
    obtain ⟨τ, H, _, hZH, hs⟩ := hz.1
    have hstable := (H.carrier_exact Z).mp hZH
    obtain ⟨hτ, hbij, _⟩ := hstable
    change s = Real.sqrt τ at hs
    subst s
    exact hbij
  obtain ⟨b, N, lift, hN, hpN, hlift, hrec, htime, U, hU, hUc, hZU,
    a, c, ha, has, hsc, htube, hgammaN, hnear⟩ := exists_jointDomain_gauge_tube E hz
  let C := Icc a c
  let β := fun z : G.Horizontal x × ℝ => lift (E.gamma z.1 z.2)
  have hsC : s ∈ C := ⟨has.le, hsc⟩
  have hβ : ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
      (spacetimeModel n) ∞ β (U ×ˢ C) :=
    hlift.comp (E.family_smooth.mono (htube.trans (jointDomain_subset_domain E))) hgammaN
  have hβrec (z : G.Horizontal x × ℝ) (hz : z ∈ U ×ˢ C) :
      (G.gaugeCover.cylinder b).toSpacetime (β z) = E.gamma z.1 z.2 :=
    hrec _ (hgammaN z hz)
  have hqb := exponential_gauge_slice_bijective E b hU β hβrec hZU hsC hsurv hbij hβ
  have hv : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) :=
    contMDiff_subtype_val
  have hq : ContDiffOn ℝ ∞ (fun z => (β z).2.val) (U ×ˢ C) := by
    have h := hv.comp_contMDiffOn (fun z hz => (hβ z hz).snd)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  obtain ⟨P, hP, hzP, g, hgf, hgt, hgs⟩ := exists_closedProduct_inverse
    hU hUc (convex_Icc a c) (uniqueDiffOn_Icc (has.trans_le hsc)) hq hZU hsC hqb
  have hCnear : C ∈ 𝓝[{r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain}] s := by
    have hp : Continuous (fun r : ℝ => (Z, r)) := continuous_const.prodMk continuous_id
    have hpa := (hp.continuousWithinAt (x := s)).tendsto_nhdsWithin
      (show MapsTo (fun r : ℝ => (Z, r)) {r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain}
        (M14AdmissibleParameter G T x) from fun _ hr => hr)
    exact mem_of_superset (hpa hnear) (fun _ hr => hr.2)
  obtain ⟨Q, hQ, hpQ, hQclock⟩ := exists_backwardSquareClock_neighborhood G T E hsurv hpos hCnear
  let χ : G.Point → EuclideanSpace ℝ (Fin n) × ℝ :=
    fun q => ((lift q).2.val, backwardSquareClock G T q)
  have hχ : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) ∞ χ
      (N ∩ Q) := by
    have h : ContMDiffOn (spacetimeModel n) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞ χ (N ∩ Q) :=
      ((hv.comp_contMDiffOn (fun q hq => (hlift q hq).snd)).mono inter_subset_left).prodMk
        ((backwardSquareClock_contMDiffOn G T).mono (fun q hq => (hQclock q hq.2).1))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h
  let V := P ∩ (U ×ˢ (univ : Set ℝ))
  have hV : IsOpen V := hP.inter (hU.prod isOpen_univ)
  let O := (N ∩ Q) ∩ χ ⁻¹' (g '' V)
  have hO : IsOpen O := hχ.continuousOn.isOpen_inter_preimage (hN.inter hQ) (g.isOpenMap V hV)
  have hχcenter : χ (E.gamma Z s) = g (Z, s) := by
    rw [← hgf ⟨hzP, hZU, hsC⟩]
    exact Prod.ext rfl (backwardSquareClock_exponential G T E hsurv)
  have hpO : E.gamma Z s ∈ O := by
    refine ⟨⟨hpN, hpQ⟩, ?_⟩
    change χ (E.gamma Z s) ∈ g '' V
    rw [hχcenter]
    exact ⟨(Z, s), ⟨hzP, hZU, mem_univ _⟩, rfl⟩
  let inv := fun q => g.symm (χ q)
  have hinv (q : G.Point) (hq : q ∈ O) : inv q ∈ P ∩ (U ×ˢ C) := by
    obtain ⟨z, hzV, hzχ⟩ := hq.2
    have hze : inv q = z := by dsimp only [inv]; rw [← hzχ, g.symm_apply_apply]
    have ht : z.2 = backwardSquareClock G T q := by
      have he := congrArg Prod.snd hzχ
      simpa only [hgt z, χ] using he
    rw [hze]
    exact ⟨hzV.1, hzV.2.1, ht ▸ (hQclock q hq.1.2).2⟩
  have himage (q : G.Point) (hq : q ∈ O) : χ q ∈ g '' (P ∩ (U ×ˢ C)) :=
    ⟨inv q, hinv q hq, g.apply_symm_apply _⟩
  refine ⟨O, hO, hpO, inv,
    hgs.contMDiffOn.comp (hχ.mono inter_subset_left) himage,
    fun q hq => htube (hinv q hq).2, ?_⟩
  intro q hq
  have heq : ((β (inv q)).2.val, (inv q).2) = χ q :=
    (hgf (hinv q hq)).trans (g.apply_symm_apply _)
  have hs : (inv q).2 = backwardSquareClock G T q := congrArg Prod.snd heq
  have hβq : β (inv q) = lift q := by
    apply Prod.ext
    · apply Subtype.ext
      have hβclock := htime _ (hgammaN _ (hinv q hq).2)
      have he : G.spacetime.timeFunction (E.gamma (inv q).1 (inv q).2) =
          G.spacetime.timeFunction q :=
        (E.clock (inv q).1 (inv q).2 (jointDomain_subset_domain E (htube (hinv q hq).2))).trans
          ((congrArg (fun r : ℝ => T - r ^ 2) hs).trans
            (backwardSquareClock_admissible G T (hQclock q hq.1.2).1.le).2.1)
      exact hβclock.trans (he.trans (htime q hq.1.1).symm)
    · exact Subtype.ext (congrArg Prod.fst heq)
  exact (hβrec _ (hinv q hq).2).symm.trans
    ((congrArg (G.gaugeCover.cylinder b).toSpacetime hβq).trans (hrec q hq.1.1))

end PoincareConjecture.M14
