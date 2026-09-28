import PoincareConjecture.Proofs.M51.EmptyEventCopy
import PoincareConjecture.Proofs.M51.EventTransportMetric
import PoincareConjecture.Proofs.M51.EventTransportCap
import PoincareConjecture.Proofs.M51.EventTransportDerivative
import PoincareConjecture.Proofs.M33.OldEventPolicy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Diffeomorph
import PoincareConjecture.Proofs.M48.StaticNeck
import PoincareConjecture.Proofs.M48.StaticCap
import PoincareConjecture.Proofs.M48.StaticComponents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace M51EventTransport

variable {A B C D : GeneralizedSliceCarrier.{u}}

noncomputable def region
    {U : Set A.carrier} {V : Set B.carrier}
    (r : SurgeryRegionEquivalence A B U V)
    (p : Diffeomorph (𝓡 3) (𝓡 3) C.carrier A.carrier ∞)
    (q : Diffeomorph (𝓡 3) (𝓡 3) B.carrier D.carrier ∞) :
    SurgeryRegionEquivalence C D (p ⁻¹' U) (q.symm ⁻¹' V) where
  map := q ∘ r.map ∘ p
  inverse := p.symm ∘ r.inverse ∘ q.symm
  map_image := by
    rw [Set.image_comp, Set.image_comp,
      Set.image_preimage_eq (f := (p : C.carrier → A.carrier)) _ p.surjective,
      r.map_image, q.image_eq_preimage_symm]
  inverse_image := by
    rw [Set.image_comp, Set.image_comp,
      Set.image_preimage_eq (f := (q.symm : D.carrier → B.carrier)) _ q.symm.surjective,
      r.inverse_image, p.symm.image_eq_preimage_symm]
    rfl
  left_inverse := by
    intro x hx
    change p.symm (r.inverse (q.symm (q (r.map (p x))))) = x
    rw [q.symm_apply_apply, r.left_inverse hx]
    exact p.symm_apply_apply x
  right_inverse := by
    intro x hx
    change q (r.map (p (p.symm (r.inverse (q.symm x))))) = x
    rw [p.apply_symm_apply, r.right_inverse hx, q.apply_symm_apply]
  map_smooth := q.contMDiff.comp_contMDiffOn (r.map_smooth.comp p.contMDiff.contMDiffOn
    (fun _ hx => hx))
  inverse_smooth := p.symm.contMDiff.comp_contMDiffOn
    (r.inverse_smooth.comp q.symm.contMDiff.contMDiffOn (fun _ hx => hx))

@[simp] theorem region_map
    {U : Set A.carrier} {V : Set B.carrier}
    (r : SurgeryRegionEquivalence A B U V)
    (p : Diffeomorph (𝓡 3) (𝓡 3) C.carrier A.carrier ∞)
    (q : Diffeomorph (𝓡 3) (𝓡 3) B.carrier D.carrier ∞)
    (x : C.carrier) :
    (region r p q).map x = q (r.map (p x)) := rfl

@[simp] theorem region_inverse
    {U : Set A.carrier} {V : Set B.carrier}
    (r : SurgeryRegionEquivalence A B U V)
    (p : Diffeomorph (𝓡 3) (𝓡 3) C.carrier A.carrier ∞)
    (q : Diffeomorph (𝓡 3) (𝓡 3) B.carrier D.carrier ∞)
    (x : D.carrier) :
    (region r p q).inverse x = p.symm (r.inverse (q.symm x)) := rfl

end M51EventTransport

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice slice' : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier}
    {metric' : ∀ t, RiemannianMetric 3 (slice' t).carrier} {T : ℝ}

noncomputable def transport
    (E : SurgeryEventData g₀ K P slice metric T)
    (φ : ∀ t : Set.Ico E.tMinus T,
      Diffeomorph (𝓡 3) (𝓡 3) (slice t.1).carrier (slice' t.1).carrier ∞)
    (ψ : Diffeomorph (𝓡 3) (𝓡 3) (slice T).carrier (slice' T).carrier ∞)
    (hφ : ∀ (t : Set.Ico E.tMinus T) (x : (slice t.1).carrier) v w,
      (metric' t.1).inner (φ t x)
        (mfderiv (𝓡 3) (𝓡 3) (φ t) x v)
        (mfderiv (𝓡 3) (𝓡 3) (φ t) x w) =
        (metric t.1).inner x v w)
    (hψ : ∀ (x : (slice T).carrier) v w,
      (metric' T).inner (ψ x)
        (mfderiv (𝓡 3) (𝓡 3) ψ x v)
        (mfderiv (𝓡 3) (𝓡 3) ψ x w) =
        (metric T).inner x v w)
    (D : M51EventTransport.MetricLimitTransportData E
      (φ ⟨E.tMinus, ⟨le_rfl, E.tMinus_lt⟩⟩)) :
    SurgeryEventData g₀ K P slice' metric' T := by
  let t₀ : Set.Ico E.tMinus T := ⟨E.tMinus, ⟨le_rfl, E.tMinus_lt⟩⟩
  let p := φ t₀
  let F := E.pre_flow.pullbackDiffeomorph p.symm
  let preSet : Set (slice' E.tMinus).carrier := p.symm ⁻¹' E.regular_limit
  let retainedSet : Set (slice' E.tMinus).carrier := p.symm ⁻¹' E.retained_pre
  let preIdentify : ∀ t : Set.Ico E.tMinus T,
      Diffeomorph (𝓡 3) (𝓡 3) (slice' E.tMinus).carrier (slice' t.1).carrier ∞ :=
    fun t => p.symm.trans ((E.pre_identify t).trans (φ t))
  let cap : ∀ i : Fin E.cap_count,
      SurgeryCapChart g₀ (slice' T) (metric' T) (P.h T) :=
    fun i => (E.caps i).transport ψ hψ
  refine {
    tMinus := E.tMinus
    tMinus_nonnegative := E.tMinus_nonnegative
    tMinus_lt := E.tMinus_lt
    preterminal_close := E.preterminal_close
    pre_flow := F
    pre_identify := preIdentify
    pre_initial := by
      intro x
      change φ t₀ (E.pre_identify t₀ (p.symm x)) = x
      rw [show φ t₀ = p from rfl, E.pre_initial, p.apply_symm_apply]
    pre_metric := by
      intro t x v w
      change (metric' t.1).inner (φ t (E.pre_identify t (p.symm x)))
        (mfderiv (𝓡 3) (𝓡 3) (φ t ∘ (E.pre_identify t ∘ p.symm)) x v)
        (mfderiv (𝓡 3) (𝓡 3) (φ t ∘ (E.pre_identify t ∘ p.symm)) x w) =
        (F.metric t.1).inner x v w
      rw [(φ t).mfderiv_comp (by simp), p.symm.mfderiv_precomp (by simp)]
      simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
      rw [hφ t (E.pre_identify t (p.symm x)) _ _, E.pre_metric t (p.symm x)]
      exact (E.pre_flow.pullbackDiffeomorph_inner p.symm t.1 x v w).symm
    regular_limit := preSet
    regular_limit_eq := by
      ext x
      change p.symm x ∈ E.regular_limit ↔ _
      rw [E.regular_limit_eq]
      simp only [F, RicciFlow.pullbackDiffeomorph_scalarCurvature]
      rfl
    regular_limit_open := by
      exact E.regular_limit_open.preimage p.symm.continuous
    terminal := E.terminal
    limit_identify := M51EventTransport.region E.limit_identify p.symm
      (Diffeomorph.refl (𝓡 3) E.terminal.carrier ∞)
    limit_metric := E.limit_metric
    limit_connection := E.limit_connection
    metric_converges := D.metric_converges
    retained_pre := retainedSet
    retained_pre_compact := by
      exact p.symm.toHomeomorph.isCompact_preimage.mpr E.retained_pre_compact
    retained_pre_subset := by
      intro x hx
      change p.symm x ∈ E.regular_limit
      exact E.retained_pre_subset hx
    low_curvature_retained := by
      intro x hx
      change x ∈ (fun y => E.limit_identify.map (p.symm y)) ''
        (p.symm ⁻¹' E.retained_pre)
      rw [M51EventTransport.limit_identify_image_preimage E p E.retained_pre]
      exact E.low_curvature_retained hx
    retained_post := ψ.symm ⁻¹' E.retained_post
    retained_post_compact := by
      exact ψ.symm.toHomeomorph.isCompact_preimage.mpr E.retained_post_compact
    retention := M51EventTransport.region E.retention p.symm ψ
    retained_metric := by
      intro x hx v w
      change (metric' T).inner (ψ (E.retention.map (p.symm x)))
        (mfderiv (𝓡 3) (𝓡 3) (ψ ∘ (E.retention.map ∘ p.symm)) x v)
        (mfderiv (𝓡 3) (𝓡 3) (ψ ∘ (E.retention.map ∘ p.symm)) x w) =
        E.limit_metric.inner (E.limit_identify.map (p.symm x))
          (mfderiv (𝓡 3) (𝓡 3) (E.limit_identify.map ∘ p.symm) x v)
          (mfderiv (𝓡 3) (𝓡 3) (E.limit_identify.map ∘ p.symm) x w)
      rw [ψ.mfderiv_comp (by simp), p.symm.mfderiv_precomp (by simp),
        p.symm.mfderiv_precomp (by simp)]
      simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
      rw [hψ, E.retained_metric (p.symm x) hx]
    cap_count := E.cap_count
    caps := cap
    cap_disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      rcases hxi with ⟨xi, hxi, rfl⟩
      rcases hxj with ⟨xj, hxj, hq⟩
      have hq' : xj = xi := ψ.injective hq
      exact Set.disjoint_left.mp (E.cap_disjoint i j hij) hxi (hq' ▸ hxj)
    post_cover := by
      have hcover := congrArg (Set.image ψ) E.post_cover
      rw [image_union, image_iUnion] at hcover
      simpa only [cap, SurgeryCapChart.transport_carrier,
        ψ.image_eq_preimage_symm, preimage_univ] using hcover
    cap_boundary := by
      intro i
      change (ψ.symm ⁻¹' E.retained_post) ∩ ψ '' (E.caps i).carrier =
        frontier (ψ '' (E.caps i).carrier)
      rw [← ψ.image_eq_preimage_symm,
        ← Set.image_inter (f := (ψ : (slice T).carrier → (slice' T).carrier)) ψ.injective,
        E.cap_boundary i]
      exact ψ.toHomeomorph.image_frontier _
    necks := E.necks
    neck_carrier_disjoint := E.neck_carrier_disjoint
    neck_time := E.neck_time
    neck_delta := E.neck_delta
    neck_scale := E.neck_scale
    pre_boundary := by
      change frontier (p.symm ⁻¹' E.retained_pre) =
        ⋃ i, (p ∘ E.limit_identify.inverse) '' (E.necks i).neck.central_sphere
      change frontier (p.toHomeomorph.symm ⁻¹' E.retained_pre) = _
      rw [← p.toHomeomorph.image_eq_preimage_symm,
        ← p.toHomeomorph.image_frontier, E.pre_boundary, image_iUnion]
      apply iUnion_congr
      intro i
      exact (image_comp _ _ _).symm
    boundary_correspondence := by
      intro i
      rw [show (M51EventTransport.region E.retention p.symm ψ).map =
          ψ ∘ E.retention.map ∘ p.symm from rfl]
      rw [show (M51EventTransport.region E.limit_identify p.symm
          (Diffeomorph.refl (𝓡 3) E.terminal.carrier ∞)).inverse =
          p ∘ E.limit_identify.inverse from rfl]
      rw [image_comp, image_comp, image_comp, p.symm_image_image,
        E.boundary_correspondence i]
      exact ψ.toHomeomorph.image_frontier _
    neck_negative_retained := by
      intro i
      rw [show (M51EventTransport.region E.limit_identify p.symm
          (Diffeomorph.refl (𝓡 3) E.terminal.carrier ∞)).map '' retainedSet =
          E.limit_identify.map '' E.retained_pre by
        exact M51EventTransport.limit_identify_image_preimage E p E.retained_pre]
      exact E.neck_negative_retained i
    neck_positive_discarded := by
      intro i
      rw [show (M51EventTransport.region E.limit_identify p.symm
          (Diffeomorph.refl (𝓡 3) E.terminal.carrier ∞)).map '' retainedSet =
          E.limit_identify.map '' E.retained_pre by
        exact M51EventTransport.limit_identify_image_preimage E p E.retained_pre]
      exact E.neck_positive_discarded i
    local_result := E.local_result
    local_embed := fun i => ψ ∘ E.local_embed i
    local_embed_smooth := by
      intro i
      exact ψ.contMDiff.comp (E.local_embed_smooth i)
    local_embed_injective := by
      intro i x y hxy
      apply (E.local_embed_injective i)
      exact ψ.injective hxy
    local_metric := by
      intro i x v w
      have he := E.local_metric i x v w
      change (metric' T).inner (ψ (E.local_embed i x))
        (mfderiv (𝓡 3) (𝓡 3) (ψ ∘ E.local_embed i) x v)
        (mfderiv (𝓡 3) (𝓡 3) (ψ ∘ E.local_embed i) x w) = _
      rw [mfderiv_comp x
        (ψ.contMDiff.mdifferentiable (by simp) _)
        ((E.local_embed_smooth i).mdifferentiable (by simp) _)]
      change (metric' T).inner (ψ (E.local_embed i x))
        (mfderiv (𝓡 3) (𝓡 3) ψ (E.local_embed i x)
          (mfderiv (𝓡 3) (𝓡 3) (E.local_embed i) x v))
        (mfderiv (𝓡 3) (𝓡 3) ψ (E.local_embed i x)
          (mfderiv (𝓡 3) (𝓡 3) (E.local_embed i) x w)) = _
      rw [hψ (E.local_embed i x) _ _]
      exact he
    local_tip := by
      intro i
      change ψ (E.local_embed i (E.local_result i).tip) =
        ψ (E.caps i).tip
      rw [E.local_tip]
    local_cap_image := by
      intro i
      change (ψ ∘ E.local_embed i) '' _ = ψ '' (E.caps i).carrier
      rw [image_comp, E.local_cap_image]
    local_retention := by
      intro i x hx
      change ψ (E.local_embed i ((E.local_result i).collapse x)) =
        ψ (E.retention.map (p.symm (p (E.limit_identify.inverse x))))
      rw [p.symm_apply_apply, E.local_retention i x hx]
    disappearing_start := E.disappearing_start
    disappearing_start_bounds := E.disappearing_start_bounds
    disappearing_curvature := by
      intro L hL
      obtain ⟨s, hs, hsT, hcurv⟩ := E.disappearing_curvature L hL
      refine ⟨s, hs, hsT, ?_⟩
      intro t ht x hx
      have hcurv' := hcurv t ht (p.symm x) ?_
      · simpa only [F, RicciFlow.pullbackDiffeomorph_scalarCurvature] using hcurv'
      · intro hinside
        apply hx
        change x ∈ interior (p.symm.toHomeomorph ⁻¹' E.retained_pre)
        rw [← p.symm.toHomeomorph.preimage_interior]
        exact hinside
    disappearing_cover := by
      intro t ht x hx
      have htpre : t ∈ Ico E.tMinus T :=
        ⟨E.disappearing_start_bounds.1.le.trans ht.1, ht.2⟩
      have hsource := E.disappearing_cover t ht (p.symm x) ?_
      · rcases hsource with hN | hcap | hcomp
        · obtain ⟨N, hcenter, heps⟩ := hN
          let e := p.symm
          let he : MetricHomothety (F.metric t) (E.pre_flow.metric t) e 1 :=
            M51EventTransport.pullback_metric_homothety E e ⟨t, htpre⟩
          let H : MetricHomothetyCalculus (F.metric t) (E.pre_flow.metric t) e 1 :=
            M13.metricHomothetyCalculus _ _ e 1 (by norm_num) he
          refine Or.inl ⟨N.m48_pullback he H (F.connection t), ?_, ?_⟩
          · change p N.center = x
            rw [hcenter, p.apply_symm_apply]
          · exact heps
        · obtain ⟨N, hcore, heps, hconstant⟩ := hcap
          let e := p.symm
          let he : MetricHomothety (F.metric t) (E.pre_flow.metric t) e 1 :=
            M51EventTransport.pullback_metric_homothety E e ⟨t, htpre⟩
          let H : MetricHomothetyCalculus (F.metric t) (E.pre_flow.metric t) e 1 :=
            M13.metricHomothetyCalculus _ _ e 1 (by norm_num) he
          refine Or.inr (Or.inl ⟨N.m48_pullback he H (F.connection t), ?_, ?_, ?_⟩)
          · exact hcore
          · exact heps
          · exact hconstant
        · obtain ⟨U, hxU, hUeq, hpositive⟩ := hcomp
          refine Or.inr (Or.inr ⟨connectedComponent x, ?_, rfl, ?_⟩)
          · exact mem_connectedComponent
          · intro y hy v w hpair
            let e := p.symm
            let he : MetricHomothety (F.metric t) (E.pre_flow.metric t) e 1 :=
              M51EventTransport.pullback_metric_homothety E e ⟨t, htpre⟩
            let H : MetricHomothetyCalculus (F.metric t) (E.pre_flow.metric t) e 1 :=
              M13.metricHomothetyCalculus _ _ e 1 (by norm_num) he
            have hy' : p.symm y ∈ U := by
              rw [hUeq]
              exact p.symm.continuous.mapsTo_connectedComponent x hy
            have hp' : LeviCivitaData.IsOrthonormalPair (E.pre_flow.metric t)
                (p.symm y)
                (mfderiv (𝓡 3) (𝓡 3) p.symm y v)
                (mfderiv (𝓡 3) (𝓡 3) p.symm y w) := by
              change LeviCivitaData.IsOrthonormalPair (E.pre_flow.metric t)
                (e y) (mfderiv (𝓡 3) (𝓡 3) e y v)
                (mfderiv (𝓡 3) (𝓡 3) e y w)
              unfold LeviCivitaData.IsOrthonormalPair
              rw [he y v v, he y w w, he y v w]
              simpa only [LeviCivitaData.IsOrthonormalPair, one_mul] using hpair
            have hpos := hpositive (p.symm y) hy' _ _ hp'
            have hsec := H.sectional_eq (F.connection t)
              (E.pre_flow.connection t) y v w
            dsimp only [e] at hsec
            rw [hsec, div_one] at hpos
            exact hpos
      · intro hinside
        apply hx
        change x ∈ interior (p.symm.toHomeomorph ⁻¹' E.retained_pre)
        rw [← p.symm.toHomeomorph.preimage_interior]
        exact hinside }

end SurgeryEventData

end PoincareConjecture
