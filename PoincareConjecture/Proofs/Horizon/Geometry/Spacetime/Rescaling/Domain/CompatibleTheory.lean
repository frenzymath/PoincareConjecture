import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.Intervals










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem rescaledCompatibleTheory
    (H : CompatibleSpacetimeTheory.{u, v} R.spacetime R.timeIntervals) :
    CompatibleSpacetimeTheory.{u, v} (parabolicSpacetime R.spacetime Q hQ a)
      R.timeIntervals := by
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  refine {
    worldline_unique := ?_
    embedding_unique := ?_
    embedding_time_restrict := ?_
    cylinder_time_restrict := ?_
    embedding_source_restrict := ?_
    cylinder_open_restrict := ?_
    cylinder_glue := ?_
    cylinder_metric := ?_ }
  · intro K L
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    obtain ⟨L, rfl⟩ := parabolicInterval_surjective Q hQ a L
    intro e f s₀ hK hL hef s hsK hsL
    have h₀ : (untransportedWorldline K e).curve
        ⟨parabolicTimeInv Q a s₀, (mem_parabolicInterval_iff Q hQ a K s₀).1 hK⟩ =
      (untransportedWorldline L f).curve
        ⟨parabolicTimeInv Q a s₀, (mem_parabolicInterval_iff Q hQ a L s₀).1 hL⟩ := by
      rw [untransportedWorldline_point, untransportedWorldline_point]
      exact hef
    have h := H.worldline_unique K L (untransportedWorldline K e)
      (untransportedWorldline L f) (parabolicTimeInv Q a s₀) _ _ h₀
      (parabolicTimeInv Q a s) ((mem_parabolicInterval_iff Q hQ a K s).1 hsK)
      ((mem_parabolicInterval_iff Q hQ a L s).1 hsL)
    rw [untransportedWorldline_point, untransportedWorldline_point] at h
    exact h
  · intro C _ K L
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    obtain ⟨L, rfl⟩ := parabolicInterval_surjective Q hQ a L
    intro e f s₀ hK hL source he hf s hsK hsL x
    have he₀ : (untransportedEmbedding K e).IsBasedAt
        ⟨parabolicTimeInv Q a s₀, (mem_parabolicInterval_iff Q hQ a K s₀).1 hK⟩ source := by
      intro y
      exact (untransportedEmbedding_point K e s₀ hK y).trans (he y)
    have hf₀ : (untransportedEmbedding L f).IsBasedAt
        ⟨parabolicTimeInv Q a s₀, (mem_parabolicInterval_iff Q hQ a L s₀).1 hL⟩ source := by
      intro y
      exact (untransportedEmbedding_point L f s₀ hL y).trans (hf y)
    have h := H.embedding_unique C K L (untransportedEmbedding K e)
      (untransportedEmbedding L f) (parabolicTimeInv Q a s₀) _ _ source he₀ hf₀
      (parabolicTimeInv Q a s) ((mem_parabolicInterval_iff Q hQ a K s).1 hsK)
      ((mem_parabolicInterval_iff Q hQ a L s).1 hsL) x
    rw [untransportedEmbedding_point, untransportedEmbedding_point] at h
    exact h
  · intro C _ K L
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    obtain ⟨L, rfl⟩ := parabolicInterval_surjective Q hQ a L
    intro h e
    let h₀ := interval_subset_of_parabolic h
    obtain ⟨r, hr⟩ := H.embedding_time_restrict C K L h₀ (untransportedEmbedding K e)
    refine ⟨transportedEmbedding L r, ?_⟩
    intro s x
    change r.toSpacetime ((P.diffeomorph L).symm s, x) = _
    rw [hr]
    change e.toSpacetime
      (P.diffeomorph K (spacetimeIntervalInclusion _ _ h₀ ((P.diffeomorph L).symm s)), x) = _
    apply congrArg (fun t ↦ e.toSpacetime (t, x))
    apply Subtype.ext
    exact parabolicTime_parabolicTimeInv Q hQ a s.val
  · intro C _ _ _ K L
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    obtain ⟨L, rfl⟩ := parabolicInterval_surjective Q hQ a L
    intro h e
    let h₀ := interval_subset_of_parabolic h
    obtain ⟨r, hr⟩ := H.cylinder_time_restrict C K L h₀ (untransportedCylinder K e)
    refine ⟨transportedCylinder L r, ?_⟩
    intro s x
    change r.toSpacetime ((P.diffeomorph L).symm s, x) = _
    rw [hr]
    change e.toSpacetime
      (P.diffeomorph K (spacetimeIntervalInclusion _ _ h₀ ((P.diffeomorph L).symm s)), x) = _
    apply congrArg (fun t ↦ e.toSpacetime (t, x))
    apply Subtype.ext
    exact parabolicTime_parabolicTimeInv Q hQ a s.val
  · intro C C' _ _ K
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    intro e j hj
    obtain ⟨r, hr⟩ := H.embedding_source_restrict C C' K (untransportedEmbedding K e) j hj
    refine ⟨transportedEmbedding K r, ?_⟩
    intro s x
    change r.toSpacetime ((P.diffeomorph K).symm s, x) = _
    rw [hr]
    change e.toSpacetime (P.diffeomorph K ((P.diffeomorph K).symm s), j x) = _
    rw [Diffeomorph.apply_symm_apply]
  · intro C _ _ _ K
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    intro e U
    obtain ⟨r, hr⟩ := H.cylinder_open_restrict C K (untransportedCylinder K e) U
    refine ⟨transportedCylinder K r, ?_⟩
    intro s x
    change r.toSpacetime ((P.diffeomorph K).symm s, x) = _
    rw [hr]
    change e.toSpacetime (P.diffeomorph K ((P.diffeomorph K).symm s), x.val) = _
    rw [Diffeomorph.apply_symm_apply]
  · intro C _ _ _ K B J
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    obtain ⟨J, rfl⟩ := parabolicInterval_family_surjective Q hQ a J
    intro hsub hopen hcover localCylinder hoverlap
    let hsub₀ : ∀ b, (J b).domain ⊆ K.domain := fun b ↦ interval_subset_of_parabolic (hsub b)
    have hopen₀ : ∀ b, IsOpen {t : K.domain | t.val ∈ (J b).domain} :=
      fun b ↦ (relative_time_open_iff Q hQ a K (J b)).1 (hopen b)
    have hcover₀ : ∀ t : K.domain, ∃ b, t.val ∈ (J b).domain :=
      (time_cover_iff Q hQ a K B J).1 hcover
    let local₀ := fun b ↦ untransportedCylinder (J b) (localCylinder b)
    have hoverlap₀ : ∀ (b c : B) (t : ℝ) (hb : t ∈ (J b).domain)
        (hc : t ∈ (J c).domain) (x : C),
        (local₀ b).toSpacetime (⟨t, hb⟩, x) = (local₀ c).toSpacetime (⟨t, hc⟩, x) := by
      intro b c t hb hc x
      exact hoverlap b c (parabolicTime Q a t)
        ((parabolicTime_mem_parabolicInterval_iff Q hQ a (J b) t).2 hb)
        ((parabolicTime_mem_parabolicInterval_iff Q hQ a (J c) t).2 hc) x
    obtain ⟨e, he, _⟩ := H.cylinder_glue C K B J hsub₀ hopen₀ hcover₀ local₀ hoverlap₀
    let e' := transportedCylinder (R := R) (Q := Q) (hQ := hQ) (a := a) K e
    have he' : ∀ (b : B)
        (t : (R.timeIntervals.interval (parabolicInterval Q hQ a (J b))).Point) (x : C),
        e'.toSpacetime (spacetimeIntervalInclusion _ _ (hsub b) t, x) =
          (localCylinder b).toSpacetime (t, x) := by
      intro b t x
      change e.toSpacetime ((P.diffeomorph K).symm
        (spacetimeIntervalInclusion _ _ (hsub b) t), x) = _
      rw [affineInterval_inverse_inclusion R.timeIntervals Q hQ a K (J b) (hsub₀ b), he]
      exact untransportedCylinder_point (J b) (localCylinder b) t.val t.property x
    refine ⟨e', he', ?_⟩
    intro b t source hb x
    exact (he' b t x).trans (hb x)
  · intro C _ _ _ K
    obtain ⟨K, rfl⟩ := parabolicInterval_surjective Q hQ a K
    intro e
    obtain ⟨G⟩ := H.cylinder_metric C K (untransportedCylinder K e)
    have h := transportedCylinderMetric (R := R) (Q := Q) (hQ := hQ) (a := a)
      K (untransportedCylinder K e) G
    have he : transportedCylinder (R := R) (Q := Q) (hQ := hQ) (a := a)
        K (untransportedCylinder K e) = e := (cylinderEquiv C K).apply_symm_apply e
    rw [he] at h
    exact ⟨h⟩

end PoincareConjecture.ParabolicRescaling
