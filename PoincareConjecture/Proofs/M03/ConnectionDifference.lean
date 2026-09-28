import PoincareConjecture.Proofs.M03.ConnectionFamily

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem connection_difference_eq_zero {g : RiemannianMetric n M}
    (D D' : LeviCivitaData g) (x : M) :
    CovariantDerivative.difference D.connection D'.connection x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hdiff := IsCovariantDerivativeOn.difference_apply
    D.connection.isCovariantDerivativeOnUniv D'.connection.isCovariantDerivativeOnUniv
    (Set.mem_univ x) hv
  rw [FiberBundle.extend_apply_self] at hdiff
  change CovariantDerivative.difference D.connection D'.connection x v =
    D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x -
      D'.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x at hdiff
  change CovariantDerivative.difference D.connection D'.connection x v = 0
  rw [hdiff, D.connection_eq_at D' _ hv, sub_self]

theorem contMDiffOn_connection_family_difference
    {g g' : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (hg' : RiemannianMetric.IsSmoothFamilyOn g' J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    (D' : (t : ℝ) → LeviCivitaData (g' t)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
          TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
        p.2 (CovariantDerivative.difference
          (D p.1).connection (D' p.1).connection p.2)) (J ×ˢ Set.univ) := by
  intro p hp
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.2
  have hep : p.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.2
  let frame (a : EuclideanSpace ℝ (Fin n)) (x : M) : TangentSpace (𝓡 n) x :=
    e.symmL ℝ x a
  have hframe (a : EuclideanSpace ℝ (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (frame a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro x hx
    simpa [frame, Trivialization.symmL_apply _ hx] using
      congrArg Prod.snd (e.apply_mk_symm hx a)
  let C (q : ℝ × M) : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
      p.2 q.2 p.2 q.2
      (CovariantDerivative.difference (D q.1).connection (D' q.1).connection q.2)
  have hbase : ∀ᶠ q in 𝓝[J ×ˢ (Set.univ : Set M)] p, q.2 ∈ e.baseSet :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hep))
  have hsmall : J ×ˢ e.baseSet ∈ 𝓝[J ×ˢ (Set.univ : Set M)] p := by
    filter_upwards [self_mem_nhdsWithin, hbase] with q hq hqe
    exact ⟨hq.1, hqe⟩
  have hC : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      C (J ×ˢ Set.univ) p := by
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro a
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro b
    have hs₁ := contMDiffOn_connection_family_apply hg D e.open_baseSet
      (frame a) (frame b) (hframe a) (hframe b)
    have hs₂ := contMDiffOn_connection_family_apply hg' D' e.open_baseSet
      (frame a) (frame b) (hframe a) (hframe b)
    have hc₁ := (Bundle.contMDiffWithinAt_totalSpace.mp
      ((hs₁ p ⟨hp.1, hep⟩).mono_of_mem_nhdsWithin hsmall)).2
    have hc₂ := (Bundle.contMDiffWithinAt_totalSpace.mp
      ((hs₂ p ⟨hp.1, hep⟩).mono_of_mem_nhdsWithin hsmall)).2
    apply (hc₁.sub hc₂).congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [hbase] with q hq
    dsimp [C]
    rw [inCoordinates_apply_eq₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
      (F₃ := EuclideanSpace ℝ (Fin n))
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := TangentSpace (𝓡 n)) hq hq hq]
    rw [← Trivialization.symmL_apply (R := ℝ) e hq a,
      ← Trivialization.symmL_apply (R := ℝ) e hq b]
    have ha := ((hframe a).contMDiffAt
      (e.open_baseSet.mem_nhds hq)).mdifferentiableAt (by simp)
    have hdiff := IsCovariantDerivativeOn.difference_apply
      (D q.1).connection.isCovariantDerivativeOnUniv
      (D' q.1).connection.isCovariantDerivativeOnUniv (Set.mem_univ q.2) ha
    change CovariantDerivative.difference (D q.1).connection (D' q.1).connection q.2
      (frame a q.2) = (D q.1).connection (frame a) q.2 -
        (D' q.1).connection (frame a) q.2 at hdiff
    change e.linearMapAt ℝ q.2
      (CovariantDerivative.difference (D q.1).connection (D' q.1).connection q.2
        (frame a q.2) (frame b q.2)) = _
    rw [hdiff, sub_apply, map_sub]
    simp only [Trivialization.linearMapAt_apply, if_pos hq]
    rfl
  let F : ℝ × M → TotalSpace (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (fun x => TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) :=
    fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) q.2
      (CovariantDerivative.difference (D q.1).connection (D' q.1).connection q.2)
  exact (contMDiffWithinAt_hom_bundle F (s := J ×ˢ Set.univ) (x₀ := p)).mpr
    ⟨contMDiffWithinAt_snd, hC⟩

end PoincareConjecture.Proofs.M03
