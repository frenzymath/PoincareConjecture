import PoincareConjecture.Proofs.M09.CompactMinimizingPreimages








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem lExponentialFamily_minimizing_stability {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p)
    (Z0 : TangentSpace (𝓡 n) p) (t0 : ℝ) (hunique : A.uniqueMinimizing Z0 t0)
    (U : Set (TangentSpace (𝓡 n) p × ℝ)) (hU : IsOpen U) (hzU : (Z0, t0) ∈ U) :
    ∃ N : Set (M × ℝ), IsOpen N ∧ (A.gamma Z0 t0, t0) ∈ N ∧
      N ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      ∀ Z τ (ht : 0 < τ) (hm : τ < τmax), (A.gamma Z τ, τ) ∈ N →
        IsMinimizingBackwardLPath F T 0 τ (A.path Z τ ht hm) → (Z, τ) ∈ U := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨ht0, hm0, _, huniq⟩ := hunique
  let y0 : M × ℝ := (A.gamma Z0 t0, t0)
  obtain ⟨Q, hQnear, hQt, hQ⟩ := local_compact_nhds
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show y0 ∈ Set.univ ×ˢ Set.Ioo 0 τmax from ⟨Set.mem_univ _, ht0, hm0⟩))
  let S := {z : TangentSpace (𝓡 n) p × ℝ |
    ∃ (ht : 0 < z.2) (hm : z.2 < τmax), (A.gamma z.1 z.2, z.2) ∈ Q ∧
      IsMinimizingBackwardLPath F T 0 z.2 (A.path z.1 z.2 ht hm)}
  have hS : IsCompact S := lExponentialFamily_isCompact_minimizing_preimage F hM04 T τmax
    hτmax hwindow hcurvature hL p A Q hQ hQt
  let Φ : TangentSpace (𝓡 n) p × ℝ → M × ℝ := fun z ↦ (A.gamma z.1 z.2, z.2)
  have hΦ : ContinuousOn Φ S :=
    (A.gamma_smooth.continuousOn.mono (by
      rintro z ⟨ht, hm, _⟩
      exact ⟨Set.mem_univ _, ht, hm⟩)).prodMk continuous_snd.continuousOn
  let C := Φ '' (S ∩ Uᶜ)
  have hC : IsCompact C := (hS.inter_right hU.isClosed_compl).image_of_continuousOn
    (hΦ.mono Set.inter_subset_left)
  have hyC : y0 ∉ C := by
    rintro ⟨⟨Z, τ⟩, ⟨⟨ht, hm, hmem, hpath⟩, hout⟩, heq⟩
    have htime : τ = t0 := congrArg Prod.snd heq
    subst τ
    have hend : A.gamma Z t0 = A.gamma Z0 t0 := congrArg Prod.fst heq
    have hcurve := huniq (A.path Z t0 ht hm)
      ((congrFun (A.path_eq Z t0 ht hm) 0).trans (A.gamma_at_zero Z))
      ((congrFun (A.path_eq Z t0 ht hm) t0).trans hend) hpath
    rw [A.path_eq] at hcurve
    have hZ := lExponentialFamily_initialVector_eq_of_eqOn A Z Z0 t0 ht hm hcurve
    exact hout (hZ.symm ▸ hzU)
  refine ⟨interior Q ∩ Cᶜ, isOpen_interior.inter hC.isClosed.isOpen_compl,
    ⟨mem_interior_iff_mem_nhds.mpr hQnear, hyC⟩,
    (fun w hw ↦ hQt (interior_subset hw.1)), ?_⟩
  intro Z τ ht hm hmem hpath
  by_contra hout
  apply hmem.2
  exact ⟨(Z, τ), ⟨⟨ht, hm, interior_subset hmem.1, hpath⟩, hout⟩, rfl⟩

end PoincareConjecture.Proofs.M09
