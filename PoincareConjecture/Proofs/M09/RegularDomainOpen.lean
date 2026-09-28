import PoincareConjecture.Proofs.M09.MinimizingStability
import PoincareConjecture.Proofs.M09.ExponentialLocalInverse
import PoincareConjecture.Proofs.M09.UniqueMinimizingVectors









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem lExponentialFamily_regularDomain_isOpen {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p) :
    IsOpen A.regularDomain := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let Φ : TangentSpace (𝓡 n) p × ℝ → M × ℝ := fun z ↦ (A.gamma z.1 z.2, z.2)
  have hΦ : ContinuousOn Φ (Set.univ ×ˢ Set.Ioo 0 τmax) :=
    A.gamma_smooth.continuousOn.prodMk continuous_snd.continuousOn
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hu := hz.1
  have hb := hz.2
  have ht : 0 < z.2 := by obtain ⟨ht, _, _⟩ := hu; exact ht
  have hm : z.2 < τmax := by obtain ⟨_, hm, _⟩ := hu; exact hm
  obtain ⟨e, hze, hsub, he, _, hderiv⟩ := lExponentialFamily_exists_local_inverse A z ht hm hb
  obtain ⟨N, hN, hzN, _, hstable⟩ := lExponentialFamily_minimizing_stability F hM04 T τmax
    hτmax hwindow hcurvature hL p A z.1 z.2 hu e.source e.open_source hze
  let V := e.source ∩ Φ ⁻¹' N
  have hV : IsOpen V := (hΦ.mono hsub).isOpen_inter_preimage e.open_source hN
  have hzV : z ∈ V := ⟨hze, hzN⟩
  apply Filter.mem_of_superset (hV.mem_nhds hzV)
  intro w hw
  have hwt := (hsub hw.1).2
  have hvec (Y : TangentSpace (𝓡 n) p) (hend : A.gamma Y w.2 = A.gamma w.1 w.2)
      (hmin : IsMinimizingBackwardLPath F T 0 w.2 (A.path Y w.2 hwt.1 hwt.2)) : Y = w.1 := by
    have hYN : (A.gamma Y w.2, w.2) ∈ N := by rw [hend]; exact hw.2
    have hYe : (Y, w.2) ∈ e.source := hstable Y w.2 hwt.1 hwt.2 hYN hmin
    have heq : e (Y, w.2) = e w := by
      rw [he hYe, he hw.1]
      exact Prod.ext hend rfl
    exact congrArg Prod.fst (e.injOn hYe hw.1 heq)
  obtain ⟨Y, hend, hYmin⟩ := lExponentialFamily_exists_minimizing_initialVector hM04 hL
    hτmax hwindow A w.2 hwt.1 hwt.2 (A.gamma w.1 w.2)
  have hmin : IsMinimizingBackwardLPath F T 0 w.2 (A.path w.1 w.2 hwt.1 hwt.2) := by
    simpa only [hvec Y hend hYmin] using hYmin
  exact ⟨(lExponentialFamily_uniqueMinimizing_iff hM04 hL hτmax hwindow A w.1 w.2
    hwt.1 hwt.2).mpr ⟨hmin, hvec⟩, hderiv w hw.1⟩

theorem lExponentialFamily_regularDomain_eq_local {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p) :
    A.regularDomain = A.localRegularDomain := by
  have hopen := lExponentialFamily_regularDomain_isOpen F hM04 T τmax hτmax hwindow
    hcurvature hL p A
  ext z
  constructor
  · intro hz
    obtain ⟨ht, hm, _⟩ := hz.1
    refine ⟨ht, hm, hz.2, (fun W : TangentSpace (𝓡 n) p ↦ (W, z.2)) ⁻¹' A.regularDomain,
      hopen.preimage (continuous_id.prodMk continuous_const), hz, ?_⟩
    intro W hW
    exact hW.1
  · rintro ⟨_, _, hb, N, _, hzN, hN⟩
    exact ⟨hN z.1 hzN, hb⟩

end PoincareConjecture.Proofs.M09
