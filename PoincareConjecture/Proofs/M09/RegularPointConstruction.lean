import PoincareConjecture.Proofs.M09.RegularChart
import PoincareConjecture.Proofs.M09.RegularRepresentative
import PoincareConjecture.Proofs.M09.HarnackIntegrability

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

theorem lExponentialFamily_exists_regularPoint_of_chart {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p : M} (A : LExponentialFamily F T τmax p)
    (G : OpenPartialHomeomorph (TangentSpace (𝓡 n) p × ℝ) (M × ℝ))
    (hsource : G.source = A.regularDomain)
    (hforward : ∀ z, G z = (A.gamma z.1 z.2, z.2))
    (hinv : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
      ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) ∞ G.symm G.target)
    (htarget : G.target ⊆ Set.univ ×ˢ Set.Ioo 0 τmax)
    (htime : ∀ z ∈ G.target, (G.symm z).2 = z.2) (z : M × ℝ) (hz : z ∈ G.target) :
    ∃ r : ReducedLengthRegularPoint F T τmax p z.1 z.2,
      r.path.curve = A.gamma (G.symm z).1 ∧ r.neighborhood = G.target ∧
      r.representative = fun w ↦ A.action (G.symm w).1 w.2 / (2 * Real.sqrt w.2) := by
  have hregular (w : M × ℝ) (hw : w ∈ G.target) :
      A.uniqueMinimizing (G.symm w).1 w.2 := by
    have hmem : G.symm w ∈ A.regularDomain := hsource ▸ G.map_target hw
    have hu := hmem.1
    rw [htime w hw] at hu
    exact hu
  have hend (w : M × ℝ) (hw : w ∈ G.target) : A.gamma (G.symm w).1 w.2 = w.1 := by
    have heq := congrArg Prod.fst ((hforward (G.symm w)).symm.trans (G.right_inv hw))
    simpa only [htime w hw] using heq
  let f : M × ℝ → ℝ := fun w ↦ A.action (G.symm w).1 w.2 / (2 * Real.sqrt w.2)
  have hf := lExponentialFamily_regular_representative_smooth hM04 hτmax hwindow A G htarget hinv
  have hfvalue (w : M × ℝ) (hw : w ∈ G.target) : f w = reducedLength F T p w.1 w.2 := by
    obtain ⟨ht, hm, hmin, _⟩ := hregular w hw
    have h := (lExponentialFamily_reducedLength_eq_action_iff hL A
      (G.symm w).1 w.2 ht hm).mpr hmin
    rw [hend w hw] at h
    exact h.symm
  obtain ⟨ht, hm, hmin, huniq⟩ := hregular z hz
  let P := A.path (G.symm z).1 z.2 ht hm
  have hP0 : P.curve 0 = p := (congrFun (A.path_eq _ _ ht hm) 0).trans (A.gamma_at_zero _)
  have hPend : P.curve z.2 = z.1 := (congrFun (A.path_eq _ _ ht hm) z.2).trans (hend z hz)
  have hspace : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ f (x, z.2)) {x | (x, z.2) ∈ G.target} :=
    hf.comp (contMDiffOn_id.prodMk contMDiffOn_const) (fun x hx ↦ hx)
  have hcenter := hf.contMDiffAt (G.open_target.mem_nhds hz)
  have htimeDerivative : ∃ d : ℝ, HasDerivAt (fun t ↦ f (z.1, t)) d z.2 := by
    have h := (hcenter.comp z.2 (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt
    exact ⟨_, (h.differentiableAt (by simp)).hasDerivAt⟩
  refine ⟨{
    tau_pos := ht
    tau_lt := hm
    path := P
    path_start := hP0
    path_end := hPend
    minimizing := hmin
    path_realizes_reduced_length := reducedLength_eq_minimizing_path hL ht hm.le P hP0 hPend hmin
    unique_minimizing_path := ?_
    neighborhood := G.target
    neighborhood_open := G.open_target
    center_mem := hz
    representative := f
    representative_eq := hfvalue
    representative_spacetime_smooth := hcenter
    representative_space_smooth_on := hspace
    representative_space_smooth := hcenter.comp z.1 (contMDiffAt_id.prodMk contMDiffAt_const)
    representative_time_derivative := htimeDerivative
    path_scalar_time_derivative := backwardScalarEvolutionAlong F T P.curve
    path_scalar_time_derivative_spec := ?_
    harnack_integrable := ?_ }, A.path_eq _ _ ht hm, rfl, rfl⟩
  · intro q hq0 hqend hqmin
    have hqend' : q.curve z.2 = A.gamma (G.symm z).1 z.2 := hqend.trans (hend z hz).symm
    simpa only [P, A.path_eq] using huniq q hq0 hqend' hqmin
  · intro s hs
    exact backward_scalar_hasDerivWithinAt hM04 hwindow hm.le
      (Set.Ioo_subset_Icc_self hs) (P.curve s)
  · change IntervalIntegrable (fun s ↦ s * Real.sqrt s * reducedHarnackDensity F T P.curve
      (backwardScalarEvolutionAlong F T P.curve) s) MeasureTheory.volume 0 z.2
    simp only [P, A.path_eq]
    exact lExponentialFamily_harnack_integrable hM04 hτmax hwindow A (G.symm z).1 z.2 ht hm

end PoincareConjecture.Proofs.M09
