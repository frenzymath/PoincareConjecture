import PoincareConjecture.Proofs.M09.ParametricEndpointFamily
import PoincareConjecture.Proofs.M09.UnitIntervalAction
import PoincareConjecture.Proofs.M09.MinimizingInitialVectors
import PoincareConjecture.Proofs.M09.ActionCongruence
import Mathlib.Geometry.Manifold.Algebra.LieGroup








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => TangentSpace (𝓡 n) p × ℝ

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_exists_parametric_comparison_action
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z0 : TangentSpace (𝓡 n) p)
    (b0 : ℝ) (hb0 : 0 < b0) (hmax0 : b0 < τmax) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    let e := chartAt E (A.gamma Z0 b0)
    ∃ (W : Set P) (V : Set (P × E)) (C : (P × E) × ℝ → ℝ),
      IsOpen W ∧ (Z0, b0) ∈ W ∧ W ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      IsOpen V ∧ V ⊆ W ×ˢ e.target ∧
      ContDiffOn ℝ ∞ C (V ×ˢ Set.Ioo 0 τmax) ∧
      ∀ a ∈ W, A.gamma a.1 a.2 ∈ e.source ∧ (a, e (A.gamma a.1 a.2)) ∈ V ∧
        ∀ (ha : 0 < a.2) (hmax : a.2 < τmax),
          IsMinimizingBackwardLPath F T 0 a.2 (A.path a.1 a.2 ha hmax) →
          ∃ B : ReducedLengthUpperBarrier F T p (A.gamma a.1 a.2) a.2,
            B.representative = fun w ↦ C ((a, e w.1), w.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  let e := chartAt E (A.gamma Z0 b0)
  let S : Set (P × ℝ) := (Set.univ ×ˢ Set.Ioo 0 τmax) ×ˢ Set.univ
  let Φ : P × ℝ → TangentSpace (𝓡 n) p × ℝ :=
    fun z ↦ (z.1.1, Real.sqrt z.1.2 * z.2)
  let D := S ∩ Φ ⁻¹' A.squareDomain
  let γ : P × ℝ → M := fun z ↦ A.squareFamily z.1.1 (Real.sqrt z.1.2 * z.2)
  have hS : IsOpen S := (isOpen_univ.prod isOpen_Ioo).prod isOpen_univ
  have hΦ : ContDiffOn ℝ ∞ Φ S := contDiff_fst.fst.contDiffOn.prodMk
    ((contDiff_fst.snd.contDiffOn.sqrt (fun z hz ↦ hz.1.2.1.ne')).mul contDiffOn_snd)
  have hD : IsOpen D := hΦ.continuousOn.isOpen_inter_preimage hS A.square_open
  have hA : ContMDiffOn (𝓘(ℝ, TangentSpace (𝓡 n) p × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.squareFamily z.1 z.2) A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hγ : ContMDiffOn (𝓘(ℝ, P × ℝ)) (𝓡 n) ∞ γ D :=
    hA.comp (hΦ.mono Set.inter_subset_left).contMDiffOn (fun z hz ↦ hz.2)
  have hI : ∀ r ∈ Set.Icc (0 : ℝ) 1, ((Z0, b0), r) ∈ D := by
    intro r hr
    refine ⟨⟨⟨Set.mem_univ _, hb0, hmax0⟩, Set.mem_univ _⟩, ?_⟩
    exact A.square_contains ⟨Set.mem_univ _, mul_nonneg (Real.sqrt_nonneg _) hr.1,
      (mul_le_of_le_one_right (Real.sqrt_nonneg _) hr.2).trans_lt
        (Real.sqrt_lt_sqrt hb0.le hmax0)⟩
  have hγstart (a : P) : γ (a, 0) = p := by
    simp only [γ, mul_zero, A.square_at_zero]
  have hγend (a : P) (ha : 0 < a.2) (hmax : a.2 < τmax) :
      γ (a, 1) = A.gamma a.1 a.2 := by
    dsimp only [γ]
    rw [mul_one, A.square_agrees a.1 (Real.sqrt a.2)
      ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt ha.le hmax⟩, Real.sq_sqrt ha.le]
  obtain ⟨f, Ω, V, W, hΩ, hV, hW, haW, haV, hVe, hVΩ, hf,
      hstart, hend, hWD, hgraph, hcenter⟩ :=
    exists_parametric_smooth_endpoint_family γ D hD hγ (Z0, b0) hI
  have hγend0 := hγend (Z0, b0) hb0 hmax0
  rw [hγend0] at haV hVe hend hgraph hcenter
  have hWt : W ⊆ Set.univ ×ˢ Set.Ioo 0 τmax := by
    intro a ha
    exact (hWD (show (a, (0 : ℝ)) ∈ W ×ˢ Set.Icc 0 1 from
      ⟨ha, le_rfl, zero_le_one⟩)).1.1
  have hgraph' (a : P) (ha : a ∈ W) : (a, e (A.gamma a.1 a.2)) ∈ V := by
    have h := hgraph a ha
    rwa [hγend a (hWt ha).2.1 (hWt ha).2.2] at h
  have hsource (a : P) (ha : a ∈ W) : A.gamma a.1 a.2 ∈ e.source := by
    have hy : e (A.gamma a.1 a.2) ∈ e.target := (hVe (hgraph' a ha)).2
    have heq : e.symm (e (A.gamma a.1 a.2)) = A.gamma a.1 a.2 := by
      have h := hcenter a ha 1 ⟨zero_le_one, le_rfl⟩
      rw [hγend a (hWt ha).2.1 (hWt ha).2.2, hend] at h
      exact h
    rw [← heq]
    exact e.map_target hy
  let L : (P × E) × ℝ → ℝ := fun z ↦ backwardLLength F T 0 z.2
    (fun t ↦ f (z.1, Real.sqrt t / Real.sqrt z.2))
  let C : (P × E) × ℝ → ℝ := fun z ↦ L z / (2 * Real.sqrt z.2)
  have hLaction : ContDiffOn ℝ ∞ L (V ×ˢ Set.Ioo 0 τmax) :=
    contDiffOn_unitFamily_action F hM04 T τmax hτmax hwindow f Ω hΩ hf V hV hVΩ
  have hroot : ContDiffOn ℝ ∞ (fun z : (P × E) × ℝ ↦ Real.sqrt z.2)
      (V ×ˢ Set.Ioo 0 τmax) := contDiffOn_snd.sqrt (fun z hz ↦ hz.2.1.ne')
  have hC : ContDiffOn ℝ ∞ C (V ×ˢ Set.Ioo 0 τmax) :=
    hLaction.div (contDiffOn_const.mul hroot)
      (fun z hz ↦ (mul_pos zero_lt_two (Real.sqrt_pos.mpr hz.2.1)).ne')
  refine ⟨W, V, C, hW, haW, hWt, hV, hVe, hC, ?_⟩
  intro a ha
  refine ⟨hsource a ha, hgraph' a ha, ?_⟩
  intro ht hmax hmin
  let q := A.gamma a.1 a.2
  let c : M × ℝ → (P × E) × ℝ := fun w ↦ ((a, e w.1), w.2)
  let Cdom : Set (M × ℝ) := e.source ×ˢ Set.univ
  let N := Cdom ∩ c ⁻¹' (V ×ˢ Set.Ioo 0 τmax)
  let B : M × ℝ → ℝ := fun w ↦ C (c w)
  have hc : ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, (P × E) × ℝ)) ∞ c Cdom :=
    (contMDiffOn_const.prodMk_space
      (contMDiffOn_chart.comp contMDiffOn_fst (fun w hw ↦ hw.1))).prodMk_space contMDiffOn_snd
  have hN : IsOpen N := hc.continuousOn.isOpen_inter_preimage
    (e.open_source.prod isOpen_univ) (hV.prod isOpen_Ioo)
  have hqN : (q, a.2) ∈ N := ⟨⟨hsource a ha, Set.mem_univ _⟩, hgraph' a ha, ht, hmax⟩
  have hB : ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ B N :=
    hC.contMDiffOn.comp (hc.mono Set.inter_subset_left) (fun w hw ↦ hw.2)
  have hBat := hB.contMDiffAt (hN.mem_nhds hqN)
  have hBtime : ∃ d : ℝ, HasDerivAt (fun s ↦ B (q, s)) d a.2 := by
    have h := (hBat.comp a.2 (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt
    exact ⟨_, (h.differentiableAt (by simp)).hasDerivAt⟩
  refine ⟨{
    neighborhood := N
    neighborhood_open := hN
    center_mem := hqN
    representative := B
    touches := ?_
    dominates := ?_
    representative_spacetime_smooth := hBat
    representative_space_smooth_on := hB.comp
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun x hx ↦ hx)
    representative_space_smooth := hBat.comp q (contMDiffAt_id.prodMk contMDiffAt_const)
    representative_time_derivative := hBtime }, rfl⟩
  · have heq : Set.EqOn (fun t ↦ f ((a, e q), Real.sqrt t / Real.sqrt a.2))
        (A.gamma a.1) (Set.Ioo 0 a.2) := by
      intro t htt
      have hr : Real.sqrt t / Real.sqrt a.2 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
          (div_le_one (Real.sqrt_pos.mpr ht)).mpr (Real.sqrt_le_sqrt htt.2.le)⟩
      have h := hcenter a ha (Real.sqrt t / Real.sqrt a.2) hr
      rw [hγend a ht hmax] at h
      change f ((a, e q), Real.sqrt t / Real.sqrt a.2) =
        A.squareFamily a.1 (Real.sqrt a.2 * (Real.sqrt t / Real.sqrt a.2)) at h
      rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr ht).ne',
        A.square_agrees a.1 (Real.sqrt t)
          ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt htt.1.le (htt.2.trans hmax)⟩,
        Real.sq_sqrt htt.1.le] at h
      exact h
    change backwardLLength F T 0 a.2
      (fun t ↦ f ((a, e q), Real.sqrt t / Real.sqrt a.2)) / (2 * Real.sqrt a.2) = _
    rw [backwardLLength_congr_Ioo F T 0 a.2 ht.le _ _ heq]
    exact ((lExponentialFamily_reducedLength_eq_action_iff hL A a.1 a.2 ht hmax).mpr hmin).symm
  · intro w hw
    obtain ⟨Q, hQ⟩ := exists_backwardPath_of_unitFamily F hM04 T τmax hτmax hwindow
      f Ω hΩ hf (a, e w.1) (fun r hr ↦ hVΩ ⟨hw.2.1, hr⟩)
      w.2 hw.2.2.1 hw.2.2.2
    have hQ0 : Q.curve 0 = p := by
      rw [hQ]
      simpa only [Real.sqrt_zero, zero_div, hstart] using hγstart a
    have hQw : Q.curve w.2 = w.1 := by
      rw [hQ]
      change f ((a, e w.1), Real.sqrt w.2 / Real.sqrt w.2) = w.1
      have hwt : 0 < w.2 := hw.2.2.1
      rw [div_self (Real.sqrt_pos.mpr hwt).ne', hend]
      exact e.left_inv hw.1.1
    have h := reducedLength_le_path hL hw.2.2.1 hw.2.2.2.le Q hQ0 hQw
    simpa only [hQ] using h

end PoincareConjecture.Proofs.M09
