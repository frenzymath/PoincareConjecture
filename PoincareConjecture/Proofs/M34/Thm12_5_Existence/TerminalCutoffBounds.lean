import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalPullbackBounds
import PoincareConjecture.Proofs.M34.Standard.CutoffMetric
import PoincareConjecture.Proofs.M34.Standard.TranslatedEndCharts
import PoincareConjecture.Proofs.M34.Standard.PullbackCurvatureJetBound
import PoincareConjecture.Proofs.M34.Mathlib.SmoothTransitionJetBounds
import PoincareConjecture.Proofs.M34.Mathlib.LocalJetProductBounds












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34.PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S) (P : RicciFlowCurvatureTheory.{0})
  (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)




theorem cutoffMetric_compactPullback_ellipticity
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∃ a : ℝ, 0 < a ∧ ∀ R : ℝ, ∀ x ∈ K,
      ∀ f : StandardCapSpace → StandardCapSpace,
      (∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x u)
          (mfderiv (𝓡 3) (𝓡 3) f x v)) →
      ∀ v : StandardCapSpace, a * ‖v‖ ^ 2 ≤
        (cutoffMetric g0.cylindrical_end (L.metric P E0 hS hSF hB hfull) R).pullbackCoefficients
          f x v v := by
  obtain ⟨a, _b, ha, _hb, hterminal⟩ :=
    L.metric_compactPullback_ellipticity P E0 hS hSF hB hfull hK
  obtain ⟨a0, ha0, hinitial⟩ := exists_uniform_bilinear_family_lower_bound hK
    (fun x _ => (g0.metric.contDiffAt_euclideanCoefficients x).continuousAt.continuousWithinAt)
    (fun x _ v hv => g0.metric.pos x v hv)
  refine ⟨min a a0, lt_min ha ha0, fun R x hx f hf v => ?_⟩
  have hleft := (mul_le_mul_of_nonneg_right (min_le_left a a0) (sq_nonneg ‖v‖)).trans
    (hterminal x hx f hf v).1
  have hright : min a a0 * ‖v‖ ^ 2 ≤ g0.metric.pullbackCoefficients f x v v := by
    change min a a0 * ‖v‖ ^ 2 ≤ g0.metric.inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v)
    rw [← hf v v]
    exact (mul_le_mul_of_nonneg_right (min_le_right a a0) (sq_nonneg ‖v‖)).trans
      (hinitial x hx v)
  let r := endCutoffWeight g0.cylindrical_end R (f x)
  have hr := endCutoffWeight_mem_Icc g0.cylindrical_end R (f x)
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hr.2))
    (mul_le_mul_of_nonneg_left hright hr.1)
  change min a a0 * ‖v‖ ^ 2 ≤
    (1 - r) * (L.metric P E0 hS hSF hB hfull).pullbackCoefficients f x v v +
      r * g0.metric.pullbackCoefficients f x v v
  nlinarith only [hsum]

set_option synthInstance.maxHeartbeats 100000 in




theorem cutoffMetric_compactPullback_spatialJet_bounds
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ j ≤ m, ∀ R : ℝ,
      ∀ {U : Set StandardCapSpace}, IsOpen U →
      ∀ {f : StandardCapSpace → StandardCapSpace}, ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
      (∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) f x).IsInvertible) →
      (∀ x ∈ U, ∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x u)
          (mfderiv (𝓡 3) (𝓡 3) f x v)) →
      ∀ q : ℝ, (∀ x ∈ U, endExhaustion g0.cylindrical_end (f x) =
        endExhaustion g0.cylindrical_end x + q) →
      ∀ x ∈ K, x ∈ U → ‖iteratedFDeriv ℝ j
        ((cutoffMetric g0.cylindrical_end (L.metric P E0 hS hSF hB hfull) R).pullbackCoefficients
          f) x‖ ≤ G := by
  obtain ⟨G, hG, hmetric⟩ :=
    L.closedFlow_compactPullback_spatialJet_bounds P E0 hS hSF hB hfull hK m
  have hρ : ContDiff ℝ ∞ (endExhaustion g0.cylindrical_end) :=
    contMDiff_iff_contDiff.mp (endExhaustion_contMDiff g0.cylindrical_end)
  obtain ⟨A, hA, hweights⟩ := Real.smoothTransition.uniform_spatial_weight_jets hρ hK m
  let C (j : ℕ) := 2 * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * G
  have hC (j : ℕ) : 0 ≤ C j := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hA))
        (zero_le_one.trans hG))
  let H := max 1 (∑ j ∈ Finset.range (m + 1), C j)
  have hH (j : ℕ) (hj : j ≤ m) : C j ≤ H :=
    (Finset.single_le_sum (fun i _ => hC i) (by simpa using hj)).trans (le_max_right _ _)
  refine ⟨H, le_max_left _ _, ?_⟩
  intro j hj R U hU f hf hinv hisom q hheight x hx hxU
  let h := L.metric P E0 hS hSF hB hfull
  let θ := fun y => endCutoffWeight g0.cylindrical_end R (f y)
  have hθ : ContDiffOn ℝ ∞ θ U :=
    (endCutoffWeight_contDiff g0.cylindrical_end R).comp_contDiffOn
      (contMDiffOn_iff_contDiffOn.mp hf)
  have hcf : ContDiffOn ℝ ∞ (h.pullbackCoefficients f) U := fun y hy =>
    (h.contDiffAt_pullbackCoefficients (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hcg : ContDiffOn ℝ ∞ (g0.metric.pullbackCoefficients f) U := fun y hy =>
    (g0.metric.contDiffAt_pullbackCoefficients (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hθeq : θ =ᶠ[𝓝 x] fun y =>
      Real.smoothTransition (endExhaustion g0.cylindrical_end y + (q - R)) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    dsimp [θ, endCutoffWeight]
    rw [hheight y hy]
    congr 1
    ring
  have hcompeq : (fun y => 1 - θ y) =ᶠ[𝓝 x] fun y =>
      1 - Real.smoothTransition (endExhaustion g0.cylindrical_end y + (q - R)) :=
    hθeq.fun_comp (fun r : ℝ => 1 - r)
  have hzero : (L.closedFlow P E0 hS hSF hB hfull).metric 0 = g0.metric := by
    change L.closedMetric P E0 hS hSF hB hfull 0 = _
    rw [L.closedMetric_of_lt P E0 hS hSF hB hfull hS, F.initial_metric]
  have hterminal : (L.closedFlow P E0 hS hSF hB hfull).metric S = h :=
    L.closedMetric_terminal P E0 hS hSF hB hfull
  have hfg (k : ℕ) (hk : k ≤ j) : ‖iteratedFDeriv ℝ k (h.pullbackCoefficients f) x‖ ≤ G := by
    rw [← hterminal]
    exact hmetric k (hk.trans hj) hU hf hinv hisom S ⟨hS.le, le_rfl⟩ x hx hxU
  have hgg (k : ℕ) (hk : k ≤ j) :
      ‖iteratedFDeriv ℝ k (g0.metric.pullbackCoefficients f) x‖ ≤ G := by
    rw [← hzero]
    exact hmetric k (hk.trans hj) hU hf hinv hisom 0 ⟨le_rfl, hS.le⟩ x hx hxU
  have hbound := norm_iteratedFDeriv_blend_le_of_local_bounds hU hθ hcf hcg hxU j
    (zero_le_one.trans hA)
    (fun k hk => by
      rw [(hθeq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
      exact (hweights k (hk.trans hj) (q - R) x hx).1)
    (fun k hk => by
      rw [(hcompeq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
      exact (hweights k (hk.trans hj) (q - R) x hx).2) hfg hgg
  have heq : (cutoffMetric g0.cylindrical_end h R).pullbackCoefficients f =
      fun y => (1 - θ y) • h.pullbackCoefficients f y +
        θ y • g0.metric.pullbackCoefficients f y :=
    funext (cutoffMetric_pullbackCoefficients g0.cylindrical_end h R f)
  rw [heq]
  exact hbound.trans (hH j hj)




theorem cutoffMetric_curvatureDerivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ,
      ∀ D : LeviCivitaData (cutoffMetric g0.cylindrical_end
        (L.metric P E0 hS hSF hB hfull) R),
      ∀ x : StandardCapSpace, D.curvatureDerivativeNorm m x ≤ C := by
  let e := g0.cylindrical_end
  let K := endTruncatedCore e 3 ∪ endReferenceSection e
  have hK : IsCompact K :=
    (endTruncatedCore_isCompact e (by norm_num : (0 : ℝ) ≤ 3)).union
      (endReferenceSection_isCompact e)
  obtain ⟨a, ha, hell⟩ := L.cutoffMetric_compactPullback_ellipticity P E0 hS hSF hB hfull hK
  obtain ⟨G, _hG, hjets⟩ :=
    L.cutoffMetric_compactPullback_spatialJet_bounds P E0 hS hSF hB hfull hK (2 + m)
  obtain ⟨C, hC, hbound⟩ := curvatureDerivativeNorm_bound_of_pullback_jets 3 m ha G
  refine ⟨C, hC, fun R D x => ?_⟩
  by_cases hx : x ∈ endTruncatedCore e 3
  · have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (id : StandardCapSpace → StandardCapSpace) univ :=
      contMDiff_id.contMDiffOn
    have hi (y : StandardCapSpace) (_hy : y ∈ (univ : Set StandardCapSpace)) :
        (mfderiv (𝓡 3) (𝓡 3) (id : StandardCapSpace → StandardCapSpace) y).IsInvertible := by
      rw [mfderiv_id]
      exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    have hm (y : StandardCapSpace) (_hy : y ∈ (univ : Set StandardCapSpace))
        (u v : TangentSpace (𝓡 3) y) : g0.metric.inner y u v =
        g0.metric.inner (id y) (mfderiv (𝓡 3) (𝓡 3) id y u)
          (mfderiv (𝓡 3) (𝓡 3) id y v) := by
      rw [mfderiv_id]
      rfl
    apply hbound D isOpen_univ he hi (mem_univ x)
    · intro j hj
      exact hjets j hj R isOpen_univ he hi hm 0 (fun y _ => by simp)
        x (Or.inl hx) (mem_univ x)
    · exact hell R x (Or.inl hx) id (hm x (mem_univ x))
  · have htail : x ∈ e.coordinate '' (univ ×ˢ Ioi (3 : ℝ)) := not_not.mp hx
    obtain ⟨z, hz, rfl⟩ := htail
    obtain ⟨y, hy, hyeq⟩ := endTranslation_covers_tail e z
    have hyU := endReferenceSection_subset_region e hy
    have he := endTranslation_contMDiffOn e hz.2.le
    have hi := fun y hy => endTranslation_mfderiv_isInvertible e hz.2.le (x := y) hy
    have hm := fun y hy u v => endTranslation_metric e hz.2.le (x := y) hy u v
    have hh (y : StandardCapSpace) (hy : y ∈ endReferenceRegion e) :
        endExhaustion e (endAxialTranslation e (z.2 - 4) y) =
          endExhaustion e y + (z.2 - 4) := by
      linarith [endExhaustion_translation_eq e hz.2.le hy]
    rw [← hyeq]
    apply hbound D (endReferenceRegion_isOpen e) he hi hyU
    · intro j hj
      exact hjets j hj R (endReferenceRegion_isOpen e) he hi hm (z.2 - 4) hh
        y (Or.inr hy) hyU
    · exact hell R y (Or.inr hy) _ (hm y hyU)

end PoincareConjecture.M34.PartialFlowTerminalJets
