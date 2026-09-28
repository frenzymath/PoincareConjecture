import PoincareConjecture.Proofs.M47.LimitCanonicalFamilyCoefficientJets
import PoincareConjecture.Proofs.M47.LimitCanonicalNeckChartJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

universe u

namespace PoincareConjecture.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private noncomputable def familyNeckCoefficientEvaluation (i l : Fin 3) :
    (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ l)).comp
    (ContinuousLinearMap.apply ℝ (E₃ →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ i))

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E₃ G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space

private theorem family_coefficient_difference_fixed_chart
    (k : ℕ) (N : EpsilonNeck (G.limit.flow.metric 0)) (q : UnitTwoSphere)
    (z : ℝ) (a : G.limit.sliceCarrier.carrier) {s : ℝ}
    (hs : s ∈ Icc (-G.exhaustion.time k) 0) {x : E₃}
    (hx : x 2 + z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (ha : N.capPersistenceEuclideanMap q z x ∈ (extChartAt (𝓡 3) a).source)
    (i l : Fin 3) :
    let phi := N.capPersistenceEuclideanMap q z
    let f := (extChartAt (𝓡 3) a) ∘ phi
    roundCylinderTensorCoefficient
        (generalizedCylinderPullback (G.embedding k) N.coordinate_map s)
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, z)) i l -
      roundCylinderTensorCoefficient
        (roundCylinderPullback (G.limit.flow.metric s) N.coordinate_map)
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, z)) i l =
      ((blowupCoordinateBilinear (G.embedding k) a s (f x) -
          limitCoordinateBilinear G.limit a s (f x)).bilinearComp
        (fderiv ℝ f x) (fderiv ℝ f x))
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ l) := by
  dsimp only
  have hphi := (N.capPersistenceEuclideanMap_contMDiffAt q z hx).mdifferentiableAt (by simp)
  have hb := blowupCoordinateBilinear_pullback_apply (G.embedding k) a hs hphi ha
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ l)
  have hl := limitCoordinateBilinear_pullback_apply a s hphi ha
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ l)
  have hsource := N.capPersistence_tensor_coefficient ((G.embedding k).pullbackInner s hs)
    q z hx i l
  have hlimit := N.capPersistence_tensor_coefficient
    (fun y v w => (G.limit.flow.metric s).inner y v w) q z hx i l
  have hread := congrArg₂ (fun v w : ℝ => v - w) hb hl
  simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply] at hread ⊢
  simp only [generalizedCylinderPullback, dif_pos hs]
  exact (congrArg₂ (fun v w : ℝ => v - w) hsource hlimit).trans hread.symm



theorem limitCanonical_eventually_chart_neck_family_jets
    (P : M47Predecessors.{u}) (N : EpsilonNeck (G.limit.flow.metric 0))
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKJ : Ktime ⊆ J)
    (a : G.limit.sliceCarrier.carrier) {H : Set E₃} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) a).target) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ k in atTop, Ktime ⊆ Icc (-G.exhaustion.time k) 0 ∧
      ∀ s ∈ Ktime, ∀ (q : UnitTwoSphere) (z : ℝ),
        z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        N.coordinate_map (q, z) ∈ (extChartAt (𝓡 3) a).source →
        (extChartAt (𝓡 3) a) (N.coordinate_map (q, z)) ∈ H →
        ∀ j ≤ m, ∀ i l : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
                (generalizedCylinderPullback (G.embedding k) N.coordinate_map s)
                (chartAt E₂ q) y i l -
              roundCylinderTensorCoefficient
                (roundCylinderPullback (G.limit.flow.metric s) N.coordinate_map)
                (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  classical
  let c := extChartAt (𝓡 3) a
  obtain ⟨D, hD, hDbound⟩ := Proofs.M47.neck_chart_map_jets_at_recorded_order
    N m hm a hH hHt
  choose B hB hbound using fun j : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound (E := E₃) (F := E₃) (G := ℝ) j hD
  let B0 : ℝ := ∑ j : Fin (m + 1), B j
  let E0 : ℝ := ∑ il : Fin 3 × Fin 3, ‖familyNeckCoefficientEvaluation il.1 il.2‖
  let L0 : ℝ := max 1 ‖capPersistenceEuclideanCoordinates‖
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun j _ => hB j
  have hE0 : 0 ≤ E0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL0 : 1 ≤ L0 := le_max_left _ _
  let A0 := E0 * B0 * L0 ^ m
  have hA0 : 0 ≤ A0 := mul_nonneg (mul_nonneg hE0 hB0)
    (pow_nonneg (zero_le_one.trans hL0) _)
  let eta := rho / (A0 + 1)
  have heta : 0 < eta := div_pos hrho (by positivity)
  have hsmall : A0 * eta < rho := by
    have hh : (A0 + 1) * eta = rho := by dsimp only [eta]; field_simp
    nlinarith
  have htail : ∀ᶠ k in atTop, ∀ j : Fin (m + 1),
      Ktime ⊆ Icc (-G.exhaustion.time k) 0 ∧
      c.symm '' H ⊆ G.exhaustion.space k ∧
      ∀ s ∈ Ktime, ∀ x ∈ H,
        ContDiffAt ℝ ∞ (blowupCoordinateBilinear (G.embedding k) a s) x ∧
        ContDiffAt ℝ ∞ (limitCoordinateBilinear G.limit a s) x ∧
        ‖iteratedFDeriv ℝ (j : ℕ) (blowupCoordinateBilinear (G.embedding k) a s) x -
          iteratedFDeriv ℝ (j : ℕ) (limitCoordinateBilinear G.limit a s) x‖ < eta := by
    apply Filter.eventually_all.mpr
    intro j
    exact limitCanonical_eventually_family_bilinear_jets G P a j hKtime hKJ hH hHt heta
  filter_upwards [htail] with k hk
  have hk0 := hk ⟨0, Nat.succ_pos m⟩
  refine ⟨hk0.1, ?_⟩
  intro s hs q z hz hsource hcenter j hj i l
  let phi := N.capPersistenceEuclideanMap q z
  let f := c ∘ phi
  let T : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y =>
    blowupCoordinateBilinear (G.embedding k) a s y - limitCoordinateBilinear G.limit a s y
  have hphi0 : phi 0 = N.coordinate_map (q, z) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q z)
  have hf0 : f 0 = c (N.coordinate_map (q, z)) := congrArg c hphi0
  have hphi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ phi 0 :=
    N.capPersistenceEuclideanMap_contMDiffAt q z (by simpa using hz)
  have hchart : phi 0 ∈ c.source := by rw [hphi0]; exact hsource
  have hf : ContDiffAt ℝ ∞ f 0 := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_extChartAt (I := 𝓡 3) (x := a) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source a).mem_nhds hchart)).comp 0 hphi)
  have hBk : ContDiffAt ℝ ∞ (blowupCoordinateBilinear (G.embedding k) a s) (f 0) :=
    (hk0.2.2 s hs _ (hf0.symm ▸ hcenter)).1
  have hBlimit : ContDiffAt ℝ ∞ (limitCoordinateBilinear G.limit a s) (f 0) :=
    (hk0.2.2 s hs _ (hf0.symm ▸ hcenter)).2.1
  have hT : ContDiffAt ℝ ∞ T (f 0) := hBk.sub hBlimit
  have hTjet (r : ℕ) (hr : r ≤ j) : ‖iteratedFDeriv ℝ r T (f 0)‖ ≤ eta := by
    change ‖iteratedFDeriv ℝ r (fun y =>
      blowupCoordinateBilinear (G.embedding k) a s y -
        limitCoordinateBilinear G.limit a s y) (f 0)‖ ≤ eta
    rw [fun_iteratedFDeriv_sub_apply (hBk.of_le (by exact_mod_cast le_top))
      (hBlimit.of_le (by exact_mod_cast le_top)), hf0]
    exact ((hk ⟨r, by omega⟩).2.2 s hs _ hcenter).2.2.le
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let A := fun x => (T (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)
  have hA : ContDiffAt ℝ ∞ A 0 := hf.bilinearPullback hT
  have hAjet : ‖iteratedFDeriv ℝ j A 0‖ ≤ B j' * eta :=
    hbound j' f T 0 hf hT (fun r hr => hDbound q z hz hsource hcenter r (by omega))
      eta heta.le hTjet
  let F0 : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderTensorCoefficient
        (generalizedCylinderPullback (G.embedding k) N.coordinate_map s)
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient
        (roundCylinderPullback (G.limit.flow.metric s) N.coordinate_map)
        (chartAt E₂ q) y i l
  have heq : (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z)))
      =ᶠ[𝓝 (0 : E₃)] (familyNeckCoefficientEvaluation i l) ∘ A := by
    have hnear := hphi.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source a).mem_nhds hchart)
    have haxis : ∀ᶠ x : E₃ in 𝓝 0, x 2 + z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      have hc : ContinuousAt (fun x : E₃ => x 2 + z) 0 :=
        ((EuclideanSpace.proj 2 : E₃ →L[ℝ] ℝ).continuous.add continuous_const).continuousAt
      exact hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa using hz))
    filter_upwards [hnear, haxis] with x hx hxaxis
    exact family_coefficient_difference_fixed_chart G k N q z a (hk0.1 hs) hxaxis hx i l
  have hscalar := (familyNeckCoefficientEvaluation i l).contDiff.contDiffAt.comp 0 hA
  have hFE := hscalar.congr_of_eventuallyEq heq
  have hE : ‖familyNeckCoefficientEvaluation i l‖ ≤ E0 :=
    Finset.single_le_sum (fun il _ => norm_nonneg (familyNeckCoefficientEvaluation il.1 il.2))
      (Finset.mem_univ (i, l))
  have hFjet : ‖iteratedFDeriv ℝ j
      (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ ≤
        E0 * B0 * eta := by
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    calc
      _ ≤ ‖familyNeckCoefficientEvaluation i l‖ * ‖iteratedFDeriv ℝ j A 0‖ :=
        (familyNeckCoefficientEvaluation i l).norm_iteratedFDeriv_comp_left hA
          (by exact_mod_cast le_top)
      _ ≤ E0 * (B j' * eta) := mul_le_mul hE hAjet (norm_nonneg _) hE0
      _ ≤ E0 * (B0 * eta) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun r _ => hB r) (Finset.mem_univ j')) heta.le) hE0
      _ = _ := by ring
  have hlin : ‖capPersistenceEuclideanCoordinates‖ ^ j ≤ L0 ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hL0 hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j
        (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ *
          ‖capPersistenceEuclideanCoordinates‖ ^ j :=
      capPersistence_product_jet_le_euclidean F0 z j
        (hFE.of_le (by exact_mod_cast le_top))
    _ ≤ (E0 * B0 * eta) * L0 ^ m :=
      mul_le_mul hFjet hlin (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = A0 * eta := by dsimp only [A0]; ring
    _ < rho := hsmall

end PoincareConjecture.M47
