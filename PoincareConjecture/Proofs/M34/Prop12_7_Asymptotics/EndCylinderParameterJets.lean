import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderParameterBounds
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderJets
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy Poincare.Analysis.Calculus

variable {g : RiemannianMetric 3 StandardCapSpace}

noncomputable def endCylinderParameterDifference (e : StandardCylindricalEnd g)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (j : ℕ) (t : ℝ)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
  (F.metric t).parametrizedCoefficients
      (endAxialTranslation e j ∘ endSphereCylinderMap e q) p -
    evolvingRoundCylinderModelCoefficients t p

theorem endCylinderParameterDifference_eq_pullback (e : StandardCylindricalEnd g)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (j : ℕ) (t : ℝ)
    (q : UnitTwoSphere) {p : RoundCylinderCoordinates} (hp : 2 < p.2) :
    endCylinderParameterDifference e F j t q p =
      (endCylinderDifferenceCoefficients e F j t (endSphereCylinderMap e q p)).bilinearComp
        (fderiv ℝ (endSphereCylinderMap e q) p)
        (fderiv ℝ (endSphereCylinderMap e q) p) := by
  have hp0 : 0 < p.2 := lt_trans (by norm_num : (0 : ℝ) < 2) hp
  have hj : 0 < p.2 + (j : ℝ) := add_pos_of_pos_of_nonneg hp0 (Nat.cast_nonneg j)
  have hf := (endSphereCylinderMap_contMDiffAt e q hp0).mdifferentiableAt (by simp)
  have hτ₀ := endAxialTranslation_contMDiffAt e (j : ℝ)
    (z := ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) hp0 hj
  have hτ := hτ₀.mdifferentiableAt (by simp)
  have hd := mfderiv_comp p hτ hf
  have hm (v w : RoundCylinderCoordinates) :=
    endCylinderCoefficients_endSphereCylinderMap e t q hp v w
  have heq (v w : RoundCylinderCoordinates) :
      endCylinderParameterDifference e F j t q p v w =
        endCylinderDifferenceCoefficients e F j t (endSphereCylinderMap e q p)
          (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p v)
          (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p w) := by
    simp only [endCylinderParameterDifference, sub_apply,
      RiemannianMetric.parametrizedCoefficients_apply]
    rw [hd]
    change _ = (F.metric t).pullbackCoefficients (endAxialTranslation e j)
        (endSphereCylinderMap e q p)
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p v)
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p w) -
      endCylinderCoefficients e t (endSphereCylinderMap e q p)
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p v)
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p w)
    exact congrArg (fun z => (F.metric t).pullbackCoefficients (endAxialTranslation e j)
      (endSphereCylinderMap e q p)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p w) - z)
      (hm v w).symm
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have h := heq v w
  simp only [mfderiv_eq_fderiv] at h
  convert! h using 1

theorem endCylinderParameterDifference_jet_eq (e : StandardCylindricalEnd g)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (j : ℕ) (t : ℝ)
    (q : UnitTwoSphere) {p : RoundCylinderCoordinates} (hp : 2 < p.2) (m : ℕ) :
    iteratedFDeriv ℝ m (endCylinderParameterDifference e F j t q) p =
      iteratedFDeriv ℝ m (fun y =>
        (endCylinderDifferenceCoefficients e F j t (endSphereCylinderMap e q y)).bilinearComp
          (fderiv ℝ (endSphereCylinderMap e q) y)
          (fderiv ℝ (endSphereCylinderMap e q) y)) p := by
  have heq : endCylinderParameterDifference e F j t q =ᶠ[𝓝 p] fun y =>
      (endCylinderDifferenceCoefficients e F j t (endSphereCylinderMap e q y)).bilinearComp
        (fderiv ℝ (endSphereCylinderMap e q) y) (fderiv ℝ (endSphereCylinderMap e q) y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with y hy
    exact endCylinderParameterDifference_eq_pullback e F j t q hy
  exact (heq.iteratedFDeriv ℝ m).self_of_nhds

theorem partialFlow_endCylinderParameterDifference_iteratedFDeriv_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    (e : StandardCylindricalEnd g0.metric)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (p₀ : endReferenceRegion e)
    {T : ℝ} (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc 0 T, ∀ q : UnitTwoSphere,
      ∀ r ∈ Icc (17 / 5 : ℝ) (23 / 5),
        ‖iteratedFDeriv ℝ m (endCylinderParameterDifference e F.flow (k + 1) t q) (0, r)‖ <
          ε := by
  classical
  choose D hDb using fun j : Fin (m + 2) => endSphereCylinderMap_uniform_jet_bound e j
  let D₀ : ℝ := 1 + ∑ j : Fin (m + 2), max (D j) 0
  have hD₀ : 1 ≤ D₀ := le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => le_max_right _ _)
  have hmapjet (j : ℕ) (hj : j ≤ m + 1) (q : UnitTwoSphere) (r : ℝ)
      (hr : r ∈ Icc (17 / 5 : ℝ) (23 / 5)) :
      ‖iteratedFDeriv ℝ j (endSphereCylinderMap e q) (0, r)‖ ≤ D₀ := by
    let i : Fin (m + 2) := ⟨j, by omega⟩
    have hle : max (D i) 0 ≤ ∑ l : Fin (m + 2), max (D l) 0 :=
      Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
    exact (hDb i q r hr).trans ((le_max_left _ _).trans (hle.trans (by dsimp [D₀]; linarith)))
  obtain ⟨C, hC, hbound⟩ := exists_bilinear_pullback_jet_bound
    (E := RoundCylinderCoordinates) (F := StandardCapSpace) (G := ℝ) m hD₀
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  choose N hN using fun j : Fin (m + 1) =>
    partialFlow_endCylinderDifferenceCoefficients_iteratedFDeriv_tendsto
      P E0 F e qH qA qS p₀ hT j hδ
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk t ht q r hr
  have hx : endSphereCylinderMap e q (0, r) ∈ endClosedSlab e (17 / 5) (23 / 5) :=
    ⟨((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0, r), ⟨mem_univ _, hr⟩, rfl⟩
  have hxU := endClosedSlab_subset_reference e (by norm_num : (3 : ℝ) < 17 / 5)
    (by norm_num : (23 / 5 : ℝ) < 5) hx
  have hf : ContDiffAt ℝ ∞ (endSphereCylinderMap e q) (0, r) :=
    contMDiffAt_iff_contDiffAt.mp (endSphereCylinderMap_contMDiffAt e q
      (by change 0 < r; linarith [hr.1]))
  have hB := (endCylinderDifferenceCoefficients_contDiffOn e F.flow (k + 1) t).contDiffAt
    ((endReferenceRegion_isOpen e).mem_nhds hxU)
  have hb := hbound (endSphereCylinderMap e q)
    (endCylinderDifferenceCoefficients e F.flow (k + 1) t) (0, r) hf hB
    (fun j hj => hmapjet j hj q r hr) δ hδ.le (fun j hj => ?_)
  · rw [endCylinderParameterDifference_jet_eq e F.flow (k + 1) t q
      (by change 2 < r; linarith [hr.1]) m]
    calc
      _ ≤ C * δ := hb
      _ < (C + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one C) hδ
      _ = ε := by dsimp [δ]; field_simp
  · let i : Fin (m + 1) := ⟨j, by omega⟩
    exact (hN i k ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hk) t ht _ hx).le

end PoincareConjecture.M34
