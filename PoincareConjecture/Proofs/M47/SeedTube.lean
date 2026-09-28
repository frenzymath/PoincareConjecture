import PoincareConjecture.Proofs.M47.SeedVolume
import PoincareConjecture.Proofs.M47.PrefixMonotone
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CanonicalBall











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47



theorem not_positive_of_mem_component
    {F : SurgeryFlowData.{u}} {t : ℝ} {x y : (F.slice t).carrier}
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hy : y ∈ connectedComponent x) :
    ¬ SurgeryPositiveComponentAt F t y := by
  intro hpos
  apply hpositive
  intro z hz
  exact hpos z (by simpa only [connectedComponent_eq hy] using hz)



theorem seed_tube_radius_pos
    (S : RepairedControlledSchedulesData.{u}) {H B : ℝ}
    (hH : 0 < H) (hB : M46.seedAnalyticConstant S ≤ B) :
    0 < (Real.sqrt H)⁻¹ / (8 * B) :=
  div_pos (inv_pos.mpr (Real.sqrt_pos.mpr hH))
    (mul_pos (by norm_num) ((M46.seedAnalyticConstant_pos S).trans_le hB))



theorem seed_ball_scalar_bound
    (S : RepairedControlledSchedulesData.{u}) (F : SurgeryFlowData.{u})
    (t : ℝ) {rho H B : ℝ} (hH : 0 < H)
    (hlevel : rho⁻¹ ^ 2 ≤ H) (hB : M46.seedAnalyticConstant S ≤ B)
    (hcanonical : ∀ y : (F.slice t).carrier,
      rho⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y →
        SurgeryCanonicalControl F t y F.parameters.epsilon S.setup.C)
    (x : (F.slice t).carrier)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hcenter : (F.connection t).scalarCurvature x ≤ H) :
    ∀ y ∈ (F.metric t).ball x ((Real.sqrt H)⁻¹ / (8 * B)),
      (F.connection t).scalarCurvature y ≤ 2 * H := by
  have hr : 0 < (Real.sqrt H)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hH)
  have hsq : ((Real.sqrt H)⁻¹)⁻¹ ^ 2 = H := by
    rw [inv_inv, Real.sq_sqrt hH.le]
  have h := M46.canonical_scalar_le_two_inv_sq_on_ball S F t x hB hr hpositive
    (by simpa only [hsq] using hcenter)
    (fun y _ hy => hcanonical y (hlevel.trans (by simpa only [hsq] using hy)))
  simpa only [hsq] using h



theorem seed_ball_curvature_bound (P : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (F : SurgeryFlowData.{u})
    (t : ℝ) {rho H B : ℝ} (hH : 0 < H)
    (hlevel : rho⁻¹ ^ 2 ≤ H) (hB : M46.seedAnalyticConstant S ≤ B)
    (hcanonical : ∀ y : (F.slice t).carrier,
      rho⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y →
        SurgeryCanonicalControl F t y F.parameters.epsilon S.setup.C)
    (hpinch : SurgeryPinchedAt (F.connection t) t)
    (x : (F.slice t).carrier)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hcenter : (F.connection t).scalarCurvature x ≤ H) :
    ∀ y ∈ (F.metric t).ball x ((Real.sqrt H)⁻¹ / (8 * B)),
      (F.connection t).curvatureTensorNorm y ≤ 13 * max (2 * H) (Real.exp 4) := by
  intro y hy
  have hscalar := seed_ball_scalar_bound S F t hH hlevel hB hcanonical
    x hpositive hcenter y hy
  exact (M46.pinched_curvature_norm_le P.toM46 hpinch (mem_univ y)).trans
    (mul_le_mul_of_nonneg_left (max_le_max_right _ hscalar) (by norm_num))



theorem seed_path_tube_bounds (P : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (F : SurgeryFlowData.{u})
    (t : ℝ) {rho H B : ℝ} (hH : 0 < H)
    (hlevel : rho⁻¹ ^ 2 ≤ H) (hB : M46.seedAnalyticConstant S ≤ B)
    (hcanonical : ∀ y : (F.slice t).carrier,
      rho⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y →
        SurgeryCanonicalControl F t y F.parameters.epsilon S.setup.C)
    (hpinch : SurgeryPinchedAt (F.connection t) t)
    (gamma : ℝ → (F.slice t).carrier) (hgamma : ContinuousOn gamma (Icc 0 1))
    (hpositive : ¬ SurgeryPositiveComponentAt F t (gamma 0))
    (hscalar : ∀ s ∈ Icc (0 : ℝ) 1, (F.connection t).scalarCurvature (gamma s) ≤ H) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ (F.metric t).ball (gamma s) ((Real.sqrt H)⁻¹ / (8 * B)),
        (F.connection t).scalarCurvature y ≤ 2 * H ∧
        (F.connection t).curvatureTensorNorm y ≤ 13 * max (2 * H) (Real.exp 4) := by
  intro s hs y hy
  have hcomponent : gamma s ∈ connectedComponent (gamma 0) :=
    (isPreconnected_Icc.image gamma hgamma).subset_connectedComponent
      ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ ⟨s, hs, rfl⟩
  have hnotpositive := not_positive_of_mem_component hpositive hcomponent
  exact ⟨seed_ball_scalar_bound S F t hH hlevel hB hcanonical
      (gamma s) hnotpositive (hscalar s hs) y hy,
    seed_ball_curvature_bound P S F t hH hlevel hB hcanonical hpinch
      (gamma s) hnotpositive (hscalar s hs) y hy⟩



theorem old_prefix_seed_canonical
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) {t : ℝ}
    (ht : t ∈ surgeryObservationInterval O ∩ prefixFinalInterval p)
    (y : (F.slice t).carrier)
    (hscalar : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y) :
    SurgeryCanonicalControl F t y F.parameters.epsilon S.setup.C := by
  have h := old.canonicalOn_prefixFinal (p.r_pos _) le_rfl t ht
    (O.interval_subset ht.1) y hscalar
  rw [old.C_eq, compatible.setup_eq] at h
  exact h

end PoincareConjecture.Proofs.M47
