import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparationLabels
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparatingTube











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M28





theorem exists_separating_cover_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] {g : RiemannianMetric 3 M},
        ∀ (H : NeckOnlyCover g) (L : EpsilonNeck g),
          H.epsilon ≤ epsilon0 → L.epsilon ≤ epsilon0 →
          L.IsSeparating → L.center ∈ closure H.X →
          ∀ N ∈ H.necks, N.center ∈ H.X → N.IsSeparating := by
  obtain ⟨epsilonL, hLpos, hLcap, hlabel⟩ :=
    NeckOnlyCover.exists_locally_constant_separation_label.{u}
  obtain ⟨epsilonA, hApos, _, hagree⟩ :=
    EpsilonNeck.exists_near_center_separation_agreement.{u}
  refine ⟨min epsilonL epsilonA, lt_min hLpos hApos,
    (min_le_left _ _).trans hLcap, ?_⟩
  intro M _ _ _ _ _ instT3 g H L hH hL hsep hclosure
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ instT3)
  obtain ⟨label, hlabel⟩ := hlabel H (hH.trans (min_le_left _ _))
  have hmiddle : L.center ∈ L.region (-(1 : ℝ) / 2) (1 / 2) := by
    obtain ⟨hc, hz⟩ := (L.mem_central_sphere_iff L.center).mp L.center_on_central_sphere
    refine ⟨hc, ?_⟩
    rw [hz]
    norm_num
  obtain ⟨x, hxmiddle, hx⟩ := mem_closure_iff.mp hclosure
    (L.region (-(1 : ℝ) / 2) (1 / 2)) (L.isOpen_region _ _) hmiddle
  obtain ⟨N0, hN0, hcenter⟩ := H.pointwise_center_cover x hx
  have hN0small : N0.epsilon ≤ epsilonA := by
    rw [H.neck_epsilon N0 hN0]
    exact hH.trans (min_le_right _ _)
  have hnear : N0.center ∈ L.region (-(1 : ℝ) / 2) (1 / 2) := by
    rw [hcenter]
    exact hxmiddle
  have hN0sep : N0.IsSeparating :=
    (hagree L N0 (hL.trans (min_le_right _ _)) hN0small hnear).mp hsep
  have hx0 : N0.center ∈ H.X := hcenter.symm ▸ hx
  have htrue := (hlabel N0 hN0 hx0).mpr hN0sep
  let : PreconnectedSpace H.X := Subtype.preconnectedSpace H.connected_X.isPreconnected
  intro N hN hxN
  apply (hlabel N hN hxN).mp
  exact (label.apply_eq_of_preconnectedSpace ⟨N.center, hxN⟩ ⟨N0.center, hx0⟩).trans htrue





theorem exists_limit_cover_tube_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] {g : RiemannianMetric 3 M},
        ∀ (H : NeckOnlyCover g) (L : EpsilonNeck g),
          H.epsilon ≤ epsilon0 → L.epsilon ≤ epsilon0 →
          L.IsSeparating → L.center ∈ closure H.X →
          (∀ N ∈ H.necks, N.center ∈ H.X) →
          ∃ hsep : ∀ N ∈ H.necks, N.IsSeparating, AppendixA19Theory g H hsep := by
  obtain ⟨epsilonS, hSpos, hScap, hseparate⟩ := exists_separating_cover_accuracy.{u}
  obtain ⟨epsilonT, hTpos, _, htube⟩ :=
    NeckOnlyCover.exists_correctedA19Conclusion_of_separating.{u}
  refine ⟨min epsilonS epsilonT, lt_min hSpos hTpos,
    (min_le_left _ _).trans hScap, ?_⟩
  intro M _ _ _ _ _ _ g H L hH hL hsep hclosure hcenters
  have hall : ∀ N ∈ H.necks, N.IsSeparating := fun N hN =>
    hseparate H L (hH.trans (min_le_left _ _)) (hL.trans (min_le_left _ _))
      hsep hclosure N hN (hcenters N hN)
  exact ⟨hall, htube H (hH.trans (min_le_right _ _)) hall⟩

end PoincareConjecture.M28
