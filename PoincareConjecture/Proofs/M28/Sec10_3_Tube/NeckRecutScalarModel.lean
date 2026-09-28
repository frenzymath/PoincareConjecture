import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderMiddleModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderTailModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.M28.Generalized.NeckCoverEnd
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_neck_recut_scalar_model_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (K : NeckOnlyCover g),
        K.epsilon ≤ epsilon0 → (∀ N ∈ K.necks, N.connection = D) →
        g.volumeMeasure univ ≠ ⊤ →
        ∀ (U : Set M) (A : OpenCylinderModel U) (W : Set M),
          W = A.tail true (1 / 2) → IsOpen W → IsCompact (frontier W) →
          W ⊆ K.X → closure W ⊆ U →
          ∃ Z : OpenCylinderModel W,
            (∃ B : ℝ, ∀ x ∈ Z.tail false (1 / 2), D.scalarCurvature x ≤ B) ∧
            (∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
              ∀ x ∈ Z.tail true a, B < D.scalarCurvature x) ∧
            ∀ x ∈ Z.tail true (1 / 2),
              ∃ N ∈ K.necks, N.center = x ∧ N.connection = D ∧ N.carrier ⊆ W := by
  obtain ⟨epsilon0, hpos, hsmall, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ instT3 g D K hepsilon hD hfinite U A W hWA hWo hfront hWK hclosure
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ instT3)
  have hWU : W ⊆ U := hWA.symm ▸ A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hheight : Continuous (fun x : U => (A.inverse x).2) := continuous_snd.comp
    (A.inverse_smooth.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property))
  have hside (x : U) (hx : (1 / 2 : ℝ) < (A.inverse x).2) : x.val ∈ W := by
    rw [hWA]
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr ⟨x.property, hx⟩
  have hdiverge := scalar_diverges_on_proper_neck_cover_end K D hD hfinite
    (fun x : U => (A.inverse x).2) hheight
    (fun x => (A.inverse_mem x x.property).2.2) hWK hclosure hside
  obtain ⟨B0, hB0⟩ := hfront.bddAbove_image D.continuous_scalarCurvature.continuousOn
  obtain ⟨d, hd, hd1, hhigh⟩ := hdiverge (2 * B0)
  let alpha : ℝ := 2 * d - 1
  have halpha : alpha ∈ Ioo (0 : ℝ) 1 := by
    dsimp [alpha]
    constructor <;> linarith
  have hR := A.exists_positive_tail_model (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  rw [← hWA] at hR
  obtain ⟨R, _hcR, hvR⟩ := hR
  obtain ⟨Z, _hcZ, hvZ, hhalf⟩ := R.exists_midlevel_model halpha
  have hread (x : M) : (R.inverse x).2 = 2 * (A.inverse x).2 - 1 := by
    rw [hvR]
    dsimp
    ring
  refine ⟨Z, ?_, ?_, ?_⟩
  · have hupper : (1 + alpha) / 2 < 1 := by linarith [halpha.2]
    obtain ⟨B, hB⟩ := (A.isCompact_compactSlab
      (by norm_num : (0 : ℝ) < 1 / 2) hupper).bddAbove_image
        D.continuous_scalarCurvature.continuousOn
    refine ⟨B, ?_⟩
    intro x hx
    have hxZ := (Z.mem_tail_iff_m28 false (by norm_num) (by norm_num)).mp hx
    have hlow := (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mp (hWA ▸ hxZ.1)
    have hRle : (R.inverse x).2 ≤ alpha := by
      by_contra! hnot
      have hh := (hhalf x hxZ.1).mpr hnot
      exact (not_lt_of_ge hh.le) hxZ.2
    have hslab : x ∈ A.compactSlab (1 / 2) ((1 + alpha) / 2) := by
      apply (A.mem_compactSlab_iff (by norm_num) hupper).mpr
      refine ⟨hWU hxZ.1, hlow.2.le, ?_⟩
      rw [hread] at hRle
      linarith
    exact hB (mem_image_of_mem D.scalarCurvature hslab)
  · intro B
    obtain ⟨e, he, he1, hB⟩ := hdiverge B
    have ht : 2 * e - 1 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
    have hbeta : 1 - alpha ∈ Ioo (0 : ℝ) 1 :=
      ⟨sub_pos.mpr halpha.2, by linarith [halpha.1]⟩
    let c := Poincare.unitIntervalReparam (1 - alpha) (2 * e - 1)
    have hc : c ∈ Ioo (0 : ℝ) 1 :=
      (Poincare.unitIntervalReparam_properties hbeta).2.1 ht
    refine ⟨c, hc, ?_⟩
    intro x hx
    have hxZ := (Z.mem_tail_iff_m28 true hc.1 hc.2).mp hx
    have hheightZ : Poincare.unitIntervalReparam (1 - alpha) (2 * e - 1) <
        Poincare.unitIntervalReparam (1 - alpha) (R.inverse x).2 := by
      simpa only [hvZ, if_true, c] using hxZ.2
    have hh := ((Poincare.unitIntervalReparam_strictMonoOn hbeta).lt_iff_lt
      ht (R.inverse_mem x hxZ.1).2).mp hheightZ
    apply hB ⟨x, hWU hxZ.1⟩
    rw [hread] at hh
    linarith
  · intro x hx
    have hxZ := (Z.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mp hx
    have hRhigh := (hhalf x hxZ.1).mp hxZ.2
    have hAhigh : d < (A.inverse x).2 := by
      rw [hread] at hRhigh
      dsimp [alpha] at hRhigh
      linarith
    have hxhigh := hhigh ⟨x, hWU hxZ.1⟩ hAhigh
    obtain ⟨N, hN, hcenter⟩ := K.pointwise_center_cover x (hWK hxZ.1)
    have hepsN : N.epsilon ≤ epsilon0 := (K.neck_epsilon N hN).trans_le hepsilon
    have hNc : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
    have hdisj : Disjoint (frontier W) N.carrier := by
      apply disjoint_left.mpr
      intro y hyfront hyN
      have hybound := hB0 (mem_image_of_mem D.scalarCurvature hyfront)
      have hcompare := hratio M g D N hepsN N.center hNc y hyN
      rw [hcenter] at hcompare
      linarith
    have hsub : N.carrier ⊆ W := by
      let : ConnectedSpace N.carrier := Subtype.connectedSpace N.isConnected_carrier
      have hclopen : IsClopen ((Subtype.val : N.carrier → M) ⁻¹' W) :=
        isClopen_preimage_val hWo hdisj
      have hfull := hclopen.eq_univ ⟨⟨N.center, hNc⟩, hcenter.symm ▸ hxZ.1⟩
      intro y hy
      have hh : (⟨y, hy⟩ : N.carrier) ∈ (univ : Set N.carrier) := mem_univ _
      rw [← hfull] at hh
      exact hh
    exact ⟨N, hN, hcenter, hD N hN, hsub⟩

end PoincareConjecture.M28
