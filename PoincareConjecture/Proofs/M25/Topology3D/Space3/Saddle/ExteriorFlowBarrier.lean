import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BoundedHeightTracks
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Set Filter
open scoped NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]




theorem boundedFlow_exterior_level_images
    (F : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K F) (hL : ∀ y, ‖F y‖ ≤ L)
    (H : E →L[ℝ] ℝ) (S C A U : Set E)
    (hA : IsClosed A) (hC : IsClosed C) (hU : IsOpen U)
    (hAS : A ⊆ S) (hSC : S \ C ⊆ A) (c delta : ℝ)
    (hflow : ∀ y ∈ S, ∀ t : ℝ, boundedFlow F hK hL y t ∈ S)
    (hunit : ∀ y ∈ S ∩ U, H (F y) = 1)
    (hsafe : ∀ y ∈ A \ C, |H y - c| ≤ 2 * delta → y ∈ U)
    (q : Fin 4 → ℝ → E)
    (hwall : ∀ t : ℝ, |t| ≤ 2 * delta →
      {y : E | y ∈ A ∩ C ∧ H y = c + t} = range (fun i : Fin 4 => q i t))
    (hqflow : ∀ i : Fin 4, ∀ s t : ℝ,
      |s| ≤ 2 * delta → |t| ≤ 2 * delta →
        boundedFlow F hK hL (q i s) (t - s) = q i t) :
    ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
      (fun y : E => boundedFlow F hK hL y (t - s)) ''
        {y : E | y ∈ A ∧ H y = c + s} = {y : E | y ∈ A ∧ H y = c + t} ∧
      (fun y : E => boundedFlow F hK hL y (-(t - s))) ''
        {y : E | y ∈ A ∧ H y = c + t} = {y : E | y ∈ A ∧ H y = c + s} := by
  have htrack (s t : ℝ) (hs : |s| ≤ 2 * delta) (ht : |t| ≤ 2 * delta)
      (y : E) (hy : y ∈ A ∧ H y = c + s) :
      boundedFlow F hK hL y (t - s) ∈ A ∧
        H (boundedFlow F hK hL y (t - s)) = c + t := by
    by_cases hyC : y ∈ C
    · obtain ⟨i, hi⟩ : y ∈ range (fun i : Fin 4 => q i s) := by
        rw [← hwall s hs]
        exact ⟨⟨hy.1, hyC⟩, hy.2⟩
      have hqt : q i t ∈ {z : E | z ∈ A ∩ C ∧ H z = c + t} := by
        rw [hwall t ht]
        exact mem_range_self i
      rw [← hi, hqflow i s t hs ht]
      exact ⟨hqt.1.1, hqt.2⟩
    · let I : Set ℝ := Icc (-(2 * delta)) (2 * delta)
      let : PreconnectedSpace I :=
        isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
      let gamma : ℝ → E := fun r => boundedFlow F hK hL y (r - s)
      have hfc : Continuous (boundedFlow F hK hL y) :=
        continuous_iff_continuousAt.mpr (fun r =>
          (boundedFlow_hasDerivAt F hK hL y r).continuousAt)
      have hgamma : Continuous gamma := hfc.comp (continuous_id.sub continuous_const)
      have hgammaS (r : ℝ) : gamma r ∈ S := hflow y (hAS hy.1) (r - s)
      let Good : Set I := {r | gamma (r : ℝ) ∈ A ∧ H (gamma (r : ℝ)) = c + (r : ℝ)}
      have hgc : Continuous (fun r : I => gamma (r : ℝ)) :=
        hgamma.comp continuous_subtype_val
      have hGoodClosed : IsClosed Good :=
        (hA.preimage hgc).inter (isClosed_eq (H.continuous.comp hgc)
          (continuous_const.add continuous_subtype_val))
      have hGoodNotC (r : I) (hr : r ∈ Good) : gamma (r : ℝ) ∉ C := by
        intro hrC
        have hrbound : |(r : ℝ)| ≤ 2 * delta := abs_le.mpr r.property
        obtain ⟨i, hi⟩ : gamma (r : ℝ) ∈ range (fun i : Fin 4 => q i (r : ℝ)) := by
          rw [← hwall (r : ℝ) hrbound]
          exact ⟨⟨hr.1, hrC⟩, hr.2⟩
        have his : q i s = y := by
          calc
            q i s = boundedFlow F hK hL (q i (r : ℝ)) (s - (r : ℝ)) :=
              (hqflow i (r : ℝ) s hrbound hs).symm
            _ = boundedFlow F hK hL (gamma (r : ℝ)) (s - (r : ℝ)) :=
              congrArg (fun z : E => boundedFlow F hK hL z (s - (r : ℝ))) hi
            _ = y := by
              change boundedFlow F hK hL
                (boundedFlow F hK hL y ((r : ℝ) - s)) (s - (r : ℝ)) = y
              simpa only [neg_sub] using boundedFlow_neg F hK hL y ((r : ℝ) - s)
        have hqs : q i s ∈ {z : E | z ∈ A ∩ C ∧ H z = c + s} := by
          rw [hwall s hs]
          exact mem_range_self i
        exact hyC (his ▸ hqs.1.2)
      have hGoodOpen : IsOpen Good := by
        apply isOpen_iff_mem_nhds.mpr
        intro r hr
        have hrbound : |(r : ℝ)| ≤ 2 * delta := abs_le.mpr r.property
        have hrheight : |H (gamma (r : ℝ)) - c| ≤ 2 * delta := by
          rw [hr.2, add_sub_cancel_left]
          exact hrbound
        have hrU : gamma (r : ℝ) ∈ U :=
          hsafe _ ⟨hr.1, hGoodNotC r hr⟩ hrheight
        have hsingle : {gamma (r : ℝ)} ⊆ S ∩ U := by
          intro z hz
          rw [mem_singleton_iff.mp hz]
          exact ⟨hgammaS _, hrU⟩
        obtain ⟨tau, htau, hlocal⟩ := exists_boundedFlow_unit_height_interval
          F hK hL H (S := S) (A := {gamma (r : ℝ)}) (U := U)
          isCompact_singleton hU hsingle hflow hunit
        have htime : ∀ᶠ z : I in 𝓝 r, |(z : ℝ) - (r : ℝ)| < tau := by
          have hc : Continuous (fun z : I => |(z : ℝ) - (r : ℝ)|) :=
            (continuous_subtype_val.sub continuous_const).abs
          exact hc.continuousAt.eventually (isOpen_Iio.mem_nhds (by simpa using htau))
        have havoid : ∀ᶠ z : I in 𝓝 r, gamma (z : ℝ) ∉ C :=
          hgc.continuousAt.eventually (hC.isOpen_compl.mem_nhds (hGoodNotC r hr))
        filter_upwards [htime, havoid] with z hztime hzC
        have hshift : boundedFlow F hK hL (gamma (r : ℝ)) ((z : ℝ) - (r : ℝ)) =
            gamma (z : ℝ) := by
          change boundedFlow F hK hL
            (boundedFlow F hK hL y ((r : ℝ) - s)) ((z : ℝ) - (r : ℝ)) =
              boundedFlow F hK hL y ((z : ℝ) - s)
          rw [← boundedFlow_add]
          congr 1
          ring
        have hheight := (hlocal (gamma (r : ℝ)) (mem_singleton _)
          ((z : ℝ) - (r : ℝ)) hztime.le).2
        rw [hshift, hr.2] at hheight
        exact ⟨hSC ⟨hgammaS _, hzC⟩, by linarith only [hheight]⟩
      have hnonempty : Good.Nonempty := by
        refine ⟨⟨s, abs_le.mp hs⟩, ?_⟩
        change boundedFlow F hK hL y (s - s) ∈ A ∧
          H (boundedFlow F hK hL y (s - s)) = c + s
        simpa only [sub_self, boundedFlow_zero] using hy
      have hGood : Good = univ :=
        (show IsClopen Good from ⟨hGoodClosed, hGoodOpen⟩).eq_univ hnonempty
      have htGood : (⟨t, abs_le.mp ht⟩ : I) ∈ Good := hGood.symm ▸ mem_univ _
      exact htGood
  have hforward (s t : ℝ) (hs : |s| ≤ 2 * delta) (ht : |t| ≤ 2 * delta) :
      (fun y : E => boundedFlow F hK hL y (t - s)) ''
        {y : E | y ∈ A ∧ H y = c + s} = {y : E | y ∈ A ∧ H y = c + t} := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact htrack s t hs ht z hz
    · intro y hy
      refine ⟨boundedFlow F hK hL y (s - t), htrack t s ht hs y hy, ?_⟩
      simpa only [neg_sub] using boundedFlow_neg F hK hL y (s - t)
  intro s t hs ht
  exact ⟨hforward s t hs ht, by simpa only [neg_sub] using hforward t s ht hs⟩

end PoincareConjecture.M25.Topology3D
