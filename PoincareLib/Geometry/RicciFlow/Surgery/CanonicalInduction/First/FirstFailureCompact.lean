import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.First.FirstFailure
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.EventNeighborhood
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Bounds.SlabScalarTransport
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences

/-!
# Lemma 17.2: a compact right-slab limit of bad points

Morgan--Tian Lemma 17.2, p. 396. The first-failure infimum has an ordinary
right slab. Its compact initial carrier contains a limit of pulled-back
bad points, and actual scalar continuity preserves the tested threshold.
The geometric proof that the limit itself is bad remains separate.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M47

/-- Counterexamples approaching the first-failure time have a high-scalar
limit in one actual ordinary right slab, Morgan--Tian Lemma 17.2, p. 396.
This extraction does not assert canonical failure at the limit point. -/
theorem exists_canonicalFailureSlabLimit (hC : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {T0 r : ℝ}
    (hT0 : 0 ≤ T0) (hold : SurgeryCanonicalOn F (Ico 0 T0) r)
    (hfail : ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r) :
    ∃ t ∈ Ico T0 O.H, SurgeryCanonicalOn F (Ico 0 t) r ∧
      ∃ (b : ℝ) (htb : t < b) (hJ : Icc t b ⊆ F.time_domain)
        (hfree : Disjoint F.surgery_times (Ioc t b)), b < O.H ∧
        let S := F.regular_slabs t b htb hJ hfree
        ∃ x : (F.slice t).carrier,
          r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
          ∃ times : ℕ → Icc t b, ∃ points : ℕ → (F.slice t).carrier,
            Antitone (fun n => (times n).val) ∧
            Tendsto (fun n => (times n).val) atTop (𝓝 t) ∧
            Tendsto points atTop (𝓝 x) ∧
            ∀ n, r⁻¹ ^ 2 ≤ (F.connection (times n).val).scalarCurvature
                (S.identify (times n) (points n)) ∧
              ¬ SurgeryCanonicalControl F (times n).val
                (S.identify (times n) (points n))
                F.parameters.epsilon F.parameters.C := by
  classical
  obtain ⟨t, ht, htF, hpast, q, hqanti, hqtendsto, hqbad⟩ :=
    exists_canonicalFailureInfimum hT0 hold hfail
  obtain ⟨b, htb, hbH, hfree⟩ := M44.exists_surgery_free_right_interval F htF ht.2
  have hJ : Icc t b ⊆ F.time_domain := by
    intro s hs
    exact O.interval_subset ⟨(hT0.trans ht.1).trans hs.1, hs.2.trans_lt hbH⟩
  let S := F.regular_slabs t b htb hJ hfree
  have hqge (n : ℕ) : t ≤ q n := hqanti.le_of_tendsto hqtendsto n
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hqtendsto.eventually (Iio_mem_nhds htb))
  let times : ℕ → Icc t b := fun n =>
    ⟨q (n + N), hqge _, (hN (n + N) (by omega)).le⟩
  have htimeanti : Antitone (fun n => (times n).val) := by
    intro m n hmn
    exact hqanti (Nat.add_le_add_right hmn N)
  have htimeconv : Tendsto (fun n => (times n).val) atTop (𝓝 t) :=
    hqtendsto.comp (tendsto_add_atTop_nat N)
  choose badPoints hscalar hbad using fun n => (hqbad (n + N)).2
  let pulled : ℕ → (F.slice t).carrier := fun n =>
    (S.identify (times n)).symm (badPoints n)
  obtain ⟨x, _, phi, hphi, hpulled⟩ :=
    (F.slices_compact t htF).tendsto_subseq (fun n => mem_univ (pulled n))
  have htimeconv' : Tendsto (fun n => (times (phi n)).val) atTop (𝓝 t) :=
    htimeconv.comp hphi.tendsto_atTop
  have hpair : Tendsto (fun n => ((times (phi n)).val, pulled (phi n))) atTop
      (𝓝 (t, x)) := htimeconv'.prodMk_nhds hpulled
  have hwithin : Tendsto (fun n => ((times (phi n)).val, pulled (phi n))) atTop
      (𝓝[Icc t b ×ˢ (univ : Set (F.slice t).carrier)] (t, x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpair
      (Eventually.of_forall fun n => ⟨(times (phi n)).property, mem_univ _⟩)
  have hcontinuous :=
    (hC.scalar_regular 3 (F.slice t).carrier (Icc t b) S.flow).continuousOn
  have hscalarconv :=
    (hcontinuous (t, x) ⟨⟨le_rfl, htb.le⟩, mem_univ x⟩).tendsto.comp hwithin
  have hscalar_slab (n : ℕ) :
      r⁻¹ ^ 2 ≤ (S.flow.connection (times (phi n)).val).scalarCurvature (pulled (phi n)) := by
    rw [← M44.regularSlab_scalar_eq F S (times (phi n)) (pulled (phi n))]
    simpa only [pulled, Diffeomorph.apply_symm_apply] using hscalar (phi n)
  have hlimit : r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x := by
    have h := ge_of_tendsto hscalarconv (Eventually.of_forall hscalar_slab)
    have heq := M44.regularSlab_scalar_eq F S ⟨t, ⟨le_rfl, htb.le⟩⟩ x
    rw [S.initial_identify] at heq
    rw [heq]
    exact h
  refine ⟨t, ht, hpast, b, htb, hJ, hfree, hbH, x, hlimit,
    times ∘ phi, pulled ∘ phi, htimeanti.comp_monotone hphi.monotone,
    htimeconv', hpulled, ?_⟩
  intro n
  simpa only [Function.comp_apply, pulled, S, Diffeomorph.apply_symm_apply] using
    And.intro (hscalar (phi n)) (hbad (phi n))

end PoincareMT.Proofs.M47
