import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusInwardApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RawAnnulusObservedLTrace














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain






theorem lower_halfDisk_graph_approximation
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {x H : ℝ} (hHpos : 0 < H) (hx : H < x)
    (hP : x + H < curvePeriod) (hH : H < 1) :
    let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
    let u := fun z => e (A.annulus.map (z + annulusPoint x 0))
    let V := fun i z => A.annulus.column i (z + annulusPoint x 0)
    let b := fun s => e (c0 (A.label0 (s + x)))
    MemLp u 2 (volume.restrict K) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict K)) ∧
      MemLp b 2 (volume.restrict (Icc (-H) H)) ∧
      ∃ f : ℕ → LoopPlane → E, (∀ j, ContDiff ℝ 1 (f j)) ∧
        Tendsto (fun j => eLpNorm (f j - u) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        (∀ i : Fin 2, Tendsto (fun j => eLpNorm (fun z =>
          fderiv ℝ (f j) z (EuclideanSpace.single i 1) - V i z)
            2 (volume.restrict K)) atTop (𝓝 0)) ∧
        Tendsto (fun j => eLpNorm (fun s => f j (annulusPoint s 0) - b s)
          2 (volume.restrict (Icc (-H) H))) atTop (𝓝 0) := by
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  let T := fun z : LoopPlane => z + annulusPoint x 0
  have hT : MeasurePreserving T volume volume := measurePreserving_add_right volume _
  have hbase : ∀ᵐ z ∂volume.restrict K, T z ∈ S := m64Annulus_halfDisk_ae_mem hx hP hH
  have hval := (m64MeasurePreserving_memLp_restrict hT isOpen_interior.measurableSet
    hbase A.annulus.observed_memLp).1
  have hcols (i : Fin 2) :=
    (m64MeasurePreserving_memLp_restrict hT isOpen_interior.measurableSet
      hbase (Lp.memLp (A.annulus.column i))).1
  have hbc : Continuous (fun s => e (c0 (A.label0 (s + x)))) :=
    (hc0.comp (A.labels_continuous hH0 hH1).1).comp (continuous_id.add continuous_const)
  have hbl : MemLp (fun s => e (c0 (A.label0 (s + x)))) 2
      (volume.restrict (Icc (-H) H)) := by
    apply (memLp_two_iff_integrable_sq_norm hbc.aestronglyMeasurable).mpr
    exact (hbc.norm.pow 2).integrableOn_Icc
  have hclass := A.annulus.classical_columns_of_contMDiffOn he hA
  have hs : ContDiffOn ℝ 1 (e ∘ A.annulus.map) S := by
    intro p hp
    exact (contMDiffAt_iff_contDiffAt.mp ((he _).comp p
      (hA.contMDiffAt (isOpen_interior.mem_nhds hp)))).contDiffWithinAt
  have hD (i : Fin 2) : MemLp (fun p =>
      fderiv ℝ (e ∘ A.annulus.map) p (EuclideanSpace.single i 1))
        2 (volume.restrict S) := (Lp.memLp (A.annulus.column i)).ae_eq (hclass i)
  obtain ⟨f, hf, hfv, hfD, hfb⟩ := m64Annulus_inward_strong_approximation
    hs A.annulus.observed_memLp hD
    (fun t ht => (A.raw_vertical_trace_l2_control he hA hc0 hc1 t ht).1.1)
    (A.raw_vertical_trace_strong he hA hc0 hc1).1 hHpos hx hP hH
  refine ⟨hval, hcols, hbl, f, hf, hfv, ?_, hfb⟩
  intro i
  have hcol := m64MeasurePreserving_ae_restrict hT isOpen_interior.measurableSet
    hbase (hclass i)
  apply (hfD i).congr
  intro j
  apply eLpNorm_congr_ae
  filter_upwards [hcol] with z hz
  rw [hz]

end PoincareConjecture.M64FreeWeakPhaseAnnulus
