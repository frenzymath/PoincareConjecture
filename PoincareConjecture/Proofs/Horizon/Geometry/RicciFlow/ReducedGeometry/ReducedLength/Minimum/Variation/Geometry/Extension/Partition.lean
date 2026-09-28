import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Extension
import Mathlib.Geometry.Manifold.PartitionOfUnity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {ι : Type v}

def timePartitionWeight (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ) (i : ι) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ I then ρ i ⟨s, hs⟩ else 0

@[simp]
theorem timePartitionWeight_coe (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ) (i : ι) (s : I) :
    timePartitionWeight I ρ i s = ρ i s := by
  simp only [timePartitionWeight, dif_pos s.property]

theorem timePartitionWeight_contDiffAt (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ) (i : ι) (s : I) :
    ContDiffAt ℝ ∞ (timePartitionWeight I ρ i) (s : ℝ) := by
  apply ContMDiffAt.contDiffAt
  apply (contMDiffAt_subtype_iff (U := I) (x := s)).mp
  have heq : (fun t : I ↦ timePartitionWeight I ρ i (t : ℝ)) = fun t ↦ ρ i t := by
    funext t
    exact timePartitionWeight_coe I ρ i t
  rw [heq]
  exact (ρ i).contMDiff.contMDiffAt

theorem timePartitionWeight_eventually_support_subset (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ) (s : I) :
    ∀ᶠ t : ℝ in 𝓝 (s : ℝ), ∀ i, timePartitionWeight I ρ i t ≠ 0 →
      i ∈ ρ.fintsupport s := by
  have hrel : ∀ᶠ t : I in 𝓝 s, ∀ i, timePartitionWeight I ρ i (t : ℝ) ≠ 0 →
      i ∈ ρ.fintsupport s := by
    filter_upwards [ρ.eventually_finsupport_subset s] with t ht
    intro i hi
    apply ht
    apply (ρ.mem_finsupport t).mpr
    simpa only [timePartitionWeight_coe, Function.mem_support] using hi
  have hw := (eventually_nhds_subtype_iff (I : Set ℝ) s
    (fun t ↦ ∀ i, timePartitionWeight I ρ i t ≠ 0 → i ∈ ρ.fintsupport s)).mp hrel
  simpa only [nhdsWithin_eq_nhds.mpr (I.isOpen.mem_nhds s.property)] using hw

theorem timePartitionWeight_sum_eq_one (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ) (s : I) {S : Finset ι}
    (hS : ∀ i, timePartitionWeight I ρ i (s : ℝ) ≠ 0 → i ∈ S) :
    ∑ i ∈ S, timePartitionWeight I ρ i (s : ℝ) = 1 := by
  have hsub : ρ.finsupport s ⊆ S := by
    intro i hi
    apply hS
    simpa only [timePartitionWeight_coe, Function.mem_support] using
      (ρ.mem_finsupport s).mp hi
  simpa only [timePartitionWeight_coe] using ρ.sum_finsupport' s (mem_univ s) hsub

variable {M : Type u} [TopologicalSpace M]

def curveGluingRelativeDomain (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (D : ι → Set (ℝ × M)) : Set (I × M) :=
  (⋃ i, Prod.fst ⁻¹' tsupport (ρ i) ∩
    (fun z : I × M ↦ ((z.1 : ℝ), z.2)) ⁻¹' (D i)ᶜ)ᶜ

omit [TopologicalSpace M] in
theorem mem_curveGluingRelativeDomain (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (D : ι → Set (ℝ × M)) {z : I × M} :
    z ∈ curveGluingRelativeDomain I ρ D ↔
      ∀ i, z.1 ∈ tsupport (ρ i) → ((z.1 : ℝ), z.2) ∈ D i := by
  simp only [curveGluingRelativeDomain, mem_compl_iff, mem_iUnion, mem_inter_iff,
    mem_preimage, not_exists, not_and, not_not]

theorem curveGluingRelativeDomain_open (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (D : ι → Set (ℝ × M)) (hD : ∀ i, IsOpen (D i)) :
    IsOpen (curveGluingRelativeDomain I ρ D) := by
  have hinc : Continuous (fun z : I × M ↦ ((z.1 : ℝ), z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hfinite : LocallyFinite (fun i ↦ Prod.fst ⁻¹' tsupport (ρ i) ∩
      (fun z : I × M ↦ ((z.1 : ℝ), z.2)) ⁻¹' (D i)ᶜ) :=
    ((ρ.toPartitionOfUnity.locallyFinite_tsupport).preimage_continuous continuous_fst).subset
      (fun _ ↦ inter_subset_left)
  exact (hfinite.isClosed_iUnion (fun i ↦
    ((isClosed_tsupport _).preimage continuous_fst).inter
      ((hD i).isClosed_compl.preimage hinc))).isOpen_compl

def curveGluingDomain (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (D : ι → Set (ℝ × M)) : Set (ℝ × M) :=
  (fun z : I × M ↦ ((z.1 : ℝ), z.2)) '' curveGluingRelativeDomain I ρ D

theorem curveGluingDomain_open (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (D : ι → Set (ℝ × M)) (hD : ∀ i, IsOpen (D i)) :
    IsOpen (curveGluingDomain I ρ D) :=
  (I.isOpen.isOpenMap_subtype_val.prodMap IsOpenMap.id) _
    (curveGluingRelativeDomain_open I ρ D hD)

omit [TopologicalSpace M] in
theorem curveGluingDomain_graph_mem (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (D : ι → Set (ℝ × M)) (γ : ℝ → M)
    (hgraph : ∀ (s : I) i, s ∈ tsupport (ρ i) → ((s : ℝ), γ s) ∈ D i) (s : I) :
    ((s : ℝ), γ s) ∈ curveGluingDomain I ρ D := by
  refine ⟨(s, γ s), ?_, rfl⟩
  exact (mem_curveGluingRelativeDomain I ρ D).mpr (hgraph s)

variable {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem contMDiffAt_sum_parametric (S : Finset ι)
    (A : ι → ℝ → (x : M) → TangentSpace (𝓡 n) x) {z : ℝ × M}
    (hA : ∀ i ∈ S, ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2
        (A i w.1 w.2)) z) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2
        (∑ i ∈ S, A i w.1 w.2)) z := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) z.2
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_snd, ?_⟩
  have hc : ∀ i ∈ S, ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) ∞
      (fun w : ℝ × M ↦ (e ⟨w.2, A i w.1 w.2⟩).2) z :=
    fun i hi ↦ (Bundle.contMDiffAt_totalSpace.mp (hA i hi)).2
  apply (contMDiffAt_finsetSum hc).congr_of_eventuallyEq
  have hnear : ∀ᶠ w : ℝ × M in 𝓝 z, w.2 ∈ e.baseSet :=
    continuous_snd.continuousAt (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))
  filter_upwards [hnear] with w hw
  change (e ⟨w.2, ∑ i ∈ S, A i w.1 w.2⟩).2 =
    ∑ i ∈ S, (e ⟨w.2, A i w.1 w.2⟩).2
  simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hw, map_sum]

def parametricWeightedSum (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (A : ι → ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (s : ℝ) (x : M) : TangentSpace (𝓡 n) x :=
  ∑ᶠ i, timePartitionWeight I ρ i s • A i s x

omit [IsManifold (𝓡 n) ∞ M] in
theorem parametricWeightedSum_eq_sum (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (A : ι → ℝ → (x : M) → TangentSpace (𝓡 n) x)
    {s : ℝ} (x : M) {S : Finset ι}
    (hS : ∀ i, timePartitionWeight I ρ i s ≠ 0 → i ∈ S) :
    parametricWeightedSum I ρ A s x = ∑ i ∈ S, timePartitionWeight I ρ i s • A i s x := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hS
  intro hz
  exact hi (by simp only [hz, zero_smul])

omit [IsManifold (𝓡 n) ∞ M] in
theorem parametricWeightedSum_eventually_eq_sum (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (A : ι → ℝ → (x : M) → TangentSpace (𝓡 n) x) (s : I) :
    ∀ᶠ t : ℝ in 𝓝 (s : ℝ), ∀ x : M,
      parametricWeightedSum I ρ A t x =
        ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i t • A i t x := by
  filter_upwards [timePartitionWeight_eventually_support_subset I ρ s] with t ht
  exact fun x ↦ parametricWeightedSum_eq_sum I ρ A x ht

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
