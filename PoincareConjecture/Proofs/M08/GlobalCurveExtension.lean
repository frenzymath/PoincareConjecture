import PoincareConjecture.Proofs.M08.BackwardEulerTransport
import Mathlib.Geometry.Manifold.PartitionOfUnity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M08

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

theorem timePartitionWeight_eventually_sum_eq_one (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ) (s : I) :
    (fun t : ℝ ↦ ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i t) =ᶠ[𝓝 (s : ℝ)]
      fun _ ↦ (1 : ℝ) := by
  filter_upwards [I.isOpen.mem_nhds s.property,
    timePartitionWeight_eventually_support_subset I ρ s] with t ht hsub
  exact timePartitionWeight_sum_eq_one I ρ ⟨t, ht⟩ hsub

theorem timePartitionWeight_sum_deriv (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ) (s : I) :
    ∑ i ∈ ρ.fintsupport s, deriv (timePartitionWeight I ρ i) (s : ℝ) = 0 := by
  have hd := HasDerivAt.fun_sum (u := ρ.fintsupport s) (fun i _ ↦
    ((timePartitionWeight_contDiffAt I ρ i s).differentiableAt (by norm_num)).hasDerivAt)
  exact hd.unique ((hasDerivAt_const (s : ℝ) (1 : ℝ)).congr_of_eventuallyEq
    (timePartitionWeight_eventually_sum_eq_one I ρ s))

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

omit [IsManifold (𝓡 n) ∞ M] in
theorem curveVelocityWithin_eq_of_open {α : ℝ → M} {I U : Set ℝ} {s : ℝ}
    (hI : IsOpen I) (hU : IsOpen U) (hsI : s ∈ I) (hsU : s ∈ U) :
    curveVelocityWithin (n := n) α I s = curveVelocityWithin (n := n) α U s := by
  unfold curveVelocityWithin
  rw [mfderivWithin_of_mem_nhds (hI.mem_nhds hsI),
    mfderivWithin_of_mem_nhds (hU.mem_nhds hsU)]

theorem connection_sum_parametric {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (S : Finset ι) (A : ι → ℝ → (x : M) → TangentSpace (𝓡 n) x) {s : ℝ} {x : M}
    (hA : ∀ i ∈ S, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (A i s y)) x) :
    D.connection (fun y ↦ ∑ i ∈ S, A i s y) x = ∑ i ∈ S, D.connection (A i s) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change D.connection 0 x = 0
      exact D.connection.isCovariantDerivativeOn.zero
  | @insert i S hi ih =>
      have hAi := hA i (Finset.mem_insert_self i S)
      have hAS := fun j hj ↦ hA j (Finset.mem_insert_of_mem hj)
      have hsection : (fun y ↦ ∑ j ∈ insert i S, A j s y) =
          (fun y ↦ A i s y) + (fun y ↦ ∑ j ∈ S, A j s y) := by
        funext y
        exact Finset.sum_insert hi
      rw [hsection, D.connection.isCovariantDerivativeOn.add hAi
        (MDifferentiableAt.sum_section hAS), ih hAS, Finset.sum_insert hi]


def gluedParametricExtension (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (U : ι → Set ℝ) (hU : ∀ i, IsOpen (U i)) (α : ℝ → M)
    (E : ∀ i, ParametricAlongCurveExtensionOn (U i) α
      (curveVelocityWithin (n := n) α (U i)))
    (hρ : ρ.IsSubordinate (fun i ↦ (Subtype.val : I → ℝ) ⁻¹' U i)) :
    ParametricAlongCurveExtensionOn (I : Set ℝ) α (curveVelocityWithin (n := n) α I) where
  extension := parametricWeightedSum I ρ (fun i ↦ (E i).extension)
  domain := curveGluingDomain I ρ (fun i ↦ (E i).domain)
  open_domain := curveGluingDomain_open I ρ _ (fun i ↦ (E i).open_domain)
  graph_mem s hs := curveGluingDomain_graph_mem I ρ _ α
    (fun t i ht ↦ (E i).graph_mem t (hρ i ht)) ⟨s, hs⟩
  smooth z hz := by
    rcases hz with ⟨⟨s, x⟩, hz, rfl⟩
    have hdomain := (mem_curveGluingRelativeDomain I ρ (fun i ↦ (E i).domain)).mp hz
    have hpieces : ∀ i ∈ ρ.fintsupport s,
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
          (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2
            (timePartitionWeight I ρ i w.1 • (E i).extension w.1 w.2)) ((s : ℝ), x) := by
      intro i hi
      exact parametricExtension_contMDiffAt_smul_reparam (E i) (f := id)
        (hdomain i ((ρ.mem_fintsupport_iff s i).mp hi)) contDiffAt_id
        (timePartitionWeight_contDiffAt I ρ i s)
    have hsum := contMDiffAt_sum_parametric (ρ.fintsupport s)
      (fun i r y ↦ timePartitionWeight I ρ i r • (E i).extension r y) hpieces
    apply ContMDiffAt.contMDiffWithinAt
    apply hsum.congr_of_eventuallyEq
    have hnear : ∀ᶠ w : ℝ × M in 𝓝 ((s : ℝ), x), ∀ y : M,
        parametricWeightedSum I ρ (fun i ↦ (E i).extension) w.1 y =
          ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i w.1 •
            (E i).extension w.1 y :=
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℝ × M → ℝ)
        ((s : ℝ), x)).eventually
          (parametricWeightedSum_eventually_eq_sum I ρ (fun i ↦ (E i).extension) s)
    filter_upwards [hnear] with w hw
    exact congrArg (fun v : TangentSpace (𝓡 n) w.2 ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2 v) (hw w.2)
  agrees τ hτ := by
    let s : I := ⟨τ, hτ⟩
    have hS := (timePartitionWeight_eventually_support_subset I ρ s).self_of_nhds
    rw [parametricWeightedSum_eq_sum I ρ (fun i ↦ (E i).extension) (α τ) hS]
    calc
      (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i τ • (E i).extension τ (α τ)) =
          ∑ i ∈ ρ.fintsupport s,
            timePartitionWeight I ρ i τ • curveVelocityWithin (n := n) α I τ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hτU : τ ∈ U i := hρ i ((ρ.mem_fintsupport_iff s i).mp hi)
        rw [(E i).agrees τ hτU,
          ← curveVelocityWithin_eq_of_open I.isOpen (hU i) hτ hτU]
      _ = (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i τ) •
          curveVelocityWithin (n := n) α I τ := (Finset.sum_smul ..).symm
      _ = curveVelocityWithin (n := n) α I τ := by
        rw [timePartitionWeight_sum_eq_one I ρ s hS, one_smul]

theorem parametricWeightedSum_deriv (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (U : ι → Set ℝ) (α : ℝ → M)
    (E : ∀ i, ParametricAlongCurveExtensionOn (U i) α
      (curveVelocityWithin (n := n) α (U i))) (s : I) (x : M)
    (hmem : ∀ i ∈ ρ.fintsupport s, ((s : ℝ), x) ∈ (E i).domain) :
    deriv (fun r ↦ parametricWeightedSum I ρ (fun i ↦ (E i).extension) r x) (s : ℝ) =
      ∑ i ∈ ρ.fintsupport s,
        (timePartitionWeight I ρ i (s : ℝ) • deriv (fun r ↦ (E i).extension r x) (s : ℝ) +
          deriv (timePartitionWeight I ρ i) (s : ℝ) • (E i).extension s x) := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  have hderiv : ∀ i ∈ ρ.fintsupport s,
      HasDerivAt (fun r ↦ timePartitionWeight I ρ i r • (E i).extension r x)
        (timePartitionWeight I ρ i (s : ℝ) • deriv (fun r ↦ (E i).extension r x) (s : ℝ) +
          deriv (timePartitionWeight I ρ i) (s : ℝ) • (E i).extension s x) (s : ℝ) := by
    intro i hi
    have hc := ((timePartitionWeight_contDiffAt I ρ i s).differentiableAt
      (by norm_num)).hasDerivAt
    have hE := (parametricExtension_differentiableAt_time (E i) (hmem i hi)).hasDerivAt
    simpa only [Pi.smul_def'] using hc.smul hE
  have hnear : (fun r ↦ parametricWeightedSum I ρ (fun i ↦ (E i).extension) r x) =ᶠ[𝓝 (s : ℝ)]
      fun r ↦ ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i r • (E i).extension r x :=
    (parametricWeightedSum_eventually_eq_sum I ρ (fun i ↦ (E i).extension) s).mono
      (fun _ hr ↦ hr x)
  exact ((HasDerivAt.fun_sum hderiv).congr_of_eventuallyEq hnear).deriv

theorem parametricWeightedSum_connection (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (U : ι → Set ℝ) (α : ℝ → M)
    (E : ∀ i, ParametricAlongCurveExtensionOn (U i) α
      (curveVelocityWithin (n := n) α (U i))) (s : I) (x : M)
    (hmem : ∀ i ∈ ρ.fintsupport s, ((s : ℝ), x) ∈ (E i).domain)
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (X : TangentSpace (𝓡 n) x) :
    D.connection (parametricWeightedSum I ρ (fun i ↦ (E i).extension) s) x X =
      ∑ i ∈ ρ.fintsupport s,
        timePartitionWeight I ρ i (s : ℝ) • D.connection ((E i).extension s) x X := by
  have hS := (timePartitionWeight_eventually_support_subset I ρ s).self_of_nhds
  have hsection : parametricWeightedSum I ρ (fun i ↦ (E i).extension) s =
      fun y ↦ ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) • (E i).extension s y := by
    funext y
    exact parametricWeightedSum_eq_sum I ρ (fun i ↦ (E i).extension) y hS
  have hspace : ∀ i ∈ ρ.fintsupport s,
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
        (fun y ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y ((E i).extension s y)) x :=
    fun i hi ↦ (parametricExtension_contMDiffAt_space (E i) (hmem i hi)).mdifferentiableAt
      (by norm_num)
  have hscaled : ∀ i ∈ ρ.fintsupport s,
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
        (fun y ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
          (timePartitionWeight I ρ i (s : ℝ) • (E i).extension s y)) x :=
    fun i hi ↦ (hspace i hi).smul_const_section
  rw [hsection, connection_sum_parametric D (ρ.fintsupport s)
    (fun i r y ↦ timePartitionWeight I ρ i r • (E i).extension r y) hscaled]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hc := D.connection.isCovariantDerivativeOn.smul_const
    (timePartitionWeight I ρ i (s : ℝ)) (hspace i hi)
  exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x ↦ L X) hc

theorem gluedParametricExtension_pullback {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (U : ι → Set ℝ) (hU : ∀ i, IsOpen (U i)) (α : ℝ → M)
    (E : ∀ i, ParametricAlongCurveExtensionOn (U i) α
      (curveVelocityWithin (n := n) α (U i)))
    (hρ : ρ.IsSubordinate (fun i ↦ (Subtype.val : I → ℝ) ⁻¹' U i)) (s : I) :
    pullbackCovariantDerivative F time α (curveVelocityWithin (n := n) α I) I
        (gluedParametricExtension I ρ U hU α E hρ) s =
      ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) •
        pullbackCovariantDerivative F time α (curveVelocityWithin (n := n) α (U i))
          (U i) (E i) s := by
  have hlocal : ∀ i ∈ ρ.fintsupport s, (s : ℝ) ∈ U i :=
    fun i hi ↦ hρ i ((ρ.mem_fintsupport_iff s i).mp hi)
  have hmem := fun i hi ↦ (E i).graph_mem s (hlocal i hi)
  have hvelocity : ∀ i ∈ ρ.fintsupport s,
      curveVelocityWithin (n := n) α (U i) s = curveVelocityWithin (n := n) α I s :=
    fun i hi ↦ (curveVelocityWithin_eq_of_open I.isOpen (hU i) s.property (hlocal i hi)).symm
  have hagrees : ∀ i ∈ ρ.fintsupport s,
      (E i).extension s (α s) = curveVelocityWithin (n := n) α I s :=
    fun i hi ↦ ((E i).agrees s (hlocal i hi)).trans (hvelocity i hi)
  have hcancel : (∑ i ∈ ρ.fintsupport s,
      deriv (timePartitionWeight I ρ i) (s : ℝ) • (E i).extension s (α s)) = 0 := by
    calc
      _ = ∑ i ∈ ρ.fintsupport s, deriv (timePartitionWeight I ρ i) (s : ℝ) •
          curveVelocityWithin (n := n) α I s :=
        Finset.sum_congr rfl (fun i hi ↦ congrArg
          (fun v ↦ deriv (timePartitionWeight I ρ i) (s : ℝ) • v) (hagrees i hi))
      _ = (∑ i ∈ ρ.fintsupport s, deriv (timePartitionWeight I ρ i) (s : ℝ)) •
          curveVelocityWithin (n := n) α I s := (Finset.sum_smul ..).symm
      _ = 0 := by rw [timePartitionWeight_sum_deriv, zero_smul]
  simp only [pullbackCovariantDerivative, gluedParametricExtension]
  rw [parametricWeightedSum_deriv I ρ U α E s (α s) hmem,
    parametricWeightedSum_connection I ρ U α E s (α s) hmem,
    Finset.sum_add_distrib, hcancel, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hvelocity i hi, smul_add]

theorem gluedParametricExtension_equation {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (U : ι → Set ℝ) (hU : ∀ i, IsOpen (U i)) (α : ℝ → M)
    (E : ∀ i, ParametricAlongCurveExtensionOn (U i) α
      (curveVelocityWithin (n := n) α (U i)))
    (hρ : ρ.IsSubordinate (fun i ↦ (Subtype.val : I → ℝ) ⁻¹' U i))
    (heq : ∀ i r, r ∈ U i → regularizedLGeodesicEquation F T α (U i) (E i) r)
    (s : I) : regularizedLGeodesicEquation F T α I
      (gluedParametricExtension I ρ U hU α E hρ) s := by
  intro W
  let G := (F.metric (T - (s : ℝ) ^ 2)).inner (α s)
  let V (i : ι) := pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
    (curveVelocityWithin (n := n) α (U i)) (U i) (E i) s
  let R := scalarCurvatureDifferential F (fun r ↦ T - r ^ 2) α s W
  let C := 4 * (s : ℝ) * (F.connection (T - (s : ℝ) ^ 2)).ricci (α s)
    (curveVelocityWithin (n := n) α I s) W
  let B := 2 * (s : ℝ) ^ 2 * R - C
  have hS := (timePartitionWeight_eventually_support_subset I ρ s).self_of_nhds
  have hinnerLocal : ∀ i ∈ ρ.fintsupport s, G (V i) W = B := by
    intro i hi
    have hsU : (s : ℝ) ∈ U i := hρ i ((ρ.mem_fintsupport_iff s i).mp hi)
    have h := heq i s hsU W
    unfold regularizedEulerResidual at h
    rw [← curveVelocityWithin_eq_of_open I.isOpen (hU i) s.property hsU] at h
    change G (V i) W - 2 * (s : ℝ) ^ 2 * R + C = 0 at h
    dsimp only [B]
    linarith
  have hmetric : G (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) • V i) W =
      ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) * G (V i) W := by
    rw [map_sum]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [G.map_smul]
    rfl
  have hinner : G (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
      (curveVelocityWithin (n := n) α I) I
      (gluedParametricExtension I ρ U hU α E hρ) s) W = B := by
    rw [gluedParametricExtension_pullback F (fun r ↦ T - r ^ 2) I ρ U hU α E hρ s]
    change G (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) • V i) W = B
    rw [hmetric]
    calc
      (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) * G (V i) W) =
          ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) * B :=
        Finset.sum_congr rfl (fun i hi ↦ congrArg
          (fun r ↦ timePartitionWeight I ρ i (s : ℝ) * r) (hinnerLocal i hi))
      _ = (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ)) * B :=
        (Finset.sum_mul ..).symm
      _ = B := by rw [timePartitionWeight_sum_eq_one I ρ s hS, one_mul]
  change G (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
      (curveVelocityWithin (n := n) α I) I
      (gluedParametricExtension I ρ U hU α E hρ) s) W - 2 * (s : ℝ) ^ 2 * R + C = 0
  rw [hinner]
  dsimp only [B]
  ring


theorem exists_regularizedEuler_extension_of_local {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {I : Set ℝ} (hI : IsOpen I) (α : ℝ → M)
    (hloc : ∀ s ∈ I, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ U ⊆ I ∧
      ∃ E : ParametricAlongCurveExtensionOn U α (curveVelocityWithin (n := n) α U),
        ∀ r ∈ U, regularizedLGeodesicEquation F T α U E r) :
    ∃ E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I),
      ∀ s ∈ I, regularizedLGeodesicEquation F T α I E s := by
  classical
  let O : TopologicalSpace.Opens ℝ := ⟨I, hI⟩
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  choose U hU hsU _hsub E heq using fun s : O ↦ hloc s s.property
  have hcover : (univ : Set O) ⊆ ⋃ i : O, (Subtype.val : O → ℝ) ⁻¹' U i := by
    intro s _
    exact mem_iUnion.mpr ⟨s, hsU s⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity O (𝓘(ℝ, ℝ)) O univ,
      ρ.IsSubordinate (fun i ↦ (Subtype.val : O → ℝ) ⁻¹' U i) :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ)) isClosed_univ _
      (fun i ↦ (hU i).preimage continuous_subtype_val) hcover
  refine ⟨gluedParametricExtension O ρ U hU α E hρ, ?_⟩
  intro s hs
  exact gluedParametricExtension_equation F T O ρ U hU α E hρ heq ⟨s, hs⟩

end PoincareConjecture.M08
