import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Density
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Algebra.Monoid









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter UniformSpace
open scoped Manifold ContDiff Bundle Topology BigOperators

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

private theorem cutoff_domain_isSigmaCompact (g : RiemannianMetric n M)
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) : IsSigmaCompact Ω := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let : SecondCountableTopology Ω :=
    (hc.isSeparable.mono subset_closure).secondCountableTopology
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

private theorem exists_energyTest_eq_one_on_compact (D : LeviCivitaData g)
    (hΩ : IsOpen Ω) {K : Set M} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ φ : EnergyTest D Ω, (∀ x : M, φ x ∈ Icc (0 : ℝ) 1) ∧ ∀ x ∈ K, φ x = 1 := by
  classical
  have hlocal (x : K) :
      ∃ b : SmoothBumpFunction (𝓡 n) (x : M), tsupport (b : M → ℝ) ⊆ Ω := by
    obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) (x : M)).mem_iff.mp
      (hΩ.mem_nhds (hKΩ x.property))
    exact ⟨b, hb⟩
  choose b hb using hlocal
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover'
    (fun x hx => {y : M | b ⟨x, hx⟩ y = 1})
    (fun x hx => (b ⟨x, hx⟩).eventuallyEq_one)
  let φ : M → ℝ := fun x => 1 - ∏ i ∈ s, (1 - b i x)
  have hφsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ :=
    contMDiff_const.sub (ContMDiff.prod fun i _ => contMDiff_const.sub (b i).contMDiff)
  have hcompact : IsCompact (⋃ i ∈ s, tsupport (b i : M → ℝ)) :=
    s.isCompact_biUnion (fun i _ => (b i).hasCompactSupport)
  have hsupport : tsupport φ ⊆ ⋃ i ∈ s, tsupport (b i : M → ℝ) := by
    apply closure_minimal _ hcompact.isClosed
    intro x hx
    by_contra hnot
    have hz (i : K) (hi : i ∈ s) : b i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hnot (mem_iUnion₂.mpr ⟨i, hi, h⟩))
    have hprod : (∏ i ∈ s, (1 - b i x)) = 1 :=
      Finset.prod_eq_one (fun i hi => by rw [hz i hi]; simp)
    exact hx (by simp only [φ, hprod, sub_self])
  have hsupportΩ : tsupport φ ⊆ Ω := hsupport.trans (by
    intro x hx
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp hx
    exact hb i hi)
  refine ⟨⟨φ, hφsmooth, hcompact.of_isClosed_subset isClosed_closure hsupport, hsupportΩ⟩,
    ?_, ?_⟩
  · intro x
    have hnonneg : 0 ≤ ∏ i ∈ s, (1 - b i x) :=
      Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (b i).le_one)
    have hone : (∏ i ∈ s, (1 - b i x)) ≤ 1 :=
      Finset.prod_le_one (fun i _ => sub_nonneg.mpr (b i).le_one)
        (fun i _ => by linarith [(b i).nonneg (x := x)])
    change 1 - (∏ i ∈ s, (1 - b i x)) ∈ Icc (0 : ℝ) 1
    exact ⟨sub_nonneg.mpr hone, by linarith⟩
  · intro x hx
    obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs hx)
    have hz : (∏ i ∈ s, (1 - b i x)) = 0 :=
      Finset.prod_eq_zero hi (sub_eq_zero.mpr hix.symm)
    change 1 - (∏ i ∈ s, (1 - b i x)) = 1
    rw [hz, sub_zero]



theorem exists_energyTest_cutoffs (D : LeviCivitaData g)
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) :
    ∃ φ : ℕ → EnergyTest D Ω,
      (∀ j : ℕ, ∀ x : M, φ j x ∈ Icc (0 : ℝ) 1) ∧
      ∀ x ∈ Ω, Tendsto (fun j : ℕ => φ j x) atTop (𝓝 (1 : ℝ)) := by
  let : SigmaCompactSpace Ω :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (cutoff_domain_isSigmaCompact g hΩ hc)
  let K : ℕ → Set M := fun j => Subtype.val '' compactCovering Ω j
  have hK (j : ℕ) : IsCompact (K j) :=
    (isCompact_compactCovering Ω j).image continuous_subtype_val
  have hKΩ (j : ℕ) : K j ⊆ Ω := by
    rintro x ⟨y, -, rfl⟩
    exact y.property
  choose φ hφ hφone using fun j => exists_energyTest_eq_one_on_compact D hΩ (hK j) (hKΩ j)
  refine ⟨φ, hφ, ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := exists_mem_compactCovering (⟨x, hx⟩ : Ω)
  have heq : (fun k : ℕ => φ k x) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hφone k x ⟨⟨x, hx⟩, compactCovering_subset Ω hk hj, rfl⟩
  exact tendsto_const_nhds.congr' heq.symm

end PoincareConjecture.LeviCivitaData.Dirichlet
