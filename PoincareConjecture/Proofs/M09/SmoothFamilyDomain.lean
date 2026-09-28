import PoincareConjecture.Proofs.M09.NormalizedSquareFamily

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def smoothFamilyDomain (f : E × ℝ → M) : Set (E × ℝ) :=
  {z | ∃ U : Set (E × ℝ), IsOpen U ∧ z ∈ U ∧
    ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U}

theorem subset_smoothFamilyDomain (f : E × ℝ → M) {U : Set (E × ℝ)}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U) :
    U ⊆ smoothFamilyDomain (n := n) f := fun _ hz ↦ ⟨U, hU, hz, hf⟩

theorem isOpen_smoothFamilyDomain (f : E × ℝ → M) :
    IsOpen (smoothFamilyDomain (n := n) f) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hzU, hf⟩ := hz
  exact Filter.mem_of_superset (hU.mem_nhds hzU) (subset_smoothFamilyDomain f hU hf)

theorem contMDiffOn_smoothFamilyDomain (f : E × ℝ → M) :
    ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f (smoothFamilyDomain (n := n) f) := by
  intro z hz
  obtain ⟨U, hU, hzU, hf⟩ := hz
  exact (hf.contMDiffAt (hU.mem_nhds hzU)).contMDiffWithinAt

theorem normalizedSquareFamily_zero_mem_smoothFamilyDomain {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (Z0 : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    (Z0, 0) ∈ smoothFamilyDomain (n := n)
      (fun z ↦ normalizedSquareFamily F T b p z.1 z.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  obtain ⟨W, d, hW, hZ, hd, _, hf⟩ :=
    exists_normalizedSquareFamily_smooth_zero F hM04 T b hb hwindow p Z0
  exact ⟨W ×ˢ Set.Ioo (-d) d, hW.prod isOpen_Ioo,
    ⟨hZ, neg_lt_zero.mpr hd, hd⟩, hf⟩

end PoincareConjecture.Proofs.M09
