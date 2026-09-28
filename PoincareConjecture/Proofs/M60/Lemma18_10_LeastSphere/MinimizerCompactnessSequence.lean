import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessEquicontinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

theorem suNormalized_C1_subsequence
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hei : IsClosedEmbedding e)
    (hread : SUChartReadable (n := n) e)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (ha : Tendsto alpha atTop (𝓝 1)) (har : ∀ j, 1 ≤ alpha j ∧ alpha j ≤ 2)
    (heq : ∀ j, SUSphereWeightedEuler g (alpha j) (f j))
    (center : ℕ → UnitTwoSphere) (scale : ℕ → ℝ)
    (hs : ∀ j, 0 < scale j ∧ scale j ≤ 1)
    (henergy : ∀ j z, m60EnergyDensity g
      (fun y => f j ((chartAt LoopPlane (center j)).symm (scale j • y))) z ≤ 1 / 2) :
    let v := fun j z => f j ((chartAt LoopPlane (center j)).symm (scale j • z))
    ∃ (v0 : C(LoopPlane, M)) (k : ℕ → ℕ),
      ContMDiff (𝓡 2) (𝓡 n) 1 v0 ∧ StrictMono k ∧
      Tendsto (fun j => (⟨v (k j),
        ((hf (k j)).comp ((suSphereChart_smooth (center (k j))).comp
          (contDiff_id.const_smul (scale (k j))).contMDiff)).continuous⟩ : C(LoopPlane, M)))
        atTop (𝓝 v0) ∧
      TendstoLocallyUniformly (fun j => e ∘ v (k j)) (e ∘ v0) atTop ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (e ∘ v (k j)))
        (fderiv ℝ (e ∘ v0)) atTop := by
  let v := fun j z => f j ((chartAt LoopPlane (center j)).symm (scale j • z))
  have hv (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) ∞ (v j) :=
    (hf j).comp ((suSphereChart_smooth (center j)).comp
      (contDiff_id.const_smul (scale j)).contMDiff)
  obtain ⟨w, k0, C, hk0, -, hgrad, hlim, -⟩ :=
    suNormalized_C0_subsequence g e he hei v hv henergy
  have hequi : Equicontinuous (fun j z =>
      (e (v (k0 j) z), fderiv ℝ (e ∘ v (k0 j)) z)) :=
    suNormalized_firstJets_equicontinuous g e he hread (alpha ∘ k0) (f ∘ k0)
      (fun j => hf (k0 j)) (ha.comp hk0.tendsto_atTop) (fun j => har (k0 j))
      (fun j => heq (k0 j)) (center ∘ k0) (scale ∘ k0) (fun j => hs (k0 j))
      w C.coe_nonneg hlim (fun j z => hgrad (k0 j) z)
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuous.continuousOn
  have hbound (z : LoopPlane) : ∃ B : ℝ, ∀ j,
      ‖((e ∘ v (k0 j)) z, fderiv ℝ (e ∘ v (k0 j)) z)‖ ≤ B := by
    refine ⟨max A C, ?_⟩
    intro j
    exact max_le_max (hA (v (k0 j) z) (mem_univ _)) (hgrad (k0 j) z)
  obtain ⟨v0, k1, hv0, hk1, hvlim, hvalues, hderiv⟩ := suTarget_C1_subsequence e he hei hread
    (fun j => v (k0 j)) (fun j => hv (k0 j)) hequi hbound
  exact ⟨v0, k0 ∘ k1, hv0, hk0.comp hk1, hvlim, hvalues, hderiv⟩

end PoincareConjecture.M60
