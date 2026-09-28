import PoincareConjecture.Proofs.M76.Dehn.OriginalRegionBranchCharts










set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}




theorem Step.compatible_branch_chart (step : Step s t)
    (B : OpenPartialHomeomorph t.Carrier s.Carrier)
    (hB : EqOn B (step.projection ∘ step.inclusion) B.source)
    (Q : OpenPartialHomeomorph s.Carrier E)
    (hQ : ∀ l, (s.charts l).symm.trans Q ∈ piecewiseAffineGroupoid E) :
    ∀ k, (t.charts k).symm.trans (B.trans Q) ∈ piecewiseAffineGroupoid E := by
  intro k
  let T := (t.charts k).symm.trans (B.trans Q)
  let A := (s.charts (step.chartIndex k)).symm.trans Q
  have heq : EqOn T A T.source := by
    intro z hz
    change Q (B ((t.charts k).symm z)) = Q ((s.charts (step.chartIndex k)).symm z)
    exact congrArg Q ((hB hz.2.1).trans (step.chart_inverse k hz.1))
  have hsub : T.source ⊆ A.source := by
    intro z hz
    refine ⟨step.chart_target k hz.1, ?_⟩
    have hi : B ((t.charts k).symm z) = (s.charts (step.chartIndex k)).symm z :=
      (hB hz.2.1).trans (step.chart_inverse k hz.1)
    change (s.charts (step.chartIndex k)).symm z ∈ Q.source
    rw [← hi]
    exact hz.2.2
  apply (mem_piecewiseAffineGroupoid_iff_forward T).mpr
  exact (((mem_piecewiseAffineGroupoid_iff_forward A).mp
    (hQ (step.chartIndex k))).mono T.open_source hsub).congr heq.symm

local notation "V3" => (Fin 3 → ℝ)






theorem Step.exists_paired_original_region_charts
    {e : ι → OpenPartialHomeomorph M V3}
    {s t : Stage e S f r C} (step : Step s t) {R : Set M}
    (he : PoincareConjecture.M76.PLDomain e R)
    {x : t.Carrier} (hxR : x ∈ t.projection ⁻¹' R)
    {W : Set t.Carrier} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ (Q : OpenPartialHomeomorph t.Carrier V3)
      (B : OpenPartialHomeomorph s.Carrier V3),
      x ∈ Q.source ∧ Q.source ⊆ W ∧
      InjOn (step.projection ∘ step.inclusion) Q.source ∧
      (∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ l, (s.charts l).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      Q.target = B.target ∧
      (∀ y, Q y = B (step.projection (step.inclusion y))) ∧
      MapsTo (step.projection ∘ step.inclusion) Q.source B.source ∧
      EqOn ((step.projection ∘ step.inclusion) ∘ Q.symm) B.symm B.target ∧
      (B.source ⊆ interior (s.projection ⁻¹' R) ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ell (Q x) = 0 ∧
          (∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y)) ∧
          ∀ y ∈ B.source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B y) = 0) := by
  let p := step.projection ∘ step.inclusion
  obtain ⟨L, hxL, hpL⟩ := step.projectionInclusion_local x
  have hLp : (L : t.Carrier → s.Carrier) = p := hpL.symm
  let O := L.target ∩ L.symm ⁻¹' W
  have hO : IsOpen O := L.isOpen_inter_preimage_symm hW
  have hxO : p x ∈ O := by
    rw [← hLp]
    refine ⟨L.map_source hxL, ?_⟩
    change L.symm (L x) ∈ W
    rw [L.left_inv hxL]
    exact hxW
  have hxRs : p x ∈ s.projection ⁻¹' R := (step.region_preimage R).subset hxR
  have hid : IsLocallyInjective (id : s.Carrier → s.Carrier) :=
    Function.injective_id.IsLocallyInjective
  obtain ⟨B, hxB, hBO, _, hB, hmodel⟩ :=
    (s.plDomain_region he).exists_injective_region_chart hid hxRs hO hxO
  let Q := L.trans B
  have hval (y : t.Carrier) : Q y = B (p y) := congrArg B (congrFun hLp y)
  have hmaps : MapsTo p Q.source B.source := by
    intro y hy
    have hyB : L y ∈ B.source := hy.2
    exact (congrFun hLp y) ▸ hyB
  have hsource : Q.source ⊆ W := by
    intro y hy
    have hyW := (hBO hy.2).2
    change L.symm (L y) ∈ W at hyW
    rwa [L.left_inv hy.1] at hyW
  have hinj : InjOn p Q.source := by
    intro y hy z hz hyz
    apply L.injOn hy.1 hz.1
    exact (congrFun hLp y).trans (hyz.trans (congrFun hLp z).symm)
  have htarget : Q.target = B.target := by
    ext z
    constructor
    · exact fun hz => hz.1
    · exact fun hz => ⟨hz, (hBO (B.map_target hz)).1⟩
  have hinv : EqOn (p ∘ Q.symm) B.symm B.target := by
    intro z hz
    change p (L.symm (B.symm z)) = B.symm z
    rw [← hLp]
    exact L.right_inv (hBO (B.map_target hz)).1
  refine ⟨Q, B, ⟨hxL, ?_⟩, hsource, hinj,
    step.compatible_branch_chart L (fun y _ => congrFun hLp y) B hB,
    hB, htarget, hval, hmaps, hinv, ?_⟩
  · change L x ∈ B.source
    rw [hLp]
    exact hxB
  · rcases hmodel with hinside | ⟨ell, v, hv, hzero, hhalf, hfront⟩
    · exact Or.inl hinside
    · exact Or.inr ⟨ell, v, hv, by simpa only [hval] using hzero, hhalf, hfront⟩

end Geometry.OriginalPLTower
