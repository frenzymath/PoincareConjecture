import PoincareConjecture.Proofs.M76.Rigidity.OriginalCapPairCharts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ConvexTargetRestriction

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_isolated_slice_pair_chart
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    {t u : ℝ} (ht : t ∈ I) (hu : u ∈ I) (htu : t ≠ u) (z : D) :
    ∃ G : OpenPartialHomeomorph X C3,
      P.slice t z ∈ G.source ∧ G (P.slice t z) = 0 ∧ Convex ℝ G.target ∧
      Disjoint G.source (P.slice u '' D) ∧
      (∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans G) ((e i).symm.trans G).source ∧
        LocallyPiecewiseAffineOn (G.symm.trans (e i)) (G.symm.trans (e i)).source) ∧
      ((G.source ⊆ interior R ∧
        ∀ x ∈ G.source, x ∈ P.slice t '' D ↔ (G x).2 = 0) ∨
       ((∀ x ∈ G.source, x ∈ R ↔ 0 ≤ (G x).1.1) ∧
        ∀ x ∈ G.source, x ∈ P.slice t '' D ↔ 0 ≤ (G x).1.1 ∧ (G x).2 = 0)) := by
  obtain ⟨H, hzH, _, hHz, hcompat, hpair⟩ := P.exists_slice_pair_chart he ht z
  have hother : IsClosed (P.slice u '' D) :=
    ((isCompact_closedBall (0 : V2) 1).image_of_continuousOn
      (P.polyhedral_slice hu).continuousOn).isClosed
  have hzother : P.slice t z ∉ P.slice u '' D :=
    fun hx => disjoint_left.mp (P.disjoint_slice_images ht hu htu)
      ⟨z, z.property, rfl⟩ hx
  obtain ⟨G, hzG, hGz, hcv, hGs, hGt, hdis, hvalue, hinv⟩ :=
    H.exists_convex_target_avoiding hzH hHz hother hzother
  have hGcompat (i : ι) :
      LocallyPiecewiseAffineOn ((e i).symm.trans G) ((e i).symm.trans G).source ∧
      LocallyPiecewiseAffineOn (G.symm.trans (e i)) (G.symm.trans (e i)).source := by
    constructor
    · have h := (hcompat i).1.mono ((e i).symm.trans G).open_source
        (fun _ hx => ⟨hx.1, hGs hx.2⟩)
      apply h.congr
      intro x _
      change H ((e i).symm x) = G ((e i).symm x)
      exact (hvalue _).symm
    · have h := (hcompat i).2.mono (G.symm.trans (e i)).open_source (by
        intro x hx
        refine ⟨hGt hx.1, ?_⟩
        change H.symm x ∈ (e i).source
        rw [← hinv x]
        exact hx.2)
      apply h.congr
      intro x _
      change (e i) (H.symm x) = (e i) (G.symm x)
      rw [hinv x]
  refine ⟨G, hzG, hGz, hcv, hdis, hGcompat, ?_⟩
  rcases hpair with ⟨hinside, hcap⟩ | ⟨hregion, hcap⟩
  · left
    refine ⟨hGs.trans hinside, ?_⟩
    intro x hx
    rw [hvalue x]
    exact hcap x (hGs hx)
  · right
    constructor
    · intro x hx
      rw [hvalue x]
      exact hregion x (hGs hx)
    · intro x hx
      rw [hvalue x]
      exact hcap x (hGs hx)

end PoincareConjecture.M76
