import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.AmbientHalfbox
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.CollarPatch
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_common_collar_chart_of_base_patch
    {W X ι : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    {R S T S₀ C₀ C₁ : Set X} (he : PLDomain e R) (hSR : S ⊆ R) (hTR : T ⊆ R)
    (hS₀ : S₀ ⊆ frontier R)
    {d : ℝ} (hd : 0 < d) (u : P2 → X)
    (hu : PolyhedralPLInCharts e u (Icc (-d) d ×ˢ Icc (-d) d))
    (hui : InjOn u (Icc (-d) d ×ˢ Icc (-d) d))
    (huS : MapsTo u (Icc (-d) d ×ˢ Icc (-d) d) S₀)
    (huaxis₀ : ∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d, u z ∈ C₀ ↔ z.2 = 0)
    (huaxis₁ : ∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d, u z ∈ C₁ ↔ z.1 = 0)
    {B D₀ D₁ : Set W} (HB : B ≃ₜ frontier R) {a : ℝ} (ha : 0 < a)
    (c : W × ℝ → X) (hc : PolyhedralPLInCharts e c (B ×ˢ Icc (0 : ℝ) a))
    (hi : InjOn c (B ×ˢ Icc (0 : ℝ) a))
    (hbase : ∀ x : B, c (x, 0) = HB x)
    (hcR : MapsTo c (B ×ˢ Icc (0 : ℝ) a) R)
    (hcfront : ∀ z ∈ B ×ˢ Icc (0 : ℝ) a, c z ∈ frontier R ↔ z.2 = 0)
    (hD₀ : D₀ ⊆ B) (hD₁ : D₁ ⊆ B)
    (htrace₀ : S ∩ c '' (B ×ˢ Ico (0 : ℝ) a) = c '' (D₀ ×ˢ Ico (0 : ℝ) a))
    (htrace₁ : T ∩ c '' (B ×ˢ Ico (0 : ℝ) a) = c '' (D₁ ×ˢ Ico (0 : ℝ) a))
    (hzero₀ : (c '' (D₀ ×ˢ ({0} : Set ℝ))) ∩ S₀ = C₀)
    (hzero₁ : (c '' (D₁ ×ˢ ({0} : Set ℝ))) ∩ S₀ = C₁) :
    ∃ C : OriginalSurfacePairChart e S T (u 0) true,
      (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
      ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0 := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (show -d < d by linarith)).prod
      (isFinitePLBallPair_Icc (show -d < d by linarith))
  obtain ⟨w, hw, hwi, hwR, hw0, hwfront, hwtrace⟩ :=
    exists_original_common_collar_patch he.compatible HB (half_pos ha) (half_lt_self ha)
      c hc hi hbase hcR hcfront J hJ u (hJs.symm ▸ hu)
      (hui.mono hJs.subset) (fun _ hz => hS₀ (huS (hJs.subset hz)))
  have hcenter : w 0 = u 0 := hw0 0 (hJs.symm.subset (by
    change (-d ≤ 0 ∧ 0 ≤ d) ∧ (-d ≤ 0 ∧ 0 ≤ d)
    constructor <;> constructor <;> linarith))
  have haxis₀ (z : P2 × ℝ) (hz : z ∈ J.space ×ˢ Icc (0 : ℝ) (a / 2)) :
      w z ∈ S ↔ z.1.2 = 0 := by
    rw [hwtrace S D₀ hD₀ htrace₀ z hz]
    have hs := huS (hJs.subset hz.1)
    have heq : u z.1 ∈ c '' (D₀ ×ˢ ({0} : Set ℝ)) ↔
        u z.1 ∈ (c '' (D₀ ×ˢ ({0} : Set ℝ))) ∩ S₀ :=
      ⟨fun h => ⟨h, hs⟩, fun h => h.1⟩
    rw [heq, hzero₀]
    exact huaxis₀ _ (hJs.subset hz.1)
  have haxis₁ (z : P2 × ℝ) (hz : z ∈ J.space ×ˢ Icc (0 : ℝ) (a / 2)) :
      w z ∈ T ↔ z.1.1 = 0 := by
    rw [hwtrace T D₁ hD₁ htrace₁ z hz]
    have hs := huS (hJs.subset hz.1)
    have heq : u z.1 ∈ c '' (D₁ ×ˢ ({0} : Set ℝ)) ↔
        u z.1 ∈ (c '' (D₁ ×ˢ ({0} : Set ℝ))) ∩ S₀ :=
      ⟨fun h => ⟨h, hs⟩, fun h => h.1⟩
    rw [heq, hzero₁]
    exact huaxis₁ _ (hJs.subset hz.1)
  rw [hJs] at hw hwi hwR hwfront haxis₀ haxis₁
  have hout := he.exists_original_boundary_pair_chart_of_proper_patch hSR hTR
    hd (half_pos ha) w hw hwi hwR hwfront haxis₀ haxis₁
  rwa [hcenter] at hout

end PoincareConjecture.M76
