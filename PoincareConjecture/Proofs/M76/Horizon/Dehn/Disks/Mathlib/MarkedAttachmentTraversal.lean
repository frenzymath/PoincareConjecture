import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.PrescribedTwoIntervalCircle
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

def markedTargetMap {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {D : Set Y} {Z : Set X} {g : Y → X} (hg : ContinuousOn g D) :
    C((D ∩ g ⁻¹' Z : Set Y), Z) where
  toFun x := ⟨g x, x.property.2⟩
  continuous_toFun := (hg.comp_continuous continuous_subtype_val
    (fun x ↦ x.property.1)).subtype_mk _

def markedSourcePath
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace X]
    {S : Set E} {R D : Set Y} {Z : Set X} {f : E → X} {g : Y → X}
    (H : S ≃ₜ R) (hRD : R ⊆ D) (hkeep : ∀ x : S, g (H x) = f x)
    {a b : S} (p : Path a b) (hmark : ∀ t : I01, f (p t) ∈ Z)
    {x y : (D ∩ g ⁻¹' Z : Set Y)} (hx : (x : Y) = H a) (hy : (y : Y) = H b) :
    Path x y where
  toFun t := ⟨H (p t), hRD (H (p t)).property, by
    change g (H (p t)) ∈ Z
    rw [hkeep]
    exact hmark t⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp H.continuous).comp p.continuous).subtype_mk _
  source' := Subtype.ext (by simpa only [p.source] using hx.symm)
  target' := Subtype.ext (by simpa only [p.target] using hy.symm)

def intervalChartSubtypePath {Y : Type*} [TopologicalSpace Y] (q : I01 ≃ₜ Y) :
    Path (q i0) (q i1) where
  toFun := q
  continuous_toFun := q.continuous
  source' := rfl
  target' := rfl

theorem marked_interval_chart_homotopic
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {D : Set Y} {Z : Set X} {g : Y → X} (hg : ContinuousOn g D)
    (q : I01 ≃ₜ (D ∩ g ⁻¹' Z : Set Y)) {x y : (D ∩ g ⁻¹' Z : Set Y)}
    (hx : q i0 = x) (hy : q i1 = y) (P : Path x y) :
    (((intervalChartSubtypePath q).cast hx.symm hy.symm).map
      (markedTargetMap hg).continuous).Homotopic
        (P.map (markedTargetMap hg).continuous) :=
  (homotopic_of_interval_chart q
    ((intervalChartSubtypePath q).cast hx.symm hy.symm) P).map (markedTargetMap hg)

theorem exists_marked_attachment_traversal
    {E0 E1 X : Type*} [TopologicalSpace E0] [TopologicalSpace E1]
    [TopologicalSpace X] {S0 : Set E0} {S1 : Set E1} {Z : Set X}
    {f0 : E0 → X} {f1 : E1 → X} {g : P2 → X}
    (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (hg : ContinuousOn g T)
    (hkeep0 : ∀ x : S0, g (n0 x) = f0 x)
    (hkeep1 : ∀ x : S1, g (n1 x) = f1 x)
    {a0 b0 : S0} {a1 b1 u v : S1}
    (hseam0 : (n1 a1 : P2) = n0 a0) (hseam1 : (n0 b0 : P2) = n1 b1)
    (α : Path u a1) (β : Path a0 b0) (γ : Path b1 v)
    (hα : ∀ t : I01, f1 (α t) ∈ Z)
    (hβ : ∀ t : I01, f0 (β t) ∈ Z)
    (hγ : ∀ t : I01, f1 (γ t) ∈ Z)
    {V : Set P2}
    (hball : IsFinitePLBallPair P2 T ((T ∩ g ⁻¹' Z) ∪ V))
    (hV : IsFinitePLBallPair ℝ V {(n1 u : P2), (n1 v : P2)})
    (hends : (n1 u : P2) ≠ n1 v)
    (hcontact : V ∩ g ⁻¹' Z = {(n1 u : P2), (n1 v : P2)}) :
    let B := T ∩ g ⁻¹' Z
    let G := markedTargetMap (Z := Z) hg
    IsFinitePLBallPair ℝ B {(n1 u : P2), (n1 v : P2)} ∧
    ∃ (uB aB bB vB : B) (αB : Path uB aB) (βB : Path aB bB) (γB : Path bB vB)
      (P : Path uB vB),
      (uB : P2) = n1 u ∧ (aB : P2) = n0 a0 ∧
      (bB : P2) = n0 b0 ∧ (vB : P2) = n1 v ∧
      (∀ t : I01, (αB t : P2) = n1 (α t)) ∧
      (∀ t : I01, (βB t : P2) = n0 (β t)) ∧
      (∀ t : I01, (γB t : P2) = n1 (γ t)) ∧
      P = (αB.trans βB).trans γB ∧
      (∀ t : I01, (αB.map G.continuous t : X) = f1 (α t)) ∧
      (∀ t : I01, (βB.map G.continuous t : X) = f0 (β t)) ∧
      (∀ t : I01, (γB.map G.continuous t : X) = f1 (γ t)) ∧
      P.map G.continuous =
        ((αB.map G.continuous).trans (βB.map G.continuous)).trans
          (γB.map G.continuous) ∧
      ∀ (q : I01 ≃ₜ B) (hq0 : q i0 = uB) (hq1 : q i1 = vB),
        (((intervalChartSubtypePath q).cast hq0.symm hq1.symm).map G.continuous).Homotopic
          (((αB.map G.continuous).trans (βB.map G.continuous)).trans
            (γB.map G.continuous)) := by
  let B := T ∩ g ⁻¹' Z
  have hB : IsFinitePLBallPair ℝ B {(n1 u : P2), (n1 v : P2)} :=
    PolygonalCrossingResolution.outer_disk_old_rim_is_interval hball hV hends hcontact
  have hu : g (n1 u) ∈ Z := by
    rw [hkeep1]
    simpa only [α.source] using hα i0
  have ha : g (n0 a0) ∈ Z := by
    rw [hkeep0]
    simpa only [β.source] using hβ i0
  have hb : g (n0 b0) ∈ Z := by
    rw [hkeep0]
    simpa only [β.target] using hβ i1
  have hv : g (n1 v) ∈ Z := by
    rw [hkeep1]
    simpa only [γ.target] using hγ i1
  let uB : B := ⟨n1 u, Or.inr (n1 u).property, hu⟩
  let aB : B := ⟨n0 a0, Or.inl (n0 a0).property, ha⟩
  let bB : B := ⟨n0 b0, Or.inl (n0 b0).property, hb⟩
  let vB : B := ⟨n1 v, Or.inr (n1 v).property, hv⟩
  let αB : Path uB aB :=
    markedSourcePath n1 subset_union_right hkeep1 α hα rfl hseam0.symm
  let βB : Path aB bB :=
    markedSourcePath n0 subset_union_left hkeep0 β hβ rfl rfl
  let γB : Path bB vB :=
    markedSourcePath n1 subset_union_right hkeep1 γ hγ hseam1 rfl
  let P := (αB.trans βB).trans γB
  let G := markedTargetMap (Z := Z) hg
  have hmap : P.map G.continuous =
      ((αB.map G.continuous).trans (βB.map G.continuous)).trans
        (γB.map G.continuous) := by simp only [P, Path.map_trans]
  refine ⟨hB, uB, aB, bB, vB, αB, βB, γB, P,
    rfl, rfl, rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, rfl,
    ?_, ?_, ?_, hmap, ?_⟩
  · intro t
    exact hkeep1 (α t)
  · intro t
    exact hkeep0 (β t)
  · intro t
    exact hkeep1 (γ t)
  · intro q hq0 hq1
    rw [← hmap]
    exact marked_interval_chart_homotopic hg q hq0 hq1 P

end PoincareConjecture.M76.Dehn
